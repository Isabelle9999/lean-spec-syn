import subprocess
import tempfile
import os
import signal as _signal
import json
import time
import threading as _threading
import queue as _queue_mod
import atexit as _atexit
from collections import OrderedDict
from dataclasses import dataclass
import events


@dataclass
class CheckResult:
    stdout: str
    stderr: str
    rc: int
    via: str  # "repl" or "lake"
    elapsed: float = 0.0
    timed_out: bool = False
    restarted: bool = False
    new_env: int | None = None  # repl env id after this command, if via="repl" and it ran
    mem_killed: bool = False  # process was killed by this server's own memory watchdog


def _mem_total_bytes():
    with open("/proc/meminfo", encoding="utf-8") as f:
        for line in f:
            if line.startswith("MemTotal:"):
                return int(line.split()[1]) * 1024
    raise RuntimeError("lean_server: no MemTotal line in /proc/meminfo")


def _mem_cap_bytes(fraction):
    return int(_mem_total_bytes() * fraction)


def _resolve_mem_cap(cfg):
    """byte cap for lean/lake subprocesses, or None if the cap is off.
    RLIMIT_DATA and RLIMIT_AS both count reserved/mapped address space rather than
    memory actually charged to the process, and Lean's runtime reserves enough of
    that per thread (scaling with core count) that no cap under the two counted
    the whole machine even lets Lean start. a cgroup v2 cap (memory.max) counts real
    use, but that includes page cache the process faults in -- including mmapped
    .olean files -- so a cold cache pins a loaded project's own cap during import.
    a watchdog that sums RssAnon (private, non-file-backed memory) across the
    process group avoids both problems, so this only computes the byte cap; see
    _MemWatchdog for the enforcement."""
    if not cfg.get("memory_cap", True):
        return None
    cap = cfg.get("memory_cap_bytes")
    if cap is None:
        cap = _mem_cap_bytes(cfg.get("memory_fraction", 0.4))
    return cap


def _rss_anon_bytes(pgid):
    """sum RssAnon, in bytes, over every live process whose process group is pgid."""
    total = 0
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat") as f:
                stat = f.read()
            fields = stat[stat.rindex(")") + 2:].split()
            if int(fields[2]) != pgid:
                continue
            with open(f"/proc/{entry}/status") as f:
                for line in f:
                    if line.startswith("RssAnon:"):
                        total += int(line.split()[1]) * 1024
                        break
        except (OSError, ValueError, IndexError):
            continue
    return total


class _MemWatchdog:
    """every 0.25s, sums RssAnon across proc's process group (pgid); once that
    exceeds cap_bytes, SIGKILLs the group and records the hit. the thread ends
    when proc ends, by itself or by this kill."""

    def __init__(self, proc, pgid, cap_bytes):
        self.hit = False
        self.rss_at_hit = 0
        self._proc = proc
        self._pgid = pgid
        self._cap = cap_bytes
        _threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        while self._proc.poll() is None:
            rss = _rss_anon_bytes(self._pgid)
            if rss > self._cap:
                self.hit = True
                self.rss_at_hit = rss
                try:
                    os.killpg(self._pgid, _signal.SIGKILL)
                except OSError:
                    pass
                return
            time.sleep(0.25)


def _extract_imports(code):
    imports, cmd = [], []
    for l in code.splitlines():
        if l.strip().startswith('import '):
            imports.append(l.strip())
            cmd.append('')
        else:
            cmd.append(l)
    return '\n'.join(imports), '\n'.join(cmd)


def _should_use_repl(code):
    for line in code.splitlines():
        s = line.strip()
        if s and not s.startswith('--') and not s.startswith('import '):
            return True
    return False


def _fmt(resp):
    msgs = resp.get("messages", [])
    lines = []
    for m in msgs:
        sev = m.get("severity", "")
        p = m.get("pos", {})
        ln = p.get('line', 0)
        col = p.get('column', 0)
        data = m.get('data', '')
        if sev == "error":
            lines.append(f":{ln}:{col}: error: {data}")
        elif sev == "warning":
            lines.append(f":{ln}:{col}: warning: {data}")
    for s in resp.get("sorries", []):
        p = s.get("pos", {})
        ln = p.get('line', 0)
        col = p.get('column', 0)
        lines.append(f":{ln}:{col}: warning: declaration uses 'sorry'")
    has_error = any(": error:" in l for l in lines)
    return '', '\n'.join(lines), 1 if has_error else 0


def run_lake(args, cwd, timeout, mem_cap_bytes=None):
    """Popen with start_new_session=True; SIGKILL process group on timeout.
    Returns (stdout, stderr, rc, killed, mem_killed). On timeout rc=1 and stderr
    starts ':0:0: error: timeout'. mem_killed=True when a _MemWatchdog killed the
    process group for exceeding mem_cap_bytes of RssAnon -- a SIGABRT (e.g. a Lean
    stack overflow) is left as an ordinary crash."""
    p = subprocess.Popen(
        args,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", cwd=cwd,
        start_new_session=True,
    )
    watch = _MemWatchdog(p, p.pid, mem_cap_bytes) if mem_cap_bytes is not None else None
    killed = False
    try:
        stdout, stderr = p.communicate(timeout=timeout)
        if watch is not None and watch.hit:
            stderr = (stderr or "") + (
                f"\n:0:0: error: lean memory cap exceeded (the watchdog killed the process, "
                f"cap={mem_cap_bytes} bytes)")
            return stdout, stderr, 1, killed, True
        return stdout, stderr, p.returncode, killed, False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), _signal.SIGKILL)
            killed = True
        except OSError:
            pass
        p.wait()
        return "", f":0:0: error: timeout after {timeout}s", 1, killed, False


def _run_lake(code, project_dir, timeout=120, mem_cap_bytes=None):
    fd, path = tempfile.mkstemp(suffix=".lean", dir=project_dir)
    t0 = time.time()
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(code)
        stdout, stderr, rc, _, mem_killed = run_lake(["lake", "env", "lean", path], project_dir,
                                                      timeout, mem_cap_bytes=mem_cap_bytes)
        timed_out = rc == 1 and stderr.startswith(":0:0: error: timeout")
        merged_stderr = '\n'.join(x for x in (stderr, stdout) if x)
        return CheckResult(stdout=stdout, stderr=merged_stderr, rc=rc,
                           via="lake", elapsed=time.time() - t0, timed_out=timed_out,
                           mem_killed=mem_killed)
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def _run_in_project_lake(code, project_dir):
    """compatibility shim returning (stdout, stderr, rc)."""
    r = _run_lake(code, project_dir)
    return r.stdout, r.stderr, r.rc


class ReplWorker:
    def __init__(self, project_dir, cmd_timeout=30, import_timeout=180, env_cache_cap=8,
                 mem_cap_bytes=None):
        self._dir = project_dir
        self._cmd_timeout = cmd_timeout
        self._import_timeout = import_timeout
        self._cap = env_cache_cap
        self._mem_cap = mem_cap_bytes
        self._proc = None
        self._mem_watch = None
        self._envs = OrderedDict()
        self.restarts = 0
        self._env_hits = 0
        self._env_misses = 0

    def _launch(self):
        self._proc = subprocess.Popen(
            ["lake", "exe", "repl"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="utf-8", cwd=self._dir,
            start_new_session=True,
        )
        self._mem_watch = (_MemWatchdog(self._proc, self._proc.pid, self._mem_cap)
                            if self._mem_cap is not None else None)

    def _send_raw(self, cmd_dict, timeout):
        proc = self._proc
        assert proc is not None and proc.stdin is not None and proc.stdout is not None
        try:
            proc.stdin.write(json.dumps(cmd_dict) + "\n\n")
            proc.stdin.flush()
        except (OSError, BrokenPipeError):
            return None
        q = _queue_mod.Queue()
        proc_stdout = proc.stdout
        def _r():
            buf = []
            try:
                for line in proc_stdout:
                    if not line.strip():
                        break
                    buf.append(line)
                q.put(''.join(buf))
            except Exception:
                q.put(None)
        _threading.Thread(target=_r, daemon=True).start()
        try:
            raw = q.get(timeout=timeout)
        except _queue_mod.Empty:
            return None
        if not raw:
            return None
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return None

    def _base_env_for(self, import_block):
        if import_block in self._envs:
            self._envs.move_to_end(import_block)
            self._env_hits += 1
            return self._envs[import_block]
        self._env_misses += 1
        cmd_text = import_block if import_block else "-- base"
        resp = self._send_raw({"cmd": cmd_text}, timeout=self._import_timeout)
        if resp is None:
            return None
        top_msg = resp.get("message", "")
        if top_msg:
            err = f":0:0: error: {top_msg}"
            self._envs[import_block] = err
            return err
        err_msgs = [m for m in resp.get("messages", []) if m.get("severity") == "error"]
        if "env" not in resp or err_msgs:
            if err_msgs:
                m0 = err_msgs[0]
                p0 = m0.get("pos", {})
                err = f":{p0.get('line',0)}:{p0.get('column',0)}: error: {m0.get('data','')}"
                self._envs[import_block] = err
            else:
                self._envs[import_block] = -1
            return self._envs[import_block]
        env_id = resp["env"]
        # probe: verify env is functional (unbuilt modules return {"env": 0} with no messages)
        probe = self._send_raw({"cmd": "example : (1 : Nat) = 1 := rfl", "env": env_id},
                               timeout=self._cmd_timeout)
        if probe is None or any(m.get("severity") == "error" for m in probe.get("messages", [])):
            self._envs[import_block] = -1
            return -1
        if len(self._envs) >= self._cap:
            self._envs.popitem(last=False)
        self._envs[import_block] = env_id
        return env_id

    def start(self):
        try:
            self._launch()
        except (FileNotFoundError, OSError):
            return False
        resp = self._send_raw({"cmd": "-- ok"}, timeout=30)
        if resp is None or "env" not in resp:
            self.close()
            return False
        self._envs[""] = resp["env"]
        return True

    def run(self, code, cmd_timeout=None, env=None):
        """return CheckResult or None if import unavailable (caller falls back to lake).
        env: run code as a command against this existing env id instead of an
        import-derived base env (code is the whole command, no import extraction)."""
        if self._proc is None:
            return None
        _ct = cmd_timeout if cmd_timeout is not None else self._cmd_timeout
        t0 = time.time()
        if env is not None:
            env_id, cmd = env, code
        else:
            import_block, cmd = _extract_imports(code)
            env_id = self._base_env_for(import_block)
            if env_id is None:
                return self._dead_result(t0)
            if isinstance(env_id, str):
                return CheckResult(stdout="", stderr=env_id, rc=1, via="repl",
                                   elapsed=time.time() - t0)
            if env_id == -1:
                return None
        resp = self._send_raw({"cmd": cmd, "env": env_id}, timeout=_ct)
        if resp is None:
            return self._dead_result(t0)
        elapsed = time.time() - t0
        stdout, stderr, rc = _fmt(resp)
        return CheckResult(stdout=stdout, stderr=stderr, rc=rc, via="repl", elapsed=elapsed,
                           new_env=resp.get("env"))

    def _dead_result(self, t0):
        """the process stopped responding: a hit recorded by this worker's
        _MemWatchdog is reported as a memory-cap hit; anything else -- including a
        SIGABRT (-6) from a Lean stack overflow -- is left as the existing generic
        repl-timeout path. either way the worker restarts."""
        watch = self._mem_watch
        mem_killed = watch is not None and watch.hit
        restarted = self._restart()
        if mem_killed:
            err = (f":0:0: error: lean memory cap exceeded (the watchdog killed the process, "
                   f"cap={self._mem_cap} bytes)")
            return CheckResult(stdout="", stderr=err, rc=1, via="repl",
                               elapsed=time.time() - t0, timed_out=False,
                               restarted=restarted, mem_killed=True)
        return CheckResult(stdout="", stderr=":0:0: error: lean repl timeout",
                           rc=1, via="repl", elapsed=time.time() - t0,
                           timed_out=True, restarted=restarted)

    def _restart(self):
        self.close()
        self.restarts += 1
        print(f"  [repl] restart #{self.restarts}")
        try:
            self._launch()
            resp = self._send_raw({"cmd": "-- ok"}, timeout=30)
            if resp is None or "env" not in resp:
                self.close()
                return True
            self._envs[""] = resp["env"]
        except Exception:
            self._proc = None
        return True

    def close(self):
        p, self._proc = self._proc, None
        self._envs.clear()
        if p is None:
            return
        try:
            if p.stdin is not None:
                p.stdin.close()
        except: pass
        try:
            pgid = os.getpgid(p.pid)
            os.killpg(pgid, _signal.SIGTERM)
            try:
                p.wait(timeout=3)
            except subprocess.TimeoutExpired:
                try: os.killpg(pgid, _signal.SIGKILL)
                except OSError: pass
        except OSError:
            pass


class LeanServer:
    def __init__(self, project_dir, cfg=None):
        cfg = cfg or {}
        workers = cfg.get("workers", 1)
        if workers != 1:
            raise ValueError(f"workers must be 1, got {workers}")
        self._dir = project_dir
        self._lake_timeout = cfg.get("lake_timeout", 120)
        self._mem_cap = _resolve_mem_cap(cfg)
        self._worker = ReplWorker(
            project_dir,
            cmd_timeout=cfg.get("cmd_timeout", 30),
            import_timeout=cfg.get("import_timeout", 180),
            env_cache_cap=cfg.get("env_cache_cap", 8),
            mem_cap_bytes=self._mem_cap,
        )
        if not self._worker.start():
            self._worker = None
        self._calls = 0
        self._repl_calls = 0
        self._lake_calls = 0
        self._timeouts = 0
        self._lake_timeouts = 0
        self._lake_killed = 0
        self._mem_killed_count = 0
        self._seconds_repl = 0.0
        self._seconds_lake = 0.0

    def check(self, code, timeout=None, env=None):
        """env: run code as a command against this existing repl env id (no
        import extraction, no lake fallback) and report the resulting env id
        on the returned CheckResult as new_env."""
        self._calls += 1
        if env is not None:
            if self._worker is None:
                return CheckResult(stdout="", stderr=":0:0: error: lean repl unavailable",
                                   rc=1, via="repl")
            r = self._worker.run(code, cmd_timeout=timeout, env=env)
            if r is None:
                return CheckResult(stdout="", stderr=":0:0: error: lean repl unavailable",
                                   rc=1, via="repl")
            self._repl_calls += 1
            self._seconds_repl += r.elapsed
            if r.timed_out:
                self._timeouts += 1
            if r.mem_killed:
                self._mem_killed_count += 1
            n_err = r.stderr.count(": error:") if r.stderr else 0
            sorry = "sorry" in (r.stderr or "") or "sorry" in (r.stdout or "")
            events.emit("lean", via=r.via, rc=r.rc, elapsed=r.elapsed,
                        timed_out=r.timed_out, restarted=r.restarted,
                        n_errors=n_err, sorry=sorry, mem_killed=r.mem_killed)
            return r
        if _should_use_repl(code) and self._worker is not None:
            r = self._worker.run(code, cmd_timeout=timeout)
            if r is not None:
                self._repl_calls += 1
                self._seconds_repl += r.elapsed
                if r.timed_out:
                    self._timeouts += 1
                if r.mem_killed:
                    self._mem_killed_count += 1
                n_err = r.stderr.count(": error:") if r.stderr else 0
                sorry = "sorry" in (r.stderr or "") or "sorry" in (r.stdout or "")
                events.emit("lean", via=r.via, rc=r.rc, elapsed=r.elapsed,
                            timed_out=r.timed_out, restarted=r.restarted,
                            n_errors=n_err, sorry=sorry, mem_killed=r.mem_killed)
                return r
        r = _run_lake(code, self._dir, timeout=timeout if timeout is not None else self._lake_timeout,
                      mem_cap_bytes=self._mem_cap)
        self._lake_calls += 1
        self._seconds_lake += r.elapsed
        if r.timed_out:
            self._timeouts += 1
            self._lake_timeouts += 1
            self._lake_killed += 1
        if r.mem_killed:
            self._mem_killed_count += 1
        n_err = r.stderr.count(": error:") if r.stderr else 0
        sorry = "sorry" in (r.stderr or "") or "sorry" in (r.stdout or "")
        events.emit("lean", via=r.via, rc=r.rc, elapsed=r.elapsed,
                    timed_out=r.timed_out, restarted=r.restarted,
                    n_errors=n_err, sorry=sorry, mem_killed=r.mem_killed)
        return r

    def stats(self):
        w = self._worker
        return {
            "calls": self._calls,
            "repl_calls": self._repl_calls,
            "lake_calls": self._lake_calls,
            "env_hits": w._env_hits if w else 0,
            "env_misses": w._env_misses if w else 0,
            "timeouts": self._timeouts,
            "lake_timeouts": self._lake_timeouts,
            "lake_killed": self._lake_killed,
            "mem_killed": self._mem_killed_count,
            "mem_cap_bytes": self._mem_cap,
            "restarts": w.restarts if w else 0,
            "seconds_repl": round(self._seconds_repl, 1),
            "seconds_lake": round(self._seconds_lake, 1),
        }

    def close(self):
        if self._worker:
            self._worker.close()
            self._worker = None


_servers = {}


def get_server(project_dir, cfg=None):
    if project_dir not in _servers:
        _servers[project_dir] = LeanServer(project_dir, cfg or _get_cfg())
    return _servers[project_dir]


def _get_cfg():
    try:
        import lss_config
        return lss_config.server_cfg()
    except Exception:
        return {}


def _get_repl(project_dir):
    """compatibility shim for diag tools."""
    if project_dir not in _servers:
        get_server(project_dir)
    return _servers[project_dir]._worker


def shutdown_all():
    for s in list(_servers.values()):
        s.close()
    _servers.clear()


def all_stats():
    return {pd: s.stats() for pd, s in _servers.items()}


_atexit.register(shutdown_all)
