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


@dataclass
class CheckResult:
    stdout: str
    stderr: str
    rc: int
    via: str  # "repl" or "lake"
    elapsed: float = 0.0
    timed_out: bool = False
    restarted: bool = False


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


def run_lake(args, cwd, timeout):
    """Popen with start_new_session=True; SIGKILL process group on timeout.
    Returns (stdout, stderr, rc, killed). On timeout rc=1 and stderr starts ':0:0: error: timeout'."""
    p = subprocess.Popen(
        args,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", cwd=cwd,
        start_new_session=True,
    )
    killed = False
    try:
        stdout, stderr = p.communicate(timeout=timeout)
        return stdout, stderr, p.returncode, killed
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), _signal.SIGKILL)
            killed = True
        except OSError:
            pass
        p.wait()
        return "", f":0:0: error: timeout after {timeout}s", 1, killed


def _run_lake(code, project_dir, timeout=120):
    fd, path = tempfile.mkstemp(suffix=".lean", dir=project_dir)
    t0 = time.time()
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(code)
        stdout, stderr, rc, _ = run_lake(["lake", "env", "lean", path], project_dir, timeout)
        timed_out = rc == 1 and stderr.startswith(":0:0: error: timeout")
        merged_stderr = '\n'.join(x for x in (stderr, stdout) if x)
        return CheckResult(stdout=stdout, stderr=merged_stderr, rc=rc,
                           via="lake", elapsed=time.time() - t0, timed_out=timed_out)
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
    def __init__(self, project_dir, cmd_timeout=30, import_timeout=180, env_cache_cap=8):
        self._dir = project_dir
        self._cmd_timeout = cmd_timeout
        self._import_timeout = import_timeout
        self._cap = env_cache_cap
        self._proc = None
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

    def _send_raw(self, cmd_dict, timeout):
        try:
            self._proc.stdin.write(json.dumps(cmd_dict) + "\n\n")
            self._proc.stdin.flush()
        except (OSError, BrokenPipeError):
            return None
        q = _queue_mod.Queue()
        proc_stdout = self._proc.stdout
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

    def run(self, code, cmd_timeout=None):
        """return CheckResult or None if import unavailable (caller falls back to lake)."""
        if self._proc is None:
            return None
        _ct = cmd_timeout if cmd_timeout is not None else self._cmd_timeout
        import_block, cmd = _extract_imports(code)
        t0 = time.time()
        env_id = self._base_env_for(import_block)
        if env_id is None:
            restarted = self._restart()
            return CheckResult(stdout="", stderr=":0:0: error: lean repl timeout",
                               rc=1, via="repl", elapsed=time.time() - t0,
                               timed_out=True, restarted=restarted)
        if isinstance(env_id, str):
            return CheckResult(stdout="", stderr=env_id, rc=1, via="repl",
                               elapsed=time.time() - t0)
        if env_id == -1:
            return None
        resp = self._send_raw({"cmd": cmd, "env": env_id}, timeout=_ct)
        elapsed = time.time() - t0
        if resp is None:
            restarted = self._restart()
            return CheckResult(stdout="", stderr=":0:0: error: lean repl timeout",
                               rc=1, via="repl", elapsed=elapsed,
                               timed_out=True, restarted=restarted)
        stdout, stderr, rc = _fmt(resp)
        return CheckResult(stdout=stdout, stderr=stderr, rc=rc, via="repl", elapsed=elapsed)

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
        try: p.stdin.close()
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
        self._worker = ReplWorker(
            project_dir,
            cmd_timeout=cfg.get("cmd_timeout", 30),
            import_timeout=cfg.get("import_timeout", 180),
            env_cache_cap=cfg.get("env_cache_cap", 8),
        )
        if not self._worker.start():
            self._worker = None
        self._calls = 0
        self._repl_calls = 0
        self._lake_calls = 0
        self._timeouts = 0
        self._lake_timeouts = 0
        self._lake_killed = 0
        self._seconds_repl = 0.0
        self._seconds_lake = 0.0

    def check(self, code, timeout=None):
        self._calls += 1
        if _should_use_repl(code) and self._worker is not None:
            r = self._worker.run(code, cmd_timeout=timeout)
            if r is not None:
                self._repl_calls += 1
                self._seconds_repl += r.elapsed
                if r.timed_out:
                    self._timeouts += 1
                return r
        r = _run_lake(code, self._dir, timeout=timeout if timeout is not None else self._lake_timeout)
        self._lake_calls += 1
        self._seconds_lake += r.elapsed
        if r.timed_out:
            self._timeouts += 1
            self._lake_timeouts += 1
            self._lake_killed += 1
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
