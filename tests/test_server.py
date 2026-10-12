import os
import subprocess
import sys
import tempfile
import threading
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

import lss_config
import lean_server
from lean_server import LeanServer, get_server, run_lake
from lean import LeanChecker, _hammer_code

PROJ = lss_config.project_dir("aeneas")

if not os.path.isdir(PROJ):
    print("SERVER SKIP (not built)")
    sys.exit(0)

AENEAS_OLEAN = os.path.join(
    PROJ, ".lake/packages/aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean"
)
if not os.path.exists(AENEAS_OLEAN):
    print("SERVER FAIL: Aeneas not built")
    sys.exit(1)

fails = []
s5 = None


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


try:
    print("=== server ===")
    cfg = lss_config.server_cfg()
    s = get_server(PROJ, cfg)

    # case 1: import Aeneas env loads; Aeneas.Std.Result is accessible
    r1 = s.check("import Aeneas\n#check Aeneas.Std.Result")
    check("import Aeneas rc=0", r1.rc == 0, f"rc={r1.rc} stderr={r1.stderr[:100]}")
    check("Aeneas.Std.Result accessible", r1.rc == 0, f"rc={r1.rc} stderr={r1.stderr[:100]}")

    # case 2: sorry with import Aeneas -> rc=0 + warning mentioning sorry
    r2 = s.check("import Aeneas\ntheorem _t : (1:Nat) = 1 := sorry")
    check("sorry rc=0", r2.rc == 0, f"rc={r2.rc} stderr={r2.stderr[:100]}")
    check("sorry has warning", "warning" in r2.stderr, f"stderr={r2.stderr[:100]}")
    check("sorry has sorry text", "sorry" in r2.stderr, f"stderr={r2.stderr[:100]}")

    # case 3: false theorem with import Aeneas -> rc=1
    r3 = s.check("import Aeneas\ntheorem _t : (0:Nat) = 1 := rfl")
    check("false rfl rc=1", r3.rc == 1, f"rc={r3.rc}")

    # case 4: same import Aeneas code again -> env_hits increases
    st0 = s.stats()
    s.check("import Aeneas\n#check Aeneas.Std.Result")
    st1 = s.stats()
    check("env_hits increases", st1["env_hits"] > st0["env_hits"],
          f"before={st0['env_hits']} after={st1['env_hits']}")

    # case 5: import_timeout=0.001 triggers timeout on any real import -> timed_out, restart,
    #         then the same server recovers and can still handle no-import code
    s5 = LeanServer(PROJ, {"cmd_timeout": 30, "import_timeout": 0.001, "env_cache_cap": 8})
    r5 = s5.check("import Mathlib\n#check Nat")
    check("tiny timeout timed_out", r5.timed_out, f"timed_out={r5.timed_out}")
    check("tiny timeout restart", s5.stats()["restarts"] >= 1,
          f"restarts={s5.stats()['restarts']}")
    r5b = s5.check("#check Nat")
    check("after restart no-import works", r5b.rc == 0,
          f"rc={r5b.rc} stderr={r5b.stderr[:80]}")

    # case 6: code with only import lines -> _should_use_repl=False -> via lake
    r6 = s.check("import Mathlib\n")
    check("import-only via lake", r6.via == "lake",
          f"via={r6.via} (expected lake since no non-import content)")

    # case 7: LeanChecker.typecheck with import Aeneas + sorry -> ok=True (regression for sorry bug)
    ck = LeanChecker(project_dir=PROJ)
    ok7, errs7 = ck.typecheck("import Aeneas\ntheorem _t : (1:Nat) = 1 := sorry", project_dir=PROJ)
    check("typecheck sorry ok=True", ok7, f"ok={ok7} errs={errs7[:2]}")

    # case 8: sanity_check -> True
    check("sanity_check", ck.sanity_check(PROJ), "sanity_check returned False")

    # case 9: run_lake with timeout=0.5 -> process group killed, no lean process left
    fd9, path9 = tempfile.mkstemp(suffix=".lean", dir=PROJ)
    try:
        with os.fdopen(fd9, "w", encoding="utf-8") as f:
            f.write("import Mathlib\nexample : True := trivial\n")
        _, stderr9, rc9, killed9, _ = run_lake(["lake", "env", "lean", path9], PROJ, timeout=0.5)
        check("run_lake timeout rc=1", rc9 == 1, f"rc={rc9}")
        check("run_lake timeout stderr", "timeout" in stderr9, f"stderr={stderr9[:80]}")
        check("run_lake killed", killed9, "killed=False; process group not killed")
        pname = os.path.basename(path9)
        ps_out = subprocess.run(["ps", "-eo", "cmd"], capture_output=True, text=True).stdout
        leaked = [l for l in ps_out.splitlines() if pname in l]
        check("no lean process left after kill", not leaked,
              f"leaked: {leaked[:2]}")
    finally:
        try:
            os.unlink(path9)
        except OSError:
            pass

    # case 10: lean-native hammer via warm REPL (code built through the same path as try_hammer)
    lndir = lss_config.project_dir('lean-native')
    if not os.path.isdir(lndir):
        print("SKIP: lean-native not built")
    else:
        hammer_code = _hammer_code('', '∀ (n : Nat), n + 0 = n')
        cfg = lss_config.server_cfg()
        sln = get_server(lndir, cfg)
        r10a = sln.check(hammer_code, timeout=90)
        check("lean-native hammer rc=0", r10a.rc == 0,
              f"rc={r10a.rc} stderr={r10a.stderr[:120]}")
        t_first = r10a.elapsed
        r10b = sln.check(hammer_code, timeout=90)
        check("lean-native hammer second call faster",
              r10a.rc == 0 and r10b.rc == 0 and r10b.elapsed < t_first,
              f"rc={r10a.rc}/{r10b.rc} first={t_first:.2f}s second={r10b.elapsed:.2f}s")

        # case 11: bad import in lean-native -> rc=1 with module name in stderr (not silent fallback)
        r11 = sln.check('import NoSuchModuleXyz\nexample : True := trivial')
        check("bad import rc=1", r11.rc == 1,
              f"rc={r11.rc} stderr={r11.stderr[:120]}")
        check("bad import stderr has module name", 'NoSuchModuleXyz' in r11.stderr,
              f"stderr={r11.stderr[:120]}")

    # case 12: env threading: a command run against a returned env id sees a theorem
    # defined in that env
    r12a = s.check("import Aeneas\ntheorem _env_t12 : (1:Nat) = 1 := rfl")
    check("case12 build returns new_env", r12a.rc == 0 and r12a.new_env is not None,
          f"rc={r12a.rc} new_env={r12a.new_env}")
    r12b = s.check("#check _env_t12", env=r12a.new_env)
    check("case12 sees theorem defined in the returned env", r12b.rc == 0,
          f"rc={r12b.rc} stderr={r12b.stderr[:120]}")

    # case 13: memory cap (cgroup v2 via systemd-run --scope; RLIMIT_DATA/RLIMIT_AS
    # don't work for Lean, see project notes). a cap set ~1GB above this REPL's own
    # import baseline survives import, but a ~3GB allocation trips it: the result
    # names the cap, the server restarts, the next command still works, and no lean
    # process is left. ~3GB is enough to trip a working cap, and little enough that
    # a silently non-working cap would not have cost more than that.
    def _rss_anon(pid):
        with open(f"/proc/{pid}/status", encoding="utf-8") as f:
            for line in f:
                if line.startswith("RssAnon:"):
                    return int(line.split()[1]) * 1024
        return None

    s13_probe = LeanServer(PROJ, {"memory_cap": False})
    s13_probe.check("import Aeneas\n#check Nat")
    baseline13 = (_rss_anon(s13_probe._worker._proc.pid)
                  if s13_probe._worker and s13_probe._worker._proc else None)
    s13_probe.close()

    if baseline13 is None:
        check("case13 memory cap", False, "could not read import baseline RssAnon")
    else:
        cap13 = baseline13 + 1024 ** 3
        s13 = LeanServer(PROJ, {"memory_cap_bytes": cap13})
        r13a = s13.check("import Aeneas\n#check Nat")
        check("case13 import ok under the small cap", r13a.rc == 0,
              f"rc={r13a.rc} stderr={r13a.stderr[:150]}")
        pid13_a = s13._worker._proc.pid if s13._worker and s13._worker._proc else None

        r13b = s13.check("#eval (Array.replicate 402653184 (0:Nat)).size", timeout=60)
        check("case13 big alloc flagged as memory cap hit", r13b.mem_killed,
              f"mem_killed={r13b.mem_killed} stderr={r13b.stderr[:200]}")
        check("case13 error names the cap", str(cap13) in r13b.stderr,
              f"stderr={r13b.stderr[:200]}")
        check("case13 restarted", r13b.restarted, f"restarted={r13b.restarted}")

        r13c = s13.check("#check Nat")
        check("case13 next command works", r13c.rc == 0,
              f"rc={r13c.rc} stderr={r13c.stderr[:120]}")
        pid13_c = s13._worker._proc.pid if s13._worker and s13._worker._proc else None

        s13.close()
        leaked13 = [pid for pid in {pid13_a, pid13_c} - {None} if os.path.exists(f"/proc/{pid}")]
        check("case13 no lean process left", not leaked13, f"leaked pids: {leaked13}")

    # case 14: the RssAnon watchdog survives a cold-cache lean-native import that
    # pinned the old cgroup cap (which also charged mmapped .olean page cache) at
    # its limit until it timed out (see project notes). drop the page cache, probe
    # an uncapped import's peak RssAnon, size a cap off that, drop the cache again,
    # then require the capped import to still succeed.
    HAMMER_IMPORT14 = "import Mathlib\nimport Hammer\n#check Nat"

    def _drop_olean_cache(root):
        for dirpath, _, filenames in os.walk(root):
            for fn in filenames:
                if not fn.endswith(".olean"):
                    continue
                fd = os.open(os.path.join(dirpath, fn), os.O_RDONLY)
                try:
                    os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
                finally:
                    os.close(fd)

    def _peak_rss_anon_during(server, code):
        # sums over the whole process group, like lean_server._MemWatchdog does --
        # the repl binary is a child of the lake process the worker holds, and
        # that child is where almost all of the RssAnon actually is.
        worker = server._worker
        pgid = worker._proc.pid if worker and worker._proc else None
        peak = [0]
        stop = threading.Event()

        def _poll():
            while not stop.is_set():
                if pgid is not None:
                    peak[0] = max(peak[0], lean_server._rss_anon_bytes(pgid))
                stop.wait(0.25)

        th = threading.Thread(target=_poll, daemon=True)
        th.start()
        r = server.check(code)
        stop.set()
        th.join(timeout=2)
        return r, peak[0]

    if not os.path.isdir(lndir):
        print("SKIP: case14 (lean-native not built)")
    else:
        _drop_olean_cache(os.path.join(lndir, ".lake"))
        s14_probe = LeanServer(lndir, {"memory_cap": False})
        r14_probe, peak14_probe = _peak_rss_anon_during(s14_probe, HAMMER_IMPORT14)
        check("case14 probe import ok", r14_probe.rc == 0,
              f"rc={r14_probe.rc} stderr={r14_probe.stderr[:150]}")
        s14_probe.close()

        cap14 = int(1.5 * peak14_probe)
        check("case14 cap is below the 6GB RssFile ceiling measured earlier",
              cap14 < 6 * 1024 ** 3, f"cap14={cap14}")

        _drop_olean_cache(os.path.join(lndir, ".lake"))
        s14 = LeanServer(lndir, {"memory_cap_bytes": cap14})
        r14, peak14 = _peak_rss_anon_during(s14, HAMMER_IMPORT14)
        check("case14 cold import under the RssAnon cap: rc=0", r14.rc == 0,
              f"rc={r14.rc} stderr={r14.stderr[:200]}")
        check("case14 cold import under the RssAnon cap: not mem_killed",
              not r14.mem_killed, f"mem_killed={r14.mem_killed} stderr={r14.stderr[:200]}")
        s14.close()
        print(f"  case14: cap={cap14} probe_peak_rss_anon={peak14_probe} "
              f"capped_run_peak_rss_anon={peak14}")

finally:
    if s5 is not None:
        s5.close()
    lean_server.shutdown_all()

if fails:
    print(f"\nSERVER FAIL: {fails}")
    sys.exit(1)
else:
    print("\nSERVER OK")
