import os
import subprocess
import sys
import tempfile
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")

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
        _, stderr9, rc9, killed9 = run_lake(["lake", "env", "lean", path9], PROJ, timeout=0.5)
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
        check("lean-native hammer second call faster", r10b.elapsed < t_first,
              f"first={t_first:.2f}s second={r10b.elapsed:.2f}s")

        # case 11: bad import in lean-native -> rc=1 with module name in stderr (not silent fallback)
        r11 = sln.check('import NoSuchModuleXyz\nexample : True := trivial')
        check("bad import rc=1", r11.rc == 1,
              f"rc={r11.rc} stderr={r11.stderr[:120]}")
        check("bad import stderr has module name", 'NoSuchModuleXyz' in r11.stderr,
              f"stderr={r11.stderr[:120]}")

finally:
    if s5 is not None:
        s5.close()
    lean_server.shutdown_all()

if fails:
    print(f"\nSERVER FAIL: {fails}")
    sys.exit(1)
else:
    print("\nSERVER OK")
