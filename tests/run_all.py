import subprocess
import sys
import os
import time
sys.stdout.reconfigure(encoding="utf-8")
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

TESTS = [
    ("events",            "tests/test_events.py",      "all ok"),
    ("pins",              "tests/test_pins.py",        "PINS OK"),
    ("lean server",       "tests/test_server.py",      "SERVER OK"),
    ("soundness guard",   "tests/audit.py",           "ALL PASS"),
    ("mutation inline",   "tests/harness_planted.py", None),
    ("mutation imported", "tests/diag_survived2.py",  "STRONG_OK"),
    ("operators",         "tests/test_operators.py",  "stillborn=0"),
    ("modularity",        "tests/test_modular.py",    "'status': 'proved'"),
    ("localisation",      "tests/test_localize.py",   "['dec']"),
    ("adversarial",       "tests/test_adv3.py",       "'attacked': True"),
    ("adv no-inputs",     "tests/test_adv4.py",       "attacked: True"),
    ("func correctness",  "tests/test_funccorrect2.py","'matched': 2"),
]

fails = []
for name, path, expect in TESTS:
    t0 = time.time()
    r = subprocess.run([sys.executable, path], capture_output=True, text=True,
                       encoding="utf-8", timeout=1800)
    out = (r.stdout or "") + (r.stderr or "")
    ok = r.returncode == 0 and (expect is None or expect in out)
    print(f"{'PASS' if ok else 'FAIL'}  {name:20} {time.time()-t0:6.1f}s")
    if not ok:
        fails.append(name)
        print("   ", out.strip()[-300:].replace("\n", "\n    "))

print(f"\n{len(TESTS)-len(fails)}/{len(TESTS)} passed" +
      (f" — FAILED: {fails}" if fails else ""))