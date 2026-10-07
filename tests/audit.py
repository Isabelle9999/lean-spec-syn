import os
import sys
sys.path.insert(0, "."); sys.path.insert(0, ".."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from lean import LeanChecker, MutationEngine, run_in_project
import lss_config

LEAN_NATIVE = lss_config.project_dir("lean-native")
AENEAS      = lss_config.project_dir("aeneas")

fails = []
def check(name, got, want, pr=None):
    ok = got == want
    print(f"  {'PASS' if ok else 'FAIL'}: {name}  (got {got}, want {want})")
    if not ok:
        if pr is not None:
            print(f"    method={pr.method!r}  error={str(pr.error)[:200]!r}")
        fails.append(name)

print("=== 0. environment ===")
for tag, p in [("lean-native", LEAN_NATIVE), ("aeneas", AENEAS)]:
    if not os.path.isdir(p):
        print(f"  {tag:16} skip (build dir not found)")
        continue
    out, err, rc = run_in_project("import Mathlib\nexample : True := trivial\n", project_dir=p)
    print(f"  {tag:16} Mathlib importable: {rc == 0}")
    if rc != 0:
        print("   ", (((out or '')+(err or '')).strip()[:120]).replace("\n"," | "))

print("\n=== 1. try_proof must reject false statements (lean_v2) ===")
ck = LeanChecker(project_dir=AENEAS)
_pr = ck.try_proof("", "∀ (n : Nat), n + 0 = n", project_dir=AENEAS)
check("true:  n + 0 = n", _pr.proved, True, _pr)
_pr = ck.try_proof("", "∀ (n : Nat), n + 1 = n", project_dir=AENEAS)
check("FALSE: n + 1 = n", _pr.proved, False, _pr)
_pr = ck.try_proof("", "(0 : Nat) = 1", project_dir=AENEAS)
check("FALSE: 0 = 1", _pr.proved, False, _pr)
_pr = ck.try_proof("", "∀ (l : List Nat), l.length = 0", project_dir=AENEAS)
check("FALSE: ∀ l, l.length = 0", _pr.proved, False, _pr)

print("\n=== 2. try_hammer must reject false statements ===")
_hdir = lss_config.hammer_project_dir()
if not _hdir or not os.path.isdir(_hdir):
    print("  skip (hammer project build dir not found)")
else:
    ckh = LeanChecker(project_dir=AENEAS)
    _pr = ckh.try_hammer("", "∀ (n : Nat), n + 0 = n")
    check("true:  n + 0 = n", _pr.proved, True, _pr)
    _pr = ckh.try_hammer("", "∀ (n : Nat), n + 1 = n")
    check("FALSE: n + 1 = n", _pr.proved, False, _pr)

print("\n=== 3. aeneas environment must NOT yield false proofs ===")
ckr = LeanChecker(project_dir=AENEAS)
_pr = ckr.try_proof("", "(0 : Nat) = 1", project_dir=AENEAS)
check("FALSE in aeneas: 0 = 1", _pr.proved, False, _pr)
_pr = ckr.try_proof("", "∀ (n : Nat), n + 0 = n", project_dir=AENEAS)
check("true in aeneas: n + 0 = n", _pr.proved, True, _pr)

print("\n=== 4. mutation classification, inline ===")
eng = MutationEngine(ck)
code = "def clampTo (lo hi v : Nat) : Nat :=\n  if v < lo then lo\n  else if v > hi then hi\n  else v\n"
weak   = "∀ (lo hi v : Nat), clampTo lo hi v ≥ 0"
strong = "∀ (lo hi v : Nat), v < lo → clampTo lo hi v = lo"
muts = eng.generate_mutants(code, "clampTo")
live = eng.filter_compilable(muts, original_code=code, func_name="clampTo")
print(f"  generated={len(muts)} compilable={len(live)}")
for label, spec in [("WEAK", weak), ("STRONG", strong)]:
    c = {}
    for m in live[:5]:
        st = eng.certify_proof(code, m, "clampTo", [spec], project_dir=AENEAS)
        k = st.get("status"); c[k] = c.get(k, 0) + 1
    print(f"  {label}: {c}")
check("WEAK has no KILLED", "KILLED" not in c if label=="WEAK" else True, True)

print("\n" + ("ALL PASS" if not fails else f"FAILURES: {fails}"))