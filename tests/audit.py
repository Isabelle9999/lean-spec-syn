import os, sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from lean import LeanChecker, MutationEngine, run_in_project

LEAN_V2 = os.path.expanduser("~/lean_v2")
RUST    = os.path.expanduser("~/rust_benchmarks")

fails = []
def check(name, got, want):
    ok = got == want
    print(f"  {'PASS' if ok else 'FAIL'}: {name}  (got {got}, want {want})")
    if not ok: fails.append(name)

print("=== 0. environment ===")
for tag, p in [("lean_v2", LEAN_V2), ("rust_benchmarks", RUST)]:
    out, err, rc = run_in_project("import Mathlib\nexample : True := trivial\n", project_dir=p)
    print(f"  {tag:16} Mathlib importable: {rc == 0}")
    if rc != 0:
        print("   ", (((out or '')+(err or '')).strip()[:120]).replace("\n"," | "))

print("\n=== 1. try_proof must reject false statements (lean_v2) ===")
ck = LeanChecker(project_dir=LEAN_V2)
check("true:  n + 0 = n",        ck.try_proof("", "∀ (n : Nat), n + 0 = n", project_dir=LEAN_V2).proved, True)
check("FALSE: n + 1 = n",        ck.try_proof("", "∀ (n : Nat), n + 1 = n", project_dir=LEAN_V2).proved, False)
check("FALSE: 0 = 1",            ck.try_proof("", "(0 : Nat) = 1", project_dir=LEAN_V2).proved, False)
check("FALSE: ∀ l, l.length = 0", ck.try_proof("", "∀ (l : List Nat), l.length = 0", project_dir=LEAN_V2).proved, False)

print("\n=== 2. try_hammer must reject false statements ===")
check("true:  n + 0 = n",  ck.try_hammer("", "∀ (n : Nat), n + 0 = n", project_dir=LEAN_V2).proved, True)
check("FALSE: n + 1 = n",  ck.try_hammer("", "∀ (n : Nat), n + 1 = n", project_dir=LEAN_V2).proved, False)

print("\n=== 3. broken environment must NOT yield proofs ===")
ckr = LeanChecker(project_dir=RUST)
check("FALSE in rust proj: 0 = 1",
      ckr.try_proof("", "(0 : Nat) = 1", project_dir=RUST).proved, False)
check("true in rust proj: n + 0 = n",
      ckr.try_proof("", "∀ (n : Nat), n + 0 = n", project_dir=RUST).proved, True)

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
        st = eng.certify_proof(code, m, "clampTo", [spec], project_dir=LEAN_V2)
        k = st.get("status"); c[k] = c.get(k, 0) + 1
    print(f"  {label}: {c}")
check("WEAK has no KILLED", "KILLED" not in c if label=="WEAK" else True, True)

print("\n" + ("ALL PASS" if not fails else f"FAILURES: {fails}"))