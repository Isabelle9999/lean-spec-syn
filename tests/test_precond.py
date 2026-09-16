import os, sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import callgraph, modularity
from lean import LeanChecker

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ)

# safeDiv has a real precondition; callers differ in whether they establish it
src = """def safeDiv (a b : Nat) : Nat := a / b

def goodCaller (n : Nat) : Nat := safeDiv n 2

def badCaller (n m : Nat) : Nat := safeDiv n m
"""
g = callgraph.build_call_graph(src)

div_spec = ["∀ (a b : Nat), 0 < b → safeDiv a b * b ≤ a"]

for caller, spec in [
    ("goodCaller", ["∀ (n : Nat), goodCaller n * 2 ≤ n"]),
    ("badCaller",  ["∀ (n m : Nat), badCaller n m * m ≤ n"]),
]:
    spec_map = {"safeDiv": div_spec, caller: spec}
    r = modularity.check_function_modularity(
        caller, src, spec, g, spec_map, ck, project_dir=PROJ)
    print(f"\n=== {caller} ===")
    print({k: v for k, v in r.items()
           if k in ("status", "precond", "preconditions", "edges", "classification")})
    print("full:", r)

print("\nEXPECTED: goodCaller discharges 0 < 2. badCaller cannot — m may be 0 —")
print("so it should report PRECONDITION_UNDISCHARGED, not CALLEE_UNDERSPECIFIED.")