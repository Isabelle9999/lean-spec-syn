import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import callgraph
import modularity
from lean import LeanChecker

sys.path.insert(0, "..")
import lss_config
PROJ = lss_config.project_dir("aeneas")
ck = LeanChecker(project_dir=PROJ)

src = """def dec (n : Nat) : Nat := n - 1

def good (n : Nat) : Nat := dec (n + 1)

def bad (n : Nat) : Nat := dec n
"""
g = callgraph.build_call_graph(src)
dec_spec = ["∀ (n : Nat), 0 < n → dec n + 1 = n"]

cases = [
    # precondition 0 < n+1 always holds -> should prove
    ("good", ["∀ (n : Nat), good n + 1 = n + 1"]),
    # precondition 0 < n fails at n = 0, and the abstracted callee says
    # nothing there -> should NOT prove
    ("bad",  ["∀ (n : Nat), bad n ≤ n"]),
]

for caller, spec in cases:
    r = modularity.check_function_modularity(
        caller, src, spec, g, {"dec": dec_spec, caller: spec}, ck, project_dir=PROJ)
    print(f"\n=== {caller} ===  status={r['status']}")
    for k in ("precond", "preconditions", "edges", "classification",
              "precondition_status", "localisation", "localization"):
        if k in r:
            print(f"   {k}: {r[k]}")
    print("   stmt:", r.get("check_stmt", "")[:150])

print("\nEXPECTED: good -> proved.  bad -> undetermined, with the failure")
print("attributed to an undischarged precondition rather than a weak callee spec.")