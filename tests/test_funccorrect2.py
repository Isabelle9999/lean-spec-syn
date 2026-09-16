import os
import sys
import inspect
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import metrics
from lean import LeanChecker

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ)
print("signature:", inspect.signature(metrics.functional_correctness), "\n")

env = """def rev2 (l : List Nat) : List Nat := l.reverse
"""

# ground truth about rev2 — NOT independently provable without unfolding rev2
gt = ["∀ (l : List Nat), (rev2 l).length = l.length"]

specs = [
    {"name": "m1", "status": "proved",
     "stmt": "∀ (l : List Nat), l.length = (rev2 l).length"},          # should MATCH
    {"name": "m2", "status": "proved",
     "stmt": "∀ (l : List Nat), (rev2 l).length = l.length ∧ (rev2 l).length ≥ 0"},  # should MATCH
    {"name": "n1", "status": "proved",
     "stmt": "∀ (n : Nat), n + 0 = n"},                                # should NOT
    {"name": "n2", "status": "proved",
     "stmt": "∀ (l : List Nat), l.length ≥ 0"},                        # should NOT
]

def call(specs, gt):
    try:
        return metrics.functional_correctness(specs, gt, ck, lean_code=env, project_dir=PROJ)
    except TypeError:
        return metrics.functional_correctness(specs, gt, ck)

r = call(specs, gt)
print("=== A: gt mentions rev2 ===")
print({k: v for k, v in r.items() if k != "matches"})
for m in r.get("matches", []):
    print("  ", m)
print("EXPECT: m1, m2 matched; n1, n2 not.\n")

# B: ground truth that is independently provable — should be NOT MATCHABLE
gt_triv = ["∀ (l : List Nat), (l.reverse).length = l.length"]
r2 = call(specs, gt_triv)
print("=== B: gt is a Mathlib theorem ===")
print({k: v for k, v in r2.items() if k != "matches"})
for m in r2.get("matches", []):
    print("  ", m)
print("EXPECT: flagged not-matchable; no spec matches it.")