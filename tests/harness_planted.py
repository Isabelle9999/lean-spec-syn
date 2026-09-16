import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
from lean import LeanChecker, MutationEngine
from synth import LLMClient

PROJ = os.path.expanduser("~/lean_v2")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
ck = LeanChecker(project_dir=PROJ); llm = LLMClient()
eng = MutationEngine(ck)

code = """def clampTo (lo hi v : Nat) : Nat :=
  if v < lo then lo
  else if v > hi then hi
  else v
"""

# deliberately WEAK: true, but blind to clamping
weak = "∀ (lo hi v : Nat), clampTo lo hi v ≥ 0"
# STRONG: pins the behaviour
strong = "∀ (lo hi v : Nat), v < lo → clampTo lo hi v = lo"

muts = eng.generate_mutants(code, "clampTo", llm=llm)
print(f"generated: {len(muts)}")

live = eng.filter_compilable(muts, original_code=code, func_name="clampTo", llm=llm)
print(f"compilable: {len(live)}\n")

for label, spec in [("WEAK", weak), ("STRONG", strong)]:
    survived = 0
    for i, m in enumerate(live):
        accepts = eng.spec_accepts_mutant(spec, m, func_name="clampTo")
        if accepts:
            survived += 1
    print(f"{label}: {survived}/{len(live)} mutants survived")

print("\nEXPECTED: WEAK survives many, STRONG survives few.")
print("If both are the same, the loop is broken.")