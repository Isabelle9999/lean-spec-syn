import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from synth import run_adversarial_tier, LLMClient
from lean import LeanChecker, ExampleStore

sys.path.insert(0, "..")
import lss_config
PROJ = lss_config.project_dir("aeneas")
ck = LeanChecker(project_dir=PROJ); llm = LLMClient(); store = ExampleStore()

code = """def clampTo (lo hi v : Nat) : Nat :=
  if v < lo then lo
  else if v > hi then hi
  else v
"""
weak = [{"name": "s1", "stmt": "∀ (lo hi v : Nat), clampTo lo hi v ≥ 0", "status": "proved"}]

for tag, ti in [("no inputs", None),
                ("with inputs", ["0 5 3", "2 4 9", "1 3 0", "5 5 5"])]:
    r = run_adversarial_tier(weak, code, "clampTo", ck, llm, store,
                             project_dir=PROJ, test_inputs=ti, rounds=2, verbose=True)
    print(f"\n===== WEAK, {tag} =====")
    print("attacked:", r["attacked"], "witness:", r.get("witness"))