import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from synth import run_adversarial_tier, LLMClient
from lean import LeanChecker, ExampleStore

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ); llm = LLMClient(); store = ExampleStore()

code = """def clampTo (lo hi v : Nat) : Nat :=
  if v < lo then lo
  else if v > hi then hi
  else v
"""
weak = [{"name": "s1", "stmt": "∀ (lo hi v : Nat), clampTo lo hi v ≥ 0", "status": "proved"}]
strong = [
    {"name": "t1", "stmt": "∀ (lo hi v : Nat), v < lo → clampTo lo hi v = lo", "status": "proved"},
    {"name": "t2", "stmt": "∀ (lo hi v : Nat), v > hi → clampTo lo hi v = hi", "status": "proved"},
    {"name": "t3", "stmt": "∀ (lo hi v : Nat), lo ≤ v → v ≤ hi → clampTo lo hi v = v", "status": "proved"},
]

for label, specs in [("WEAK  (attack MUST be found)", weak),
                     ("STRONG (attack should NOT be found)", strong)]:
    r = run_adversarial_tier(specs, code, "clampTo", ck, llm, store,
                             project_dir=PROJ, rounds=3, verbose=True)
    print(f"\n===== {label} =====")
    print(r)