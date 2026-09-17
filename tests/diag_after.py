import os, sys, time
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
import lean
from lean import LeanChecker, run_in_project, _run_in_project_lake
from synth import LLMClient

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ)

print("=== A: is try_proof fixed? ===")
env = "def quad_mabs (f : Nat → Nat) (n : Nat) : Nat := f (f n)\n"
stmt = ("∀ (_ag0 : (n : Nat) → Nat), (∀ (n : Nat), _ag0 n = n + n) → "
        "(∀ (n : Nat), quad_mabs _ag0 n = 4 * n)")
r = ck.try_proof(env, stmt, project_dir=PROJ)
print("proved:", r.proved, "| method:", r.method)
print("err:", (r.error or "")[:250])

print("\n=== B: how many calls take the REPL path? ===")
n0 = lean._lean_call_count
t0 = time.time()
for i in range(5):
    ck.try_proof("", f"∀ (n : Nat), n + {i} = {i} + n", project_dir=PROJ)
print(f"5 try_proof calls: {time.time()-t0:.1f}s, "
      f"{lean._lean_call_count - n0} lean calls")
print("  (REPL path would be well under 1s total)")

print("\n=== C: what does the adversarial LLM return? ===")
llm = LLMClient()
code = ("def clampTo (lo hi v : Nat) : Nat :=\n  if v < lo then lo\n"
        "  else if v > hi then hi\n  else v\n")
specs = [{"name": "s1", "stmt": "∀ (lo hi v : Nat), clampTo lo hi v ≥ 0",
          "status": "proved"}]
resp = llm.generate_adversarial(specs, "def clampTo (lo hi v : Nat) : Nat",
                                lean_code=code)
print("response:", repr(resp)[:300])
print("is empty:", not resp)