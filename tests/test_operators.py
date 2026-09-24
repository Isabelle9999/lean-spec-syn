import os
import sys
import collections
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from lean import LeanChecker, MutationEngine
from synth import LLMClient

sys.path.insert(0, "..")
import lss_config
LEAN_V2 = lss_config.project_dir("aeneas")
RUST    = lss_config.project_dir("aeneas")
llm = LLMClient()

cases = [
    ("clampTo (inline, relational)", LEAN_V2,
     "def clampTo (lo hi v : Nat) : Nat :=\n  if v < lo then lo\n  else if v > hi then hi\n  else v\n",
     "clampTo", None),
    ("records.swap (imported, record)", RUST,
     ("import Aeneas\nimport FeatureSuite.Code.Funs\nimport FeatureSuite.Code.Types\n"
      "open Aeneas Aeneas.Std Result ControlFlow Error\nopen FeatureSuite\n"),
     "records.swap", RUST),
]

for name, proj, code, fn, pdir in cases:
    ck = LeanChecker(project_dir=proj)
    eng = MutationEngine(ck)
    muts = eng.generate_mutants(code, fn, llm=llm, project_dir=pdir)
    live = eng.filter_compilable(muts, original_code=code, func_name=fn, llm=llm)
    ops = collections.Counter(
        (m.get("operator", "?") if isinstance(m, dict) else "?") for m in muts)
    print(f"\n=== {name} ===")
    print(f"generated={len(muts)}  compilable={len(live)}  stillborn={len(muts)-len(live)}")
    for op, n in ops.most_common():
        print(f"   {n:3}  {op}")