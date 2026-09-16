import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from lean import LeanChecker, MutationEngine
from synth import LLMClient

PROJ = os.path.expanduser("~/rust_benchmarks")
ck = LeanChecker(project_dir=PROJ); llm = LLMClient()
eng = MutationEngine(ck)

lean_code = ("import Aeneas\nimport FeatureSuite.Code.Funs\n"
             "import FeatureSuite.Code.Types\n"
             "open Aeneas Aeneas.Std Result ControlFlow Error\nopen FeatureSuite\n")
func = "records.swap"
strong = "∀ (p : records.Pair), records.swap p = ok { first := p.second, second := p.first }"
weak   = "∀ (p : records.Pair), ∃ r, records.swap p = ok r"
structs = {"Pair": [("first", "Std.U32"), ("second", "Std.U32")]}

muts = eng.generate_mutants(lean_code, func, llm=llm, project_dir=PROJ)
live = eng.filter_compilable(muts, original_code=lean_code, func_name=func, llm=llm)

print("live entry type:", type(live[0]).__name__)
if isinstance(live[0], dict):
    print("keys:", list(live[0].keys()))
    print("mutant_func_name:", live[0].get("mutant_func_name"))
print()

for label, spec in [("WEAK", weak), ("STRONG", strong)]:
    counts = {}
    for m in live:                      # pass the DICT, not m["code"]
        st = eng.certify_proof(lean_code, m, func, [spec],
                               project_dir=PROJ, struct_defs=structs)
        k = st.get("status")
        counts[k] = counts.get(k, 0) + 1
        if label == "STRONG":
            print("  ", st)
    print(f"{label}: {counts}")