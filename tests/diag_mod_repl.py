import os, sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import lean, callgraph, modularity
from lean import LeanChecker, run_in_project, _run_in_project_lake

sys.path.insert(0, "..")
import lss_config
PROJ = lss_config.project_dir("aeneas")
ck = LeanChecker(project_dir=PROJ)

src = "def dbl (n : Nat) : Nat := n + n\n\ndef quad (n : Nat) : Nat := dbl (dbl n)\n"
g = callgraph.build_call_graph(src)
spec_map = {"dbl": ["∀ (n : Nat), dbl n = n + n"],
            "quad": ["∀ (n : Nat), quad n = 4 * n"]}

# what layer 1 does with the abstraction statement, both paths
stmt = ("∀ (_ag0 : (n : Nat) → Nat), (∀ (n : Nat), _ag0 n = n + n) → "
        "(∀ (n : Nat), quad_mabs _ag0 n = 4 * n)")
env = "def quad_mabs (f : Nat → Nat) (n : Nat) : Nat := f (f n)\n"

print("=== try_proof on the abstraction statement ===")
r = ck.try_proof(env, stmt, project_dir=PROJ)
print("proved:", r.proved, "method:", r.method, "err:", (r.error or "")[:150])

print("\n=== same code, both invocation paths ===")
code = "import Mathlib\n" + env + f"theorem _t : {stmt} := by grind [quad_mabs]\n"
ro, re, rc = run_in_project(code, project_dir=PROJ)
so, se, sc = _run_in_project_lake(code, PROJ)
print("REPL       rc:", rc, ((ro or "")+(re or "")).strip()[:200])
print("subprocess rc:", sc, ((so or "")+(se or "")).strip()[:200])

print("\n=== full modularity check ===")
res = modularity.check_function_modularity(
    "quad", src, spec_map["quad"], g, spec_map, ck, project_dir=PROJ)
print({k: v for k, v in res.items() if k in ("status", "localization", "edge_classifications")})