import os, sys, inspect
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import callgraph, modularity
from lean import LeanChecker

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ)

src = """def dec (n : Nat) : Nat := n - 1

def bad (n : Nat) : Nat := dec n
"""
g = callgraph.build_call_graph(src)
dec_spec = ["∀ (n : Nat), 0 < n → dec n + 1 = n"]
bad_spec = ["∀ (n : Nat), bad n ≤ n"]

r = modularity.check_function_modularity(
    "bad", src, bad_spec, g, {"dec": dec_spec, "bad": bad_spec}, ck, project_dir=PROJ)
print("check:", r["status"])

loc = modularity.localize_failure(
    "bad", src, r["callees"], r["abs_names"], r["callee_types"],
    [dec_spec], bad_spec, g, ck, project_dir=PROJ)
print("\nlocalize:", loc)

print("\n--- does check_function_modularity call localize_failure? ---")
print("localize_failure" in inspect.getsource(modularity.check_function_modularity))
