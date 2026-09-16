import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import callgraph
import modularity
from lean import LeanChecker

PROJ = os.path.expanduser("~/lean_v2")
ck = LeanChecker(project_dir=PROJ)

src = """def dbl (n : Nat) : Nat := n + n

def quad (n : Nat) : Nat := dbl (dbl n)
"""

g = callgraph.build_call_graph(src)
print("callees of quad:", g.callees("quad") if hasattr(g, "callees") else "(check API)")
print("methods:", [m for m in dir(g) if not m.startswith("_")])

quad_spec = ["∀ (n : Nat), quad n = 4 * n"]

# STRONG callee spec — quad should prove from it with dbl abstracted
strong = {"dbl": ["∀ (n : Nat), dbl n = n + n"], "quad": quad_spec}
# WEAK callee spec — quad should NOT prove; localisation should name dbl
weak   = {"dbl": ["∀ (n : Nat), dbl n ≥ 0"],      "quad": quad_spec}

for label, spec_map in [("STRONG callee spec", strong), ("WEAK callee spec", weak)]:
    r = modularity.check_function_modularity(
        "quad", src, quad_spec, g, spec_map, ck, project_dir=PROJ)
    print(f"\n=== {label} ===")
    print(r)

print("\nEXPECTED: STRONG -> quad's spec proves with dbl abstracted (contract-discharged).")
print("          WEAK   -> fails, and localisation names dbl as underspecified.")