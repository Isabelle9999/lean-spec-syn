import os, sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())
from loader import load_rust_project
from lean import LeanChecker, MutationEngine, run_in_project
from synth import LLMClient

RUST = os.path.expanduser("~/rust_benchmarks")
bs = load_rust_project(RUST)
bm = [b for b in bs if "swap" in b["name"]][0]
lc = bm["lean_code"] + bm.get("lean_preamble", "")
fn = bm.get("func_name")
print("func_name:", fn, " func_source present:", bool(bm.get("func_source")))

ck = LeanChecker(project_dir=RUST); eng = MutationEngine(ck); llm = LLMClient()

# (a) mutation as the run path calls it vs as the test calls it
m1 = eng.generate_mutants(lc, fn, llm=llm)
m2 = eng.generate_mutants(lc, fn, llm=llm, project_dir=RUST,
                          func_source=bm.get("func_source"))
print(f"\n(a) no project_dir: {len(m1) if isinstance(m1,list) else m1}")
print(f"    with project_dir: {len(m2) if isinstance(m2,list) else m2}")

# (c) why does rfl fail on a definitionally-true spec
stmt = ("∀ (a b : Std.U32), records.swap { first := a, second := b } = "
        "ok { first := b, second := a }")
for tac in ["rfl", "simp [records.swap]", "intro a b; rfl", "decide", "tauto"]:
    code = lc + f"\ntheorem _t : {stmt} := by {tac}\n"
    out, err, rc = run_in_project(code, project_dir=RUST)
    print(f"(c) {tac:22} rc={rc}", "" if rc==0 else
          (((out or "")+(err or "")).strip()[:110]).replace("\n"," | "))