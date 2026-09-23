import os, sys, time
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
import lean
from lean import run_in_project, _run_in_project_lake, _should_use_repl, _get_repl

sys.path.insert(0, "..")
import lss_config
L = lss_config.project_dir("aeneas")

cases = [
    ("plain",      "import Mathlib\ntheorem t : 1 = 1 := rfl\n"),
    ("with def",   "import Mathlib\ndef dbl (n : Nat) : Nat := n + n\n"
                   "theorem t : ∀ n, dbl n = n + n := by intro n; simp [dbl]\n"),
    ("abstracted", "import Mathlib\ndef quad_mabs (f : Nat → Nat) (n : Nat) : Nat := f (f n)\n"
                   "theorem t : ∀ (g : Nat → Nat), (∀ n, g n = n + n) → "
                   "(∀ n, quad_mabs g n = 4 * n) := by grind [quad_mabs]\n"),
    ("false",      "import Mathlib\ntheorem t : (0:Nat) = 1 := by simp\n"),
]

print("repl available:", bool(_get_repl(L)), "\n")
for name, code in cases:
    print(f"=== {name}   should_use_repl={_should_use_repl(code)}")
    t0 = time.time(); ro, re, rc = run_in_project(code, project_dir=L); tr = time.time()-t0
    t0 = time.time(); so, se, sc = _run_in_project_lake(code, L);      ts = time.time()-t0
    print(f"  REPL       rc={rc} {tr:5.1f}s  {((ro or '')+(re or '')).strip()[:120]}")
    print(f"  subprocess rc={sc} {ts:5.1f}s  {((so or '')+(se or '')).strip()[:120]}")
    print(f"  AGREE: {rc == sc}\n")