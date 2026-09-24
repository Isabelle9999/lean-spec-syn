import os
import sys
sys.path.insert(0, "."); sys.stdout.reconfigure(encoding="utf-8")
from lean import run_in_project

sys.path.insert(0, "..")
import lss_config
PROJ = lss_config.project_dir("aeneas")
env = "def quad_mabs (f : Nat → Nat) (n : Nat) : Nat := f (f n)\n"
stmt = ("∀ (g : (n : Nat) → Nat), (∀ (n : Nat), g n = n + n) → "
        "(∀ (n : Nat), quad_mabs g n = 4 * n)")

for name, tac in [
    ("simp_all",        "simp_all [quad_mabs]"),
    ("intro+simp[h]",   "intro g h n\n  simp [quad_mabs, h]\n  omega"),
    ("intro+simp+ring", "intro g h n\n  simp [quad_mabs, h]\n  ring"),
    ("intro+rw",        "intro g h n\n  unfold quad_mabs\n  rw [h, h]\n  omega"),
    ("grind",           "grind [quad_mabs]"),
]:
    code = f"import Mathlib\n{env}theorem _t : {stmt} := by\n  {tac}\n"
    out, err, rc = run_in_project(code, project_dir=PROJ)
    print(f"{name:18} rc={rc}")
    if rc != 0:
        print("   ", (((out or "")+(err or "")).strip()[:180]).replace("\n", " | "))