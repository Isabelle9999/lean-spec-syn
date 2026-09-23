import os
import sys
import time
sys.path.insert(0, ".")
sys.stdout.reconfigure(encoding="utf-8")

os.environ.setdefault("ANTHROPIC_API_KEY",
    open("/mnt/c/Users/User/projects/anthropic_api.txt").read().strip())

from lean import LeanChecker

sys.path.insert(0, "..")
import lss_config
PROJ = lss_config.project_dir("aeneas")
ck = LeanChecker(project_dir=PROJ)

env = "structure Pair where\n  first : Nat\n  second : Nat\ndef swp (p : Pair) : Pair := ⟨p.second, p.first⟩\n"

cases = [
    ("L1 rfl",        env, "∀ (p : Pair), swp p = ⟨p.second, p.first⟩"),
    ("L1 decide",     "",  "∀ (n : Nat), n < 3 → n ≤ 2"),
    ("L2 hammer",     "",  "∀ (l : List Nat), (l ++ []).length = l.length"),
    ("neither",       "",  "∀ (l : List Nat) (f : Nat → Nat), (l.map f).length = l.length"),
]

for name, e, stmt in cases:
    t0 = time.time()
    r = ck.try_proof(e, stmt, project_dir=PROJ)
    t1 = time.time() - t0
    print(f"{name:12} L1: proved={r.proved:<5} method={r.method}  {t1:.1f}s")
    if not r.proved:
        t0 = time.time()
        r2 = ck.try_hammer(e, stmt, project_dir=PROJ)
        t2 = time.time() - t0
        print(f"{'':12} L2: proved={r2.proved:<5} method={r2.method}  {t2:.1f}s")
    print()