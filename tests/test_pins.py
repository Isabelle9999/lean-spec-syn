import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")
import lss_config

repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fails = []


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


print("=== pins ===")
for name, build_dir in lss_config.all_projects().items():
    if not os.path.isdir(build_dir):
        print(f"  FAIL: {name} (build dir not found: {build_dir})")
        fails.append(f"{name} build dir missing")
        continue

    pin_dir = os.path.join(repo, "lean", name)

    # (1) drift: pin files byte-identical to build dir
    for fname in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
        pin_file = os.path.join(pin_dir, fname)
        build_file = os.path.join(build_dir, fname)
        if not os.path.exists(pin_file):
            continue
        if not os.path.exists(build_file):
            check(f"{name}/{fname} present in build", False, "missing in build dir")
            continue
        with open(pin_file, "rb") as f:
            pin_bytes = f.read()
        with open(build_file, "rb") as f:
            build_bytes = f.read()
        check(f"{name}/{fname} no drift", pin_bytes == build_bytes)

    # (2a) Mathlib.olean must exist for every project
    mathlib_olean = os.path.join(
        build_dir,
        ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean",
    )
    check(f"{name} Mathlib.olean exists", os.path.exists(mathlib_olean), "Mathlib not built")

    # (2b) Hammer.olean must exist when has_hammer
    cfg_projects = lss_config._cfg().get("projects", {})
    if cfg_projects.get(name, {}).get("has_hammer"):
        hammer_olean = os.path.join(
            build_dir,
            ".lake/packages/Hammer/.lake/build/lib/lean/Hammer.olean",
        )
        check(f"{name} Hammer.olean exists", os.path.exists(hammer_olean), "Hammer not built")

    # (2c) aeneas: Aeneas.olean must exist (lake build Aeneas was run)
    if name == "aeneas":
        olean = os.path.join(
            build_dir,
            ".lake/packages/aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean",
        )
        check(f"{name} Aeneas.olean exists", os.path.exists(olean), "Aeneas not built")

    # (3) toolchain: lake env lean --version reports expected version
    tc_file = os.path.join(pin_dir, "lean-toolchain")
    if os.path.exists(tc_file):
        # strip "v" prefix: lean --version says "4.31.0", toolchain says "v4.31.0"
        expected = open(tc_file).read().strip().split(":")[-1].lstrip("v")
        try:
            r = subprocess.run(
                ["lake", "env", "lean", "--version"],
                capture_output=True, text=True, timeout=30, cwd=build_dir,
            )
            out = (r.stdout + r.stderr).strip()
            check(f"{name} toolchain {expected}", expected in out, out[:80])
        except Exception as e:
            check(f"{name} toolchain {expected}", False, str(e))

# (3) hygiene: no .py in the repo contains Windows elan paths
bad = []
skip_dirs = {"__pycache__", ".lake", ".lss", ".git", ".claude"}
_self = os.path.relpath(__file__, repo)
for root, dirs, files in os.walk(repo):
    dirs[:] = [d for d in dirs if d not in skip_dirs]
    for fname in files:
        if not fname.endswith(".py"):
            continue
        path = os.path.join(root, fname)
        rel = os.path.relpath(path, repo)
        if rel == _self:
            continue
        try:
            text = open(path, encoding="utf-8").read()
        except Exception:
            continue
        if ".elan/toolchains" in text or "lean.exe" in text:
            bad.append(rel)
check("no .elan/toolchains or lean.exe in .py files", not bad,
      ", ".join(bad) if bad else "")

if not fails:
    print("\nPINS OK")
else:
    print(f"\nFAILED: {fails}")
    sys.exit(1)
