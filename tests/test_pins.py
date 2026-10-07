import json
import os
import re
import subprocess
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")
import lss_config

repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
static = "--static" in sys.argv
fails = []

print(f"mode {'static' if static else 'full'}")


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


# import derive from scripts/
sys.path.insert(0, os.path.join(repo, "scripts"))
from derive_manifest import derive  # noqa: E402

projects = lss_config._cfg()["projects"]

print("=== static checks ===")

# (a) lean-toolchain version matches lean_version in lss.toml
for name, proj in projects.items():
    tc_file = os.path.join(repo, "lean", name, "lean-toolchain")
    if not os.path.exists(tc_file):
        continue
    tc_ver = open(tc_file).read().strip().split(":")[-1]
    lss_ver = proj.get("lean_version", "")
    check(f"{name} toolchain matches lean_version",
          tc_ver == lss_ver, f"toolchain={tc_ver!r} lss.toml={lss_ver!r}")

# (b) lean-native manifest equals derive(aeneas manifest)
aeneas_mf = os.path.join(repo, "lean", "aeneas", "lake-manifest.json")
native_mf = os.path.join(repo, "lean", "lean-native", "lake-manifest.json")
if os.path.exists(aeneas_mf) and os.path.exists(native_mf):
    with open(aeneas_mf) as f:
        aeneas_manifest = json.load(f)
    with open(native_mf) as f:
        actual_manifest = json.load(f)
    check("lean-native manifest matches derive(aeneas)",
          derive(aeneas_manifest) == actual_manifest,
          "run scripts/derive_manifest.py to regenerate")
else:
    check("lean-native/aeneas manifest files present",
          False, "manifest file missing from repo")

# (c) every [[require]] in each lakefile has a matching manifest entry


def _is_commit(rev):
    return bool(re.fullmatch(r"[0-9a-f]{40}", rev or ""))


for name in projects:
    lf_path = os.path.join(repo, "lean", name, "lakefile.toml")
    mf_path = os.path.join(repo, "lean", name, "lake-manifest.json")
    if not os.path.exists(lf_path) or not os.path.exists(mf_path):
        continue
    with open(lf_path, "rb") as f:
        lf = tomllib.load(f)
    with open(mf_path) as f:
        mf = json.load(f)
    mf_pkgs = {p["name"].strip("«»"): p for p in mf.get("packages", [])}
    for req in lf.get("require", []):
        rname = req["name"].strip("«»")
        rrev = req.get("rev") or ""
        entry = mf_pkgs.get(rname)
        if entry is None:
            check(f"{name} [{rname}] in manifest", False, "not found")
            continue
        if _is_commit(rrev):
            ok = entry.get("rev") == rrev
            got = entry.get("rev", "")
        else:
            ok = entry.get("inputRev") == rrev
            got = entry.get("inputRev", "")
        check(f"{name} [{rname}] rev pinned", ok,
              f"lakefile={rrev!r} manifest={got!r}")

# (d) no .py in the repo contains Windows elan paths
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
check("no .elan/toolchains or lean.exe in .py files",
      not bad, ", ".join(bad) if bad else "")

if not static:
    print("\n=== full checks ===")
    for name, build_dir in lss_config.all_projects().items():
        if not os.path.isdir(build_dir):
            print(f"  FAIL: {name} (build dir not found: {build_dir})")
            fails.append(f"{name} build dir missing")
            continue

        pin_dir = os.path.join(repo, "lean", name)

        # drift: pin files byte-identical to build dir
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

        # olean checks
        mathlib_olean = os.path.join(
            build_dir,
            ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean",
        )
        check(f"{name} Mathlib.olean exists",
              os.path.exists(mathlib_olean), "Mathlib not built")

        cfg_projects = lss_config._cfg().get("projects", {})
        if cfg_projects.get(name, {}).get("has_hammer"):
            hammer_olean = os.path.join(
                build_dir,
                ".lake/packages/Hammer/.lake/build/lib/lean/Hammer.olean",
            )
            check(f"{name} Hammer.olean exists",
                  os.path.exists(hammer_olean), "Hammer not built")

        if name == "aeneas":
            olean = os.path.join(
                build_dir,
                ".lake/packages/aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean",
            )
            check(f"{name} Aeneas.olean exists", os.path.exists(olean), "Aeneas not built")

        # toolchain: lake env lean --version reports expected version
        tc_file = os.path.join(pin_dir, "lean-toolchain")
        if os.path.exists(tc_file):
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

if not fails:
    print("\npins ok")
else:
    print(f"\nfailed: {fails}")
    sys.exit(1)
