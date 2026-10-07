"""derive lean/lean-native/lake-manifest.json from lean/aeneas/lake-manifest.json.
drops the aeneas package entry and sets top-level name to «lss-lean-native»."""
import json
import os

repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = os.path.join(repo, "lean", "aeneas", "lake-manifest.json")
dst = os.path.join(repo, "lean", "lean-native", "lake-manifest.json")

with open(src) as f:
    manifest = json.load(f)

pkgs = [p for p in manifest["packages"] if p["name"] != "aeneas"]
for p in pkgs:
    if p["name"] == "mathlib":
        p["inherited"] = False
manifest["packages"] = pkgs
manifest["name"] = "«lss-lean-native»"

with open(dst, "w", encoding="utf-8") as f:
    json.dump(manifest, f, indent=2, ensure_ascii=False)
    f.write("\n")

names = [p["name"] for p in manifest["packages"]]
print(f"wrote {dst}")
print(f"packages ({len(names)}): {', '.join(names)}")
