"""derive lean/lean-native/lake-manifest.json from lean/aeneas/lake-manifest.json."""
import copy
import json
import os
import sys


def derive(aeneas_manifest):
    """build lean-native manifest from aeneas manifest."""
    m = copy.deepcopy(aeneas_manifest)
    pkgs = [p for p in m["packages"] if p["name"] != "aeneas"]
    for p in pkgs:
        if p["name"] == "mathlib":
            p["inherited"] = False
    m["packages"] = pkgs
    m["name"] = "«lss-lean-native»"
    return m


if __name__ == "__main__":
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    src = os.path.join(repo, "lean", "aeneas", "lake-manifest.json")
    dst = os.path.join(repo, "lean", "lean-native", "lake-manifest.json")

    with open(src) as f:
        aeneas = json.load(f)
    result = derive(aeneas)

    if "--check" in sys.argv:
        with open(dst) as f:
            actual = json.load(f)
        if result != actual:
            print("lean/lean-native/lake-manifest.json is out of date; run scripts/derive_manifest.py")
            sys.exit(1)
        print("manifest ok")
    else:
        with open(dst, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2, ensure_ascii=False)
            f.write("\n")
        names = [p["name"] for p in result["packages"]]
        print(f"wrote {dst}")
        print(f"packages ({len(names)}): {', '.join(names)}")
