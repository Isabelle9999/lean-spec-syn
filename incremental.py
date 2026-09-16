import hashlib
import json
import os
import subprocess

_HASHES_FILE = ".lss/hashes.json"
_CACHE_DIR = ".lss/cache"


def lean_version():
    from lean import LEAN
    try:
        r = subprocess.run([LEAN, "--version"], capture_output=True, text=True, timeout=10)
        return (r.stdout + r.stderr).strip()
    except Exception:
        return "unknown"


def _hash(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def load_hashes(path=_HASHES_FILE):
    if os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None
    return None


def save_hashes(data, path=_HASHES_FILE):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)


def bench_hash(bm):
    return _hash(bm.get("lean_code", ""))


def compute_current_hashes(benches, lean_ver):
    return {
        "lean_version": lean_ver,
        "benches": {bm["name"]: bench_hash(bm) for bm in benches},
    }


def affected_benches(prev, curr):
    if prev is None:
        return set(curr["benches"])
    if prev.get("lean_version") != curr.get("lean_version"):
        return set(curr["benches"])
    prev_b = prev.get("benches", {})
    changed = {name for name, h in curr["benches"].items() if prev_b.get(name) != h}
    changed |= {name for name in prev_b if name not in curr["benches"]}
    return changed


def load_cached_specs(bm_name, cache_dir=_CACHE_DIR):
    path = os.path.join(cache_dir, f"{bm_name}.json")
    if os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None
    return None


def save_cached_specs(bm_name, specs, cache_dir=_CACHE_DIR):
    os.makedirs(cache_dir, exist_ok=True)
    with open(os.path.join(cache_dir, f"{bm_name}.json"), "w", encoding="utf-8") as f:
        json.dump(specs, f, indent=2)
