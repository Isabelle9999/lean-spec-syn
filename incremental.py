import hashlib
import json
import os

_HASHES_FILE = ".lss/hashes.json"
_CACHE_DIR = ".lss/cache"


def lean_version():
    try:
        import lss_config
        tc = open(os.path.join(lss_config.default_project_dir(), "lean-toolchain")).read().strip()
        return tc
    except Exception:
        return "unknown"


def code_version(settings="", repo=None):
    """what made a run's specs: the synthesizer's own commit and the run's settings
    (lss.toml with any overrides, the Lean project), or None when the synthesizer's
    files differ from its commit (a run then has no fingerprint to compare, and
    every function runs again)."""
    import subprocess
    repo = repo or os.path.dirname(os.path.abspath(__file__))
    try:
        sha = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=repo).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], capture_output=True,
                               text=True, cwd=repo).stdout.strip()
    except OSError:
        return None
    return f"{sha}:{_hash(settings)}" if sha and not dirty else None


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
    """a function's own text: its Lean code, and for a Rust unit (whose Lean code only
    imports its crate) its name and its crate's code."""
    return _hash("\0".join([bm.get("lean_code", ""), bm.get("lean_name", ""), bm.get("func_source") or ""]))


def compute_current_hashes(benches, lean_ver, code=None):
    """a function's fingerprint: its own text, under this Lean version, this
    synthesizer commit and these settings (specs made otherwise are never carried
    forward)."""
    return {
        "lean_version": lean_ver,
        "code": code,
        "benches": {bm["name"]: bench_hash(bm) for bm in benches},
    }


def affected_benches(prev, curr):
    if prev is None:
        return set(curr["benches"])
    if prev.get("lean_version") != curr.get("lean_version"):
        return set(curr["benches"])
    if curr.get("code") is None or prev.get("code") != curr.get("code"):
        return set(curr["benches"])
    prev_b = prev.get("benches", {})
    changed = {name for name, h in curr["benches"].items() if prev_b.get(name) != h}
    changed |= {name for name in prev_b if name not in curr["benches"]}
    return changed


def kept_hashes(curr, finished):
    """the fingerprints to save after a run: only those of functions that finished
    (a result, or carried forward), so one that crashed, timed out or could not
    start runs again next time."""
    return {**curr, "benches": {n: h for n, h in curr["benches"].items() if n in finished}}


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
