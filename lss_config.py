import json
import os
import tomllib
from pathlib import Path

_CFG = None
_CFG_PATH = Path(__file__).parent / "lss.toml"


def _cfg():
    global _CFG
    if _CFG is None:
        with open(_CFG_PATH, "rb") as f:
            _CFG = tomllib.load(f)
        # a bench variant: LSS_OVERRIDES='{"proof": {"rust_hammer": true}}' sets keys per table
        for table, keys in json.loads(os.environ.get("LSS_OVERRIDES") or "{}").items():
            _CFG.setdefault(table, {}).update(keys)
    return _CFG


def config():
    """lss.toml with any LSS_OVERRIDES applied."""
    return _cfg()


def project_dir(name):
    p = _cfg()["projects"][name]
    return os.path.expanduser(os.environ.get(p["env_var"], p["dir"]))


def default_project():
    for name, p in _cfg()["projects"].items():
        if p.get("default"):
            return name
    return next(iter(_cfg()["projects"]))


def default_project_dir():
    return project_dir(default_project())


def hammer_project_dir():
    for p in _cfg()["projects"].values():
        if p.get("has_hammer"):
            return os.path.expanduser(os.environ.get(p["env_var"], p["dir"]))
    return None


def all_projects():
    return {name: project_dir(name) for name in _cfg()["projects"]}


def server_cfg():
    defaults = {
        "workers": 1,
        "cmd_timeout": 30,
        "import_timeout": 180,
        "lake_timeout": 120,
        "env_cache_cap": 8,
        "max_restarts": 20,
        "hammer_timeout": 90,
        "memory_cap": True,
        "memory_fraction": 0.4,
    }
    s = _cfg().get("server", {})
    return {k: s.get(k, v) for k, v in defaults.items()}


def proof_cfg():
    defaults = {"aeneas_layer": True, "aeneas_heartbeats": 200000,
                "premise_selector": "local", "rust_hammer": False,
                "hammer_heartbeats": 1000000, "split_seconds": 180, "mutant_hammer_seconds": 120}
    p = _cfg().get("proof", {})
    return {k: p.get(k, v) for k, v in defaults.items()}
