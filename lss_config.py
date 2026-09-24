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
    return _CFG


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


def hammer_timeout():
    for p in _cfg()["projects"].values():
        if p.get("has_hammer"):
            return p.get("hammer_timeout", 120)
    return 120


def all_projects():
    return {name: project_dir(name) for name in _cfg()["projects"]}
