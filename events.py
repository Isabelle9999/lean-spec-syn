import json
import time
import hashlib
from contextvars import ContextVar

_ctx: ContextVar[dict] = ContextVar("lss_ctx", default={})
_state: dict = {}
_stats: dict = {}


def configure(run_id, config):
    cfg_json = json.dumps(config, sort_keys=True, separators=(",", ":"))
    config_hash = hashlib.sha256(cfg_json.encode()).hexdigest()[:12]
    import os
    os.makedirs(".lss/runs", exist_ok=True)
    fh = open(f".lss/runs/run_{run_id}.events.jsonl", "a", encoding="utf-8", buffering=1)
    _state.update({"run_id": run_id, "config_hash": config_hash, "fh": fh})
    _stats.update({"llm_calls": 0, "input_tokens": 0, "output_tokens": 0,
                   "cached_tokens": 0, "usd": 0.0, "lean_calls": 0, "lean_s": 0.0})


class _CtxMgr:
    def __init__(self, fields):
        self._fields = fields
        self._token = None

    def __enter__(self):
        self._token = _ctx.set({**_ctx.get(), **self._fields})
        return self

    def __exit__(self, *_):
        _ctx.reset(self._token)


def context(**fields):
    return _CtxMgr(fields)


def with_context(**fields):
    def decorator(fn):
        def wrapper(*args, **kwargs):
            with context(**fields):
                return fn(*args, **kwargs)
        return wrapper
    return decorator


def emit(kind, **fields):
    if not _state:
        return
    row = {
        "ts": time.time(),
        "run_id": _state["run_id"],
        "config_hash": _state["config_hash"],
        "kind": kind,
        **_ctx.get(),
        **fields,
    }
    _state["fh"].write(json.dumps(row) + "\n")
    if kind == "llm":
        _stats["llm_calls"] += 1
        _stats["input_tokens"] += fields.get("input_tokens", 0)
        _stats["output_tokens"] += fields.get("output_tokens", 0)
        _stats["cached_tokens"] += fields.get("cache_read_input_tokens", 0)
        _stats["usd"] += fields.get("usd", 0.0)
    elif kind == "lean":
        _stats["lean_calls"] += 1
        _stats["lean_s"] += fields.get("elapsed", 0.0)


def get_stats():
    return dict(_stats)
