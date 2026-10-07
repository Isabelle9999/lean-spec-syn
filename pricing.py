import tomllib
from pathlib import Path

_prices = None


def _load():
    global _prices
    if _prices is None:
        p = Path(__file__).parent / "prices.toml"
        with open(p, "rb") as f:
            _prices = tomllib.load(f)
    return _prices


def cost_usd(model, usage, batch=False):
    cfg = _load()
    models = cfg.get("models", {})
    if model not in models:
        raise ValueError(f"unknown model: {model!r}")
    m = models[model]
    inp = usage.get("input_tokens", 0)
    out = usage.get("output_tokens", 0)
    cr = usage.get("cache_read_input_tokens", 0)
    cw = usage.get("cache_creation_input_tokens", 0)
    per_m = 1e-6
    base = m["input"]
    mult = m["batch_mult"] if batch else 1.0
    cost = (
        inp * base * per_m
        + out * m["output"] * per_m
        + cr * base * m["cache_read_mult"] * per_m
        + cw * base * m["cache_write_5m_mult"] * per_m
    ) * mult
    return cost
