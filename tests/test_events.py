import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import tempfile
import json

import events
import pricing


def test_emit_no_configure():
    # a: emit without configure is a no-op (no exception, no state)
    events._state.clear()
    events.emit("llm", model="test", ok=True)
    print("a: emit no-op ok")


def test_nested_context_merge():
    # b: nested contexts merge into the emitted line
    events._state.clear()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".jsonl", delete=False, encoding="utf-8") as f:
        fname = f.name
    events._state["run_id"] = "t1"
    events._state["config_hash"] = "abc"
    fh = open(fname, "a", encoding="utf-8", buffering=1)
    events._state["fh"] = fh
    events._stats.clear()
    events._stats.update({"llm_calls": 0, "input_tokens": 0, "output_tokens": 0,
                          "cached_tokens": 0, "usd": 0.0, "lean_calls": 0, "lean_s": 0.0})
    with events.context(func="foo"):
        with events.context(stage="validate"):
            with events.context(candidate_id="s1"):
                events.emit("verdict", status="proved")
    fh.close()
    with open(fname, encoding="utf-8") as f:
        rows = [json.loads(l) for l in f if l.strip()]
    os.unlink(fname)
    assert len(rows) == 1
    r = rows[0]
    assert r["func"] == "foo", f"func missing: {r}"
    assert r["stage"] == "validate", f"stage missing: {r}"
    assert r["candidate_id"] == "s1", f"candidate_id missing: {r}"
    assert r["status"] == "proved", f"status missing: {r}"
    events._state.clear()
    print("b: nested context merge ok")


def test_cost_usd_known():
    # c: cost_usd on fixed usage equals hand-computed value
    usage = {"input_tokens": 1_000_000, "output_tokens": 1_000_000,
             "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0}
    # input: 1M * $3/M = $3.00; output: 1M * $15/M = $15.00; total = $18.00
    got = pricing.cost_usd("claude-sonnet-4-6", usage)
    expected = 18.00
    assert abs(got - expected) < 1e-9, f"expected {expected}, got {got}"
    print("c: cost_usd known model ok")


def test_cost_usd_unknown():
    # d: unknown model raises ValueError
    try:
        pricing.cost_usd("no-such-model", {})
        assert False, "should have raised"
    except ValueError as e:
        assert "no-such-model" in str(e)
    print("d: unknown model raises ok")


if __name__ == "__main__":
    test_emit_no_configure()
    test_nested_context_merge()
    test_cost_usd_known()
    test_cost_usd_unknown()
    print("all ok")
