"""usage: python tools/cost_report.py <events.jsonl>"""
import sys
import json
from collections import defaultdict


def _row():
    return {"llm_calls": 0, "input": 0, "output": 0, "cached": 0,
            "usd": 0.0, "lean_calls": 0, "lean_s": 0.0,
            "via_lake": 0, "timed_out": 0, "restarted": 0, "max_elapsed": 0.0}


def _layer_row():
    return {"lean_calls": 0, "lean_s": 0.0, "timed_out": 0,
            "restarted": 0, "swapped": 0, "proofs": 0}


# method prefix -> layer name (how lean.py and synth.py build the method string):
# try_proof_batch "l1:<tactic>", try_hammer "l2:hammer (...)", try_aeneas
# "aeneas:<a|b|h>", decompose_and_prove "l3:<how>"
_METHOD_LAYER = {"l1:": "tactics", "l2:": "hammer", "aeneas:": "aeneas", "l3:": "decompose"}
# proofs hammer found: on the whole goal, or as the closer after step*
_HAMMER_METHODS = {"l2:hammer": "whole goal", "aeneas:h": "after step*"}


def main():
    if len(sys.argv) < 2:
        print("usage: cost_report.py <events.jsonl>")
        sys.exit(1)
    report(sys.argv[1])


def report(path):
    """print the cost report of one run's events file."""
    totals = _row()
    by_stage = defaultdict(_row)
    by_model = defaultdict(_row)
    by_func = defaultdict(_row)
    verdicts_of = defaultdict(list)
    by_layer = defaultdict(_layer_row)
    lean_events = []
    context_chars = {}  # func -> (chars sent, chars of the whole crate source)
    hammer_closes = defaultdict(lambda: defaultdict(int))  # track -> where -> proofs

    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
            except json.JSONDecodeError:
                continue
            kind = ev.get("kind")
            stage = ev.get("stage", "")
            func = ev.get("func", "")
            if kind == "llm":
                inp = ev.get("input_tokens", 0)
                out = ev.get("output_tokens", 0)
                cr = ev.get("cache_read_input_tokens", 0)
                usd = ev.get("usd", 0.0)
                for d in (totals, by_stage[stage], by_model[ev.get("model", "")]):
                    d["llm_calls"] += 1
                    d["input"] += inp
                    d["output"] += out
                    d["cached"] += cr
                    d["usd"] += usd
                if func:
                    for k, v in [("llm_calls", 1), ("input", inp), ("output", out),
                                 ("cached", cr), ("usd", usd)]:
                        by_func[func][k] += v
            elif kind == "lean":
                s = ev.get("elapsed", 0.0)
                totals["lean_calls"] += 1
                totals["lean_s"] += s
                d = by_stage[stage]
                d["lean_calls"] += 1
                d["lean_s"] += s
                if ev.get("via") == "lake":
                    d["via_lake"] += 1
                if ev.get("timed_out"):
                    d["timed_out"] += 1
                if ev.get("restarted"):
                    d["restarted"] += 1
                d["max_elapsed"] = max(d["max_elapsed"], s)
                if func:
                    by_func[func]["lean_calls"] += 1
                    by_func[func]["lean_s"] += s
                lean_events.append({
                    "elapsed": s, "stage": stage,
                    "via": ev.get("via", ""), "timed_out": ev.get("timed_out", False),
                    "restarted": ev.get("restarted", False), "n_errors": ev.get("n_errors", 0),
                })
                layer = ev.get("layer", "")
                if layer:
                    ld = by_layer[layer]
                    ld["lean_calls"] += 1
                    ld["lean_s"] += s
                    if ev.get("timed_out"):
                        ld["timed_out"] += 1
                    if ev.get("restarted"):
                        ld["restarted"] += 1
                    if ev.get("swapped"):
                        ld["swapped"] += 1
            elif kind == "verdict":
                if func:
                    verdicts_of[func].append(ev.get("status", "?"))
                method = ev.get("method", "")
                if ev.get("status") == "proved" and method:
                    for prefix, lname in _METHOD_LAYER.items():
                        if method.startswith(prefix):
                            by_layer[lname]["proofs"] += 1
                            break
                    for prefix, where in _HAMMER_METHODS.items():
                        if method.startswith(prefix):
                            hammer_closes[ev.get("source", "?")][where] += 1
            elif kind == "prompt_context" and func:
                context_chars[func] = (ev.get("chars", 0), ev.get("chars_whole", 0))

    def _fmt(d):
        return (f"llm={d['llm_calls']} in={d['input']} out={d['output']} "
                f"cached={d['cached']} usd=${d['usd']:.4f} "
                f"lean={d['lean_calls']} lean_s={d['lean_s']:.1f}")

    def _fmt_stage(d):
        extra = ""
        if d["lean_calls"] > 0:
            extra = (f" lake={d['via_lake']} tout={d['timed_out']}"
                     f" restart={d['restarted']} maxs={d['max_elapsed']:.1f}")
        return _fmt(d) + extra

    print("totals")
    print(f"  {_fmt(totals)}")

    if by_stage:
        print("\nby stage")
        for stage, d in sorted(by_stage.items()):
            print(f"  {stage or '(none)':25} {_fmt_stage(d)}")

    if by_model:
        print("\nby model")
        for model, d in sorted(by_model.items()):
            print(f"  {model:35} {_fmt(d)}")

    if by_func or verdicts_of:
        print("\nby function")
        for func in sorted(set(by_func) | set(verdicts_of)):
            d = by_func[func]
            vs = ", ".join(verdicts_of[func]) or "-"
            calls, tokens = int(d["llm_calls"]), int(d["input"])
            per_call = tokens // calls if calls else 0
            ctx = (f" context={context_chars[func][0]} chars (whole crate {context_chars[func][1]})"
                   if func in context_chars else "")
            print(f"  {func:30} usd=${d['usd']:.4f} lean_s={d['lean_s']:.1f} llm={calls}"
                  f" in_tokens={tokens} ({per_call}/call){ctx} verdicts=[{vs}]")

    if hammer_closes or by_layer.get("hammer"):
        print("\nhammer closes")
        for track in sorted(hammer_closes) or ["-"]:
            got = hammer_closes.get(track, {})
            print(f"  {track:12} whole goal={got.get('whole goal', 0)} after step*={got.get('after step*', 0)}")

    if by_layer:
        print("\nby layer")
        layer_lean = 0
        layer_s = 0.0
        layer_tout = 0
        layer_restart = 0
        layer_swap = 0
        layer_proofs = 0
        for lname in sorted(by_layer, key=lambda n: -by_layer[n]["lean_s"]):
            ld = by_layer[lname]
            print(f"  {lname:12} lean={ld['lean_calls']} s={ld['lean_s']:.1f}"
                  f" tout={ld['timed_out']} restart={ld['restarted']}"
                  f" swap={ld['swapped']} proofs={ld['proofs']}")
            layer_lean += ld["lean_calls"]
            layer_s += ld["lean_s"]
            layer_tout += ld["timed_out"]
            layer_restart += ld["restarted"]
            layer_swap += ld["swapped"]
            layer_proofs += ld["proofs"]
        no_lean = totals["lean_calls"] - layer_lean
        no_s = totals["lean_s"] - layer_s
        no_tout = sum(1 for e in lean_events if e["timed_out"]) - layer_tout
        no_restart = sum(1 for e in lean_events if e["restarted"]) - layer_restart
        print(f"  {'(no layer)':12} lean={no_lean} s={no_s:.1f}"
              f" tout={no_tout} restart={no_restart}"
              f" swap=0 proofs=0")

    if lean_events:
        print("\nslowest lean calls")
        for e in sorted(lean_events, key=lambda x: x["elapsed"], reverse=True)[:10]:
            print(f"  {e['elapsed']:6.1f}s  stage={e['stage'] or '(none)':20}"
                  f" via={e['via']:4} tout={e['timed_out']} restart={e['restarted']}"
                  f" nerr={e['n_errors']}")


if __name__ == "__main__":
    main()
