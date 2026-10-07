"""usage: python tools/cost_report.py <events.jsonl>"""
import sys
import json
from collections import defaultdict


def _row():
    return {"llm_calls": 0, "input": 0, "output": 0, "cached": 0,
            "usd": 0.0, "lean_calls": 0, "lean_s": 0.0,
            "via_lake": 0, "timed_out": 0, "restarted": 0, "max_elapsed": 0.0}


def main():
    if len(sys.argv) < 2:
        print("usage: cost_report.py <events.jsonl>")
        sys.exit(1)
    path = sys.argv[1]
    totals = _row()
    by_stage = defaultdict(_row)
    by_model = defaultdict(_row)
    by_func = defaultdict(lambda: {**_row(), "verdicts": []})
    lean_events = []

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
            elif kind == "verdict":
                if func:
                    by_func[func]["verdicts"].append(ev.get("status", "?"))

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

    if by_func:
        print("\nby function")
        for func, d in sorted(by_func.items()):
            vs = ", ".join(d["verdicts"]) if d["verdicts"] else "-"
            print(f"  {func:30} usd=${d['usd']:.4f} lean_s={d['lean_s']:.1f} verdicts=[{vs}]")

    if lean_events:
        print("\nslowest lean calls")
        for e in sorted(lean_events, key=lambda x: x["elapsed"], reverse=True)[:10]:
            print(f"  {e['elapsed']:6.1f}s  stage={e['stage'] or '(none)':20}"
                  f" via={e['via']:4} tout={e['timed_out']} restart={e['restarted']}"
                  f" nerr={e['n_errors']}")


if __name__ == "__main__":
    main()
