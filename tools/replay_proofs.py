"""usage: python tools/replay_proofs.py <rust project dir> [--aeneas on|off] [--limit N]

replays the lean-only proof layers (aeneas tactic layer, mathlib tactics, hammer)
against cached rust-unit candidates, callees-first, with no llm call (decompose_and_prove
is skipped). reports lean cost per layer and open goals logged by the aeneas layer.
"""
import sys
import os
import json
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import events
from lean import LeanChecker
from loader import load_rust_project
import callgraph


def _layer_row():
    return {"candidates": 0, "proved": 0, "lean_s": 0.0, "timeouts": 0, "mem_killed": 0}


def _parse_args(argv):
    project = argv[0]
    aeneas_on = True
    limit = None
    i = 1
    while i < len(argv):
        if argv[i] == "--aeneas":
            aeneas_on = argv[i + 1] == "on"
            i += 2
        elif argv[i] == "--limit":
            limit = int(argv[i + 1])
            i += 2
        else:
            i += 1
    return project, aeneas_on, limit


def main():
    if not sys.argv[1:]:
        print(__doc__)
        sys.exit(1)
    project, aeneas_on, limit = _parse_args(sys.argv[1:])
    project = os.path.abspath(os.path.expanduser(project))

    by_layer = defaultdict(_layer_row)
    open_goals = defaultdict(int)

    def _collect(kind, **fields):
        fields = {**events.current_context(), **fields}
        if kind == "lean":
            layer = fields.get("layer")
            if layer:
                d = by_layer[layer]
                d["lean_s"] += fields.get("elapsed", 0.0)
                if fields.get("timed_out"):
                    d["timeouts"] += 1
                if fields.get("mem_killed"):
                    d["mem_killed"] += 1
        elif kind == "open_goal":
            open_goals[fields.get("head", "?")] += 1

    events.emit = _collect

    benches = {b["name"]: b for b in load_rust_project(project)}
    g = callgraph.for_project(project)
    topo = g.topo_sorted_names()
    order = {n: i for i, n in enumerate(topo)}

    cache_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".lss", "cache")
    candidates = []  # (bench, name, stmt), callees-first
    skipped = 0
    for bm in sorted(benches.values(), key=lambda b: order.get(b.get("lean_name"), len(topo))):
        path = os.path.join(cache_dir, bm["name"] + ".json")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as f:
            specs = json.load(f)
        for s in specs:
            if not (s.get("name") and s.get("stmt")):
                continue
            # gates 1-3 (dedup/typecheck/eval/vacuity) run before any prover is
            # called; a candidate rejected there never reaches validate()'s provers.
            if s.get("status") == "rejected" and s.get("fail_gate") in ("dedup", "g1", "g2", "g3"):
                skipped += 1
                continue
            candidates.append((bm, s["name"], s["stmt"]))

    print(f"skipped (gates 1-3, never reached the provers): {skipped}")

    if limit is not None:
        candidates = candidates[:limit]

    checker = LeanChecker()
    unproved = 0
    by_candidate = []  # (func, name, layer or "unproved")
    for bm, name, stmt in candidates:
        lean_env = bm["lean_code"].rstrip() + "\n" + bm.get("lean_preamble", "")
        func = bm["func_name"]
        proved_by = None

        if aeneas_on:
            by_layer["aeneas"]["candidates"] += 1
            pr = checker.try_aeneas(stmt, func, project, candidate_id=name)
            if pr.proved:
                by_layer["aeneas"]["proved"] += 1
                proved_by = "aeneas"

        if proved_by is None:
            by_layer["tactics"]["candidates"] += 1
            pr = checker.try_proof(lean_env, stmt, func_name=func, project_dir=project)
            if pr.proved:
                by_layer["tactics"]["proved"] += 1
                proved_by = "tactics"

        if proved_by is None:
            by_layer["hammer"]["candidates"] += 1
            pr = checker.try_hammer(lean_env, stmt, func_name=func, project_dir=project)
            if "timeout" in (pr.error or ""):
                by_layer["hammer"]["timeouts"] += 1
            if pr.proved:
                by_layer["hammer"]["proved"] += 1
                proved_by = "hammer"

        if proved_by is None:
            unproved += 1
        line = proved_by or "unproved"
        by_candidate.append((func, name, line))
        # printed now, flushed, so a crash mid-run still leaves a trace of how far
        # the replay got and on which candidate; the final section below reprints
        # the same lines together once the run completes normally.
        print(f"  {func:25} {name:30} {line}", flush=True)

    print(f"candidates used: {len(candidates)} (aeneas layer: {'on' if aeneas_on else 'off'})")
    print("\nby layer")
    for lname in ("aeneas", "tactics", "hammer"):
        if lname not in by_layer:
            continue
        d = by_layer[lname]
        print(f"  {lname:10} candidates={d['candidates']:4} proved={d['proved']:4}"
              f" lean_s={d['lean_s']:7.1f} timeouts={d['timeouts']} mem_killed={d['mem_killed']}")
    print(f"  {'unproved':10} candidates={unproved}")

    if open_goals:
        print("\nopen goals by head symbol (aeneas layer)")
        for head, n in sorted(open_goals.items(), key=lambda kv: -kv[1]):
            print(f"  {head:20} {n}")

    print("\nby candidate")
    for func, name, layer in by_candidate:
        print(f"  {func:25} {name:30} {layer}")


if __name__ == "__main__":
    main()
