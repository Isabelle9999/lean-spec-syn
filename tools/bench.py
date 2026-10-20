"""the harness: pick a fixed dev set, run a set with one config, report it, compare two runs.

  python tools/bench.py select [--size 10] [--seed 0]   writes bench/split.json
  python tools/bench.py run dev --tag baseline [--set proof.rust_hammer=true]
  python tools/bench.py report baseline
  python tools/bench.py compare baseline hammer

the suite is lss.toml [bench] suite (Aeneas-translated crates). select uses only what
the code looks like, never a result: every kind of hard function and every crate gets
a seat, then the hardest by the same features, at most one function per loop family or
mutual-recursion group and per_crate per crate. the test set is every other function and is run only with
--final. a function with no result counts as unknown and stays in every denominator.
"""
import argparse
import glob
import json
import math
import os
import random
import subprocess
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

SPLIT = os.path.join("bench", "split.json")
SHAPES = ("loop", "diverge", "generic", "mutual", "self_rec")  # read off the unit graph
PER_CRATE = 3  # at most this many dev functions from one crate


# ---- the dev set ----

def unit_features(bench, graph):
    """what the code looks like: the hard kinds it has, its size in lines and how many
    functions it calls, directly or not."""
    n = bench["lean_name"]
    text = graph.def_text(n) or ""
    scc = graph.scc_of(n)
    return {
        "loop": bench.get("loop_id") is not None or bool(bench.get("loop_is_body")),
        "diverge": bool(bench.get("can_diverge")),
        "generic": bool(graph.generic(n)),
        "mutual": scc is not None and len(graph.sccs[scc]) > 1,
        "self_rec": n in graph.callees(n),
        "lines": len(text.splitlines()),
        "callees": len(graph.transitive_callees(n)),
    }


def _family(bench, by_lean, graph):
    """what one dev seat stands for: a mutual-recursion group as a whole (its members
    share one proof effort), else the outermost function a loop or loop body belongs to."""
    scc = graph.scc_of(bench["lean_name"])
    if scc is not None and len(graph.sccs[scc]) > 1:
        return "group:" + min(graph.sccs[scc])
    seen, n = set(), bench["lean_name"]
    while n in by_lean and by_lean[n].get("parent_lean_name") and n not in seen:
        seen.add(n)
        n = by_lean[n]["parent_lean_name"]
    return n


def _quartile(values):
    v = sorted(values)
    return v[(3 * len(v)) // 4] if v else 0


def pick(units, size, seed, per_crate=PER_CRATE):
    """units: dicts with crate, bench, lean_name, family and the features. returns the
    dev picks in order: the unit covering the most kinds and crates not yet covered,
    then the hardest, ties broken by a seeded draw."""
    if not units:
        return []
    deep = _quartile([u["callees"] for u in units if u["callees"] > 0])
    large = _quartile([u["lines"] for u in units])
    top_c, top_l = max(1, max(u["callees"] for u in units)), max(1, max(u["lines"] for u in units))
    rng = random.Random(seed)
    pool = sorted(units, key=lambda u: (u["crate"], u["bench"]))
    for u in pool:
        # deep: top quarter of the functions that call any; large: top quarter by lines
        u["kinds"] = [k for k in SHAPES if u[k]] + (["deep"] if 0 < deep <= u["callees"] else []) \
            + (["large"] if u["lines"] >= large else [])
        u["hardness"] = len(u["kinds"]) + u["callees"] / top_c + u["lines"] / top_l
        u["draw"] = rng.random()
    uncovered = {k for u in pool for k in u["kinds"]} | {"crate:" + u["crate"] for u in pool}
    dev, families, crates = [], set(), defaultdict(int)
    while len(dev) < size:
        cands = [u for u in pool if u not in dev and u["family"] not in families
                 and crates[u["crate"]] < per_crate]
        if not cands:
            break
        best = max(cands, key=lambda u: (len((set(u["kinds"]) | {"crate:" + u["crate"]}) & uncovered),
                                          u["hardness"], u["draw"]))
        dev.append(best)
        families.add(best["family"])
        crates[best["crate"]] += 1
        uncovered -= set(best["kinds"]) | {"crate:" + best["crate"]}
    return dev


def _suite():
    import lss_config
    return [os.path.expanduser(p) for p in lss_config.bench_cfg()["suite"]]


def select(size, seed):
    import callgraph
    import loader
    units = []
    for path in _suite():
        g = callgraph.for_project(path)
        benches = loader.load_rust_project(path)
        by_lean = {b["lean_name"]: b for b in benches}
        for b in benches:
            if b["lean_name"] not in g.names or g.is_opaque(b["lean_name"]):
                continue
            units.append({"crate": g.crate, "bench": b["name"], "lean_name": b["lean_name"],
                          "family": f"{g.crate}:{_family(b, by_lean, g)}", **unit_features(b, g)})
    dev = pick(units, size, seed)
    keep = ("crate", "bench", "lean_name", "family", "kinds", "lines", "callees")
    names = {u["bench"] + "@" + u["crate"] for u in dev}
    fams = {u["family"] for u in dev}
    rest = sorted((u for u in units if u["bench"] + "@" + u["crate"] not in names),
                  key=lambda u: (u["crate"], u["bench"]))
    split = {
        "seed": seed, "size": size,
        "suite": {c: sum(1 for u in units if u["crate"] == c) for c in sorted({u["crate"] for u in units})},
        "kinds_covered": sorted({k for u in dev for k in u["kinds"]}),
        "dev": [{k: u[k] for k in keep} for u in dev],
        # the rest of a dev function's loop family or recursion group is in neither set:
        # tuning on one member would leak into a held-out number on the others
        "held_back": [{k: u[k] for k in keep} for u in rest if u["family"] in fams],
        "test": [{k: u[k] for k in keep} for u in rest if u["family"] not in fams],
    }
    os.makedirs(os.path.dirname(SPLIT), exist_ok=True)
    with open(SPLIT, "w", encoding="utf-8") as f:
        json.dump(split, f, indent=1, sort_keys=True)
        f.write("\n")
    print(f"suite: {sum(split['suite'].values())} functions in {len(split['suite'])} crates")
    print(f"dev: {len(dev)} functions, kinds covered: {', '.join(split['kinds_covered'])}")
    for u in dev:
        print(f"  {u['crate']}: {u['bench']}  [{', '.join(u['kinds'])}] lines={u['lines']} callees={u['callees']}")
    print(f"test: {len(split['test'])} functions; held back with their dev family: {len(split['held_back'])}")
    return split


# ---- running a set ----

def _overrides(pairs):
    """["proof.rust_hammer=true"] -> {"proof": {"rust_hammer": True}}. the key must be a
    table.key already in lss.toml and the value JSON (true, 120, "local"), so a typo
    cannot leave a variant silently identical to the baseline."""
    import lss_config
    cfg = lss_config.config()
    out = defaultdict(dict)
    for p in pairs or []:
        key, _, raw = p.partition("=")
        table, _, name = key.partition(".")
        if not isinstance(cfg.get(table), dict) or name not in cfg[table]:
            sys.exit(f"--set {p}: {key} is not a key in lss.toml")
        try:
            out[table][name] = json.loads(raw)
        except json.JSONDecodeError:
            sys.exit(f"--set {p}: the value must be JSON, e.g. true, 120 or \"local\"")
    return dict(out)


def run(set_name, tag, overrides, final=False):
    if set_name == "test" and not final:
        sys.exit("the test set runs once, for the final numbers: pass --final")
    out_dir = os.path.join(".lss", "bench", tag)
    if os.path.exists(os.path.join(out_dir, "meta.json")):
        sys.exit(f"tag {tag} was already run; use a new tag so two runs are never mixed")
    with open(SPLIT, encoding="utf-8") as f:
        units = json.load(f)[set_name]
    import loader
    paths = {loader.detect_crate(p, loader.load_manifest(p)): os.path.abspath(p) for p in _suite()}
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "meta.json"), "w", encoding="utf-8") as f:
        json.dump({"set": set_name, "units": [u["bench"] + "@" + u["crate"] for u in units],
                   "kinds": {u["bench"] + "@" + u["crate"]: u["kinds"] for u in units},
                   "paths": paths, "overrides": overrides}, f, indent=1)
    # a fresh proof cache per tag, so a second config never reuses the first's proofs
    env = {**os.environ, "LSS_BENCH_TAG": tag, "LSS_OVERRIDES": json.dumps(overrides),
           "LSS_CACHE_PATH": os.path.join(out_dir, "cache.json")}
    for u in units:
        # one process per function: a timed-out function's thread ends with its process
        # and never shares a Lean server with the next function
        log = os.path.join(out_dir, f"{u['crate']}.{u['bench']}.log")
        print(f"{u['crate']}: {u['bench']} (log {log})", flush=True)
        with open(log, "w", encoding="utf-8") as f:
            r = subprocess.run([sys.executable, "run.py", "--rust-project", paths[u["crate"]],
                                "--bench", u["bench"], "--force-full"], stdout=f, stderr=subprocess.STDOUT, env=env)
        print(f"  exit {r.returncode}", flush=True)


# ---- statistics ----

def wilson(k, n, z=1.96):
    """95% Wilson score interval for k of n (good coverage at small n, unlike the
    normal approximation)."""
    if n == 0:
        return (0.0, 1.0)
    p = k / n
    d = 1 + z * z / n
    mid = (p + z * z / (2 * n)) / d
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, mid - half), min(1.0, mid + half))


def sign_test(gains, losses):
    """exact two-sided sign test on the functions whose verdict changed."""
    n = gains + losses
    if n == 0:
        return 1.0
    k = max(gains, losses)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n)


# ---- reports ----

def results(tag, runs_dir=os.path.join(".lss", "runs")):
    """per function of the tagged run: status, spec counts, dollars, tokens, Lean and
    wall seconds. functions of the set with no result are unknown (reason: no result)."""
    with open(os.path.join(".lss", "bench", tag, "meta.json"), encoding="utf-8") as f:
        meta = json.load(f)
    rows = {u: {"status": "unknown", "reason": "no result", "usd": 0.0, "input": 0, "output": 0,
                "lean_s": 0.0, "seconds": 0.0, "proved": 0, "generated": 0} for u in meta["units"]}
    for path in sorted(glob.glob(os.path.join(runs_dir, "*.events.jsonl"))):
        with open(path, encoding="utf-8") as f:
            evs = [json.loads(line) for line in f if line.strip()]
        start = next((e for e in evs if e.get("kind") == "run_start"), None)
        if not start or start.get("tag") != tag:
            continue
        crate = next((c for c, p in meta["paths"].items() if p == start.get("project")), None)
        for e in evs:
            key = f"{e.get('unit')}@{crate}"
            if key not in rows:
                continue
            r = rows[key]
            if e["kind"] == "llm":
                r["usd"] += e.get("usd", 0.0)
                r["input"] += e.get("input_tokens", 0)
                r["output"] += e.get("output_tokens", 0)
            elif e["kind"] == "lean":
                r["lean_s"] += e.get("elapsed", 0.0)
            elif e["kind"] == "unit_result":
                r.update({k: e[k] for k in ("status", "seconds") if k in e})
                r.update({k: e.get(k, 0) for k in ("proved", "generated")})
                r["reason"] = e.get("reason", "")
    return meta, rows


def report(tag):
    from metrics import yield_counts
    meta, rows = results(tag)
    print(f"{tag}: set {meta['set']}, {len(rows)} functions, overrides {meta['overrides'] or 'none'}")
    print(f"{'function':<44} {'status':<15} {'proved':>7} {'$':>7} {'in':>8} {'out':>7} {'lean s':>7} {'wall s':>7}")
    for u, r in rows.items():
        why = f"  ({r['reason']})" if r["reason"] else ""
        print(f"{u:<44} {r['status']:<15} {r['proved']:>3}/{r['generated']:<3} {r['usd']:>7.2f} "
              f"{r['input']:>8} {r['output']:>7} {r['lean_s']:>7.0f} {r['seconds']:>7.0f}{why}")
    statuses = [r["status"] for r in rows.values()]
    k, n = yield_counts(statuses)
    lo, hi = wilson(k, n)
    kt = sum(1 for s in statuses if s == "proved_total")
    lt, ht = wilson(kt, n)
    print(f"yield: {k} of {n} functions have a kernel-proved spec ({k / n if n else 0:.0%}, 95% CI {lo:.0%}-{hi:.0%})")
    print(f"total correctness: {kt} of {n} ({lt:.0%}-{ht:.0%})")
    print("status counts: " + ", ".join(f"{s}={statuses.count(s)}" for s in sorted(set(statuses))))
    usd = sum(r["usd"] for r in rows.values())
    print(f"cost: ${usd:.2f} total, ${usd / max(1, len(rows)):.2f} per function; "
          f"wall {sum(r['seconds'] for r in rows.values()) / 3600:.1f} h; "
          f"Lean {sum(r['lean_s'] for r in rows.values()) / 3600:.1f} h")
    by_kind = defaultdict(list)
    for u, ks in meta.get("kinds", {}).items():
        for kd in ks:
            by_kind[kd].append(rows[u]["status"])
    for kd in sorted(by_kind):
        kk, nn = yield_counts(by_kind[kd])
        print(f"  {kd}: {kk} of {nn}")
    return rows


def compare(a, b):
    _, ra = results(a)
    _, rb = results(b)
    both = [u for u in ra if u in rb]
    proved = lambda r: r["status"].startswith("proved")  # noqa: E731
    gains = [u for u in both if proved(rb[u]) and not proved(ra[u])]
    losses = [u for u in both if proved(ra[u]) and not proved(rb[u])]
    print(f"{a} -> {b}: {len(both)} functions in both")
    print(f"gained a proof: {len(gains)} {gains}")
    print(f"lost a proof: {len(losses)} {losses}")
    print(f"sign test on the {len(gains) + len(losses)} changed functions: p = {sign_test(len(gains), len(losses)):.3f}")
    diffs = sorted(rb[u]["usd"] - ra[u]["usd"] for u in both)
    med = diffs[len(diffs) // 2] if diffs else 0.0
    cheaper = sum(1 for d in diffs if d < 0)
    print(f"cost: ${sum(ra[u]['usd'] for u in both):.2f} -> ${sum(rb[u]['usd'] for u in both):.2f}; "
          f"median change per function ${med:+.2f}; cheaper on {cheaper} of {len(diffs)} "
          f"(sign test p = {sign_test(cheaper, sum(1 for d in diffs if d > 0)):.3f})")
    ta = sum(ra[u]["seconds"] for u in both) / 3600
    tb = sum(rb[u]["seconds"] for u in both) / 3600
    print(f"wall time: {ta:.1f} h -> {tb:.1f} h")
    return gains, losses


def main(argv=None):
    p = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("select")
    s.add_argument("--size", type=int, default=None)
    s.add_argument("--seed", type=int, default=None)
    r = sub.add_parser("run")
    r.add_argument("set", choices=["dev", "test"])
    r.add_argument("--tag", required=True)
    r.add_argument("--set", dest="overrides", action="append", metavar="TABLE.KEY=VALUE")
    r.add_argument("--final", action="store_true")
    rp = sub.add_parser("report")
    rp.add_argument("tag")
    c = sub.add_parser("compare")
    c.add_argument("a")
    c.add_argument("b")
    args = p.parse_args(argv)
    if args.cmd == "select":
        import lss_config
        cfg = lss_config.bench_cfg()
        select(args.size or cfg["dev_size"], cfg["seed"] if args.seed is None else args.seed)
    elif args.cmd == "run":
        run(args.set, args.tag, _overrides(args.overrides), final=args.final)
    elif args.cmd == "report":
        report(args.tag)
    else:
        compare(args.a, args.b)


if __name__ == "__main__":
    main()
