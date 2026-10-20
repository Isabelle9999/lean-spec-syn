"""harness: per-function statuses from kernel-proved specs only. --static needs
no Lean."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

static = "--static" in sys.argv
fails = []

print(f"mode {'static' if static else 'full'}")


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


def _spec(status, stmt="f x ⦃ r => r = x ⦄"):
    return {"name": "s", "stmt": stmt, "status": status, "method": ""}


def run_static_metrics():
    import metrics
    import benchmarks
    import synth

    print("[metrics]")
    st = metrics.unit_status
    check("a function counts as proved only with a kernel-proved spec",
          st([_spec("unproved"), _spec("rejected")]) == "unknown"
          and st([_spec("unproved"), _spec("proved")]) == "proved_total")
    check("a function whose proved specs all allow divergence is proved_partial",
          st([_spec("proved", "f x ⦃ r => r = x ⦄div")]) == "proved_partial"
          and st([_spec("proved", "f x ⦃ r => r = x ⦄div"), _spec("proved")]) == "proved_total")
    check("a function whose only refuted specs are wrong guesses is unknown, not refuted",
          st([_spec("refuted"), _spec("unproved")]) == "unknown" and st([]) == "unknown")
    check("unknown functions stay in the yield denominator, skipped ones leave it",
          metrics.yield_counts(["proved_total", "proved_partial", "unknown", "unknown", "skipped"]) == (2, 4))
    rep = metrics.generate_report("f", [_spec("proved"), _spec("unproved")], 1.0, 3, 4, kill_rate=0.5)
    gone = ("soundness", "avg_clarity", "avg_uniqueness", "admissibility", "precision", "validated_count")
    check("the report has a status and no ad hoc scores",
          rep["status"] == "proved_total" and rep["proved_count"] == 1 and rep["unproved_count"] == 1
          and not any(k in rep for k in gone)
          and not any(hasattr(metrics, f) for f in ("clarity_score", "uniqueness_score",
                                                    "admissibility_check", "soundness_score")),
          str(sorted(rep)))
    try:
        score = benchmarks.evaluate([_spec("unproved")], {"func_name": "f", "lean_code": "def f := 1"},
                                    lean_checker=object())
    except Exception as e:  # an unproved spec reached the mutation engine
        score = repr(e)
    check("the mutation score uses only kernel-proved specs",
          score == {"kill_rate": None, "mutation_counts": None}, str(score))
    r = synth.run_adversarial_tier([_spec("unproved")], "def f := 1", "f", None, None, None)
    check("an unproved spec does not reach the adversarial tier", r["attacked"] is False, str(r))
    check("post-completeness is gone", not hasattr(synth, "compute_post_completeness"))


def _read_events(path):
    import json
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def run_static_results():
    import argparse
    import json
    import tempfile
    import time
    import events
    import lss_config

    print("[results]")
    old_cwd = os.getcwd()
    tmp = tempfile.mkdtemp()
    os.chdir(tmp)
    try:
        import run
        check("importing run starts no run log", not os.path.exists(".lss/runs"))
        import builtins
        os.makedirs(".lss/runs")
        for f in ("run_2.txt", "run_7.txt", "run_7.events.jsonl"):
            open(os.path.join(".lss/runs", f), "w").close()
        orig_print = builtins.print
        try:
            run._start_log()
        finally:
            builtins.print = orig_print
        check("a new run id is one past the highest in use, never a reused one", run._run_id == 8, str(run._run_id))

        events.configure(1, {"t": 1})
        path = events.log_path()
        assert path is not None
        args = argparse.Namespace(verbose=False, debug=False, quick=True, timeout=5)
        bm = {"name": "b1", "lean_code": "def f (x : Nat) : Nat := x", "func_name": "f"}

        def fake_synth(*a, **k):
            events.emit("probe")
            return [_spec("proved"), _spec("unproved")]

        saved = (run.synthesize, run.evaluate, run.check_trait_obligations)
        run.evaluate = lambda *a, **k: {"kill_rate": None, "mutation_counts": None}
        run.check_trait_obligations = lambda *a, **k: {"trait_found": False}
        try:
            run.synthesize = fake_synth
            run.run_bench(bm, args, None, None, None)
            evs = _read_events(path)
            probe = [e for e in evs if e["kind"] == "probe"]
            res = [e for e in evs if e["kind"] == "unit_result"]
            check("every event of a function carries its unit, inside the timeout thread too",
                  len(probe) == 1 and probe[0].get("unit") == "b1", str(probe))
            check("a function ends with one unit_result: status, spec counts and seconds",
                  len(res) == 1 and res[0]["unit"] == "b1" and res[0]["status"] == "proved_total"
                  and res[0]["proved"] == 1 and res[0]["unproved"] == 1 and res[0]["generated"] == 2
                  and res[0]["seconds"] >= 0, str(res))

            run.synthesize = lambda *a, **k: time.sleep(3)
            run.run_bench(dict(bm, name="b2"), argparse.Namespace(**{**vars(args), "timeout": 1}),
                          None, None, None)
            res = [e for e in _read_events(path) if e["kind"] == "unit_result" and e["unit"] == "b2"]
            check("a timeout still ends with one unit_result, status unknown",
                  len(res) == 1 and res[0]["status"] == "unknown" and res[0]["reason"] == "timeout", str(res))

            def boom(*a, **k):
                raise ValueError("x")
            run.synthesize = boom
            raised = False
            try:
                run.run_bench(dict(bm, name="b3"), args, None, None, None)
            except ValueError:
                raised = True
            res = [e for e in _read_events(path) if e["kind"] == "unit_result" and e["unit"] == "b3"]
            check("a crash ends with unit_result unknown and is raised again",
                  raised and len(res) == 1 and res[0]["status"] == "unknown"
                  and res[0]["reason"] == "crash: ValueError", str(res))

            asked = []
            run.synthesize = lambda *a, **k: asked.append(1) or []
            try:
                out = run.run_bench(dict(bm, name="b4", source="rust-aeneas"), args, None, _Builds({"/s/bad"}), None,
                                    project_dir="/s/bad")
            except Exception as e:  # an attempt that went ahead, and failed on the fake checker
                out = repr(e)
            res = [e for e in _read_events(path) if e["kind"] == "unit_result" and e["unit"] == "b4"]
            check("a function whose crate does not build is unknown at once, with the build error, before any LLM call",
                  out == (None, None) and not asked and len(res) == 1 and res[0]["status"] == "unknown"
                  and res[0]["reason"] == "crate env: :12:4: error: Unknown identifier `x`", str(res))
        finally:
            run.synthesize, run.evaluate, run.check_trait_obligations = saved
    finally:
        os.chdir(old_cwd)

    base = json.dumps(lss_config.config(), sort_keys=True)
    os.environ["LSS_OVERRIDES"] = json.dumps({"proof": {"rust_hammer": True}})
    lss_config._CFG = None
    try:
        on = lss_config.proof_cfg()["rust_hammer"]
        changed = json.dumps(lss_config.config(), sort_keys=True) != base
    finally:
        del os.environ["LSS_OVERRIDES"]
        lss_config._CFG = None
    check("a bench variant's overrides change the config the run hashes",
          on is True and changed and lss_config.proof_cfg()["rust_hammer"] is False)


def _unit(crate, name, family=None, lines=10, callees=0, **shape):
    u = {"crate": crate, "bench": name, "lean_name": f"{crate}.{name}", "family": family or name,
         "lines": lines, "callees": callees}
    u.update({k: shape.get(k, False) for k in ("loop", "diverge", "generic", "mutual", "self_rec")})
    return u


def _units():
    return [
        _unit("A", "a1", loop=True, lines=40), _unit("A", "a1_loop", family="a1", loop=True, diverge=True, lines=60),
        _unit("A", "a2", lines=5), _unit("A", "a3", generic=True, lines=12),
        # harder than a3 and c1 by size alone: without coverage first, generic and self_rec go unpicked
        _unit("A", "a4", diverge=True, lines=50), _unit("A", "a5", loop=True, lines=45),
        _unit("C", "c5", loop=True, diverge=True, lines=30),
        _unit("B", "b1", mutual=True, lines=20), _unit("B", "b2", mutual=True, lines=22),
        _unit("B", "b3", callees=9, lines=30), _unit("B", "b4", lines=3),
        _unit("C", "c1", self_rec=True, lines=15), _unit("C", "c2", lines=80, callees=2),
        _unit("C", "c3", lines=4), _unit("C", "c4", diverge=True, lines=9),
    ]


class _Builds:
    """a checker whose crate envs build, except the paths in `bad`."""

    def __init__(self, bad=()):
        self.bad = set(bad)

    def _aeneas_env_for(self, p):
        return {"ok": p not in self.bad, "error": "" if p not in self.bad else ":12:4: error: Unknown identifier `x`"}


class _FakeGraph:
    def __init__(self, crate, defs, groups=()):  # defs: name -> (lines, callees, opaque)
        self.crate = crate
        self.defs = defs
        self.names = set(defs)
        grouped = {n for g in groups for n in g}
        self.sccs = [frozenset(g) for g in groups] + [frozenset([n]) for n in sorted(defs) if n not in grouped]

    def def_text(self, n):
        return "\n".join(["x"] * self.defs[n][0])

    def scc_of(self, n):
        return next(i for i, c in enumerate(self.sccs) if n in c)

    def generic(self, n):
        return False

    def callees(self, n):
        return set()

    def transitive_callees(self, n):
        return set(self.defs[n][1])

    def is_opaque(self, n):
        return self.defs[n][2]


def run_static_bench():
    import contextlib
    import io
    import json
    import subprocess
    import tempfile
    import callgraph
    import loader
    import lss_config
    from tools import bench

    print("[bench]")
    dev = bench.pick(_units(), 6, seed=0, per_crate=2)
    kinds = {k for u in dev for k in u["kinds"]}
    present = {k for u in _units() for k in ("loop", "diverge", "generic", "mutual", "self_rec") if u[k]}
    check("the dev pick covers every kind of hard function and every crate",
          present <= kinds and {"deep", "large"} <= kinds and {u["crate"] for u in dev} == {"A", "B", "C"},
          f"{[u['bench'] for u in dev]} {kinds}")
    check("at most one function per loop family and per_crate per crate",
          len({u["family"] for u in dev}) == len(dev)
          and max(sum(1 for u in dev if u["crate"] == c) for c in "ABC") <= 2)
    again = bench.pick(_units(), 6, seed=0, per_crate=2)
    check("the pick is fixed by the seed", [u["bench"] for u in dev] == [u["bench"] for u in again])
    check("the easiest functions are left out", not {"a2", "b4", "c3"} & {u["bench"] for u in dev},
          str([u["bench"] for u in dev]))

    tmp = tempfile.mkdtemp()
    old_cwd = os.getcwd()
    graphs = {"/s/a": _FakeGraph("A", {"A.f": (10, [], False), "A.g": (30, ["A.f"], False), "A.o": (5, [], True)}),
              "/s/b": _FakeGraph("B", {"B.h": (12, [], False)})}
    benches = {p: [{"name": "rust_" + n.split(".")[1], "lean_name": n} for n in g.defs] for p, g in graphs.items()}
    cfg = lambda: {"suite": ["/s/a", "/s/b"], "dev_size": 2, "seed": 0}  # noqa: E731
    calls = []

    def fake_run(argv, stdout=None, stderr=None, env=None):
        calls.append((argv, env))
        return subprocess.CompletedProcess(argv, 0)

    os.chdir(tmp)
    try:
        with Patch((callgraph, "for_project", lambda p: graphs[p]), (loader, "load_rust_project", lambda p: benches[p]),
                   (loader, "load_manifest", lambda p: {}), (loader, "detect_crate", lambda p, m: graphs[p].crate),
                   (lss_config, "bench_cfg", cfg), (subprocess, "run", fake_run)):
            with contextlib.redirect_stdout(io.StringIO()):
                split = bench.select(2, 0, checker=_Builds())
            dev_keys = {(u["crate"], u["bench"]) for u in split["dev"]}
            test_keys = {(u["crate"], u["bench"]) for u in split["test"]}
            check("the test set is every other function, never a dev one, and no opaque one",
                  len(dev_keys) == 2 and not dev_keys & test_keys
                  and dev_keys | test_keys == {("A", "rust_f"), ("A", "rust_g"), ("B", "rust_h")},
                  f"{dev_keys} {test_keys}")
            try:
                bench.run("test", "t", {}, checker=_Builds())
                refused = False
            except SystemExit:
                refused = True
            check("the test set runs only with --final", refused and not calls)
            with contextlib.redirect_stdout(io.StringIO()):
                bench.run("dev", "base", bench._overrides(["proof.rust_hammer=true", "proof.split_seconds=60"]),
                          checker=_Builds())
            one_each = all(a.count("--bench") == 1 and a[a.index("--bench") + 1] in {b for _, b in dev_keys}
                           for a, _ in calls)
            argv, env = calls[0] if calls else ([], {})
            check("each function runs in its own process, with the tag, the overrides and the tag's own cache",
                  len(calls) == len(dev_keys) and one_each and "--force-full" in argv
                  and argv[argv.index("--rust-project") + 1] in ("/s/a", "/s/b")
                  and env.get("LSS_BENCH_TAG") == "base"
                  and env.get("LSS_CACHE_PATH") == os.path.join(".lss", "bench", "base", "cache.json")
                  and json.loads(env.get("LSS_OVERRIDES", "{}")) == {"proof": {"rust_hammer": True, "split_seconds": 60}},
                  str(calls))
            n = len(calls)
            try:
                bench.run("dev", "base", {}, checker=_Builds())
                reused = True
            except SystemExit:
                reused = False
            check("a tag already run is refused, so two runs are never mixed", not reused and len(calls) == n)
            stopped = []
            for step in (lambda: bench.select(2, 0, checker=_Builds({"/s/b"})),
                         lambda: bench.run("dev", "base2", {}, checker=_Builds({"/s/a", "/s/b"}))):
                try:
                    with contextlib.redirect_stdout(io.StringIO()):
                        step()
                except SystemExit as e:
                    stopped.append(str(e))
            check("a crate whose Lean code does not build stops select and run before any function is attempted",
                  len(stopped) == 2 and all("/s/b" in m for m in stopped) and len(calls) == n
                  and not os.path.exists(os.path.join(".lss", "bench", "base2", "meta.json")), str(stopped))
        bad = []
        for arg in ("proof.rust_hamer=true", "proof.rust_hammer=False", "rust_hammer=true"):
            try:
                bench._overrides([arg])
            except SystemExit:
                bad.append(arg)
        check("a --set key not in lss.toml, or a value that is not JSON, is refused", len(bad) == 3, str(bad))

        # a mutual-recursion group is one seat: its second member never takes a seat
        groups = {"/s/m": _FakeGraph("M", {"M.even": (40, ["M.odd"], False), "M.odd": (40, ["M.even"], False),
                                           "M.plain": (12, [], False)}, groups=[("M.even", "M.odd")]),
                  "/s/b": graphs["/s/b"]}
        gbench = {"/s/m": [{"name": "rust_" + n.split(".")[1], "lean_name": n} for n in groups["/s/m"].defs],
                  "/s/b": benches["/s/b"]}
        with Patch((callgraph, "for_project", lambda p: groups[p]), (loader, "load_rust_project", lambda p: gbench[p]),
                   (lss_config, "bench_cfg", lambda: {"suite": ["/s/m", "/s/b"], "dev_size": 3, "seed": 0})):
            with contextlib.redirect_stdout(io.StringIO()):
                gsplit = bench.select(3, 0, checker=_Builds())
        gdev = {u["bench"] for u in gsplit["dev"]}
        gtest = {u["bench"] for u in gsplit["test"]}
        gheld = {u["bench"] for u in gsplit["held_back"]}
        check("a mutual-recursion group takes one dev seat, not one per member",
              len(gdev & {"rust_even", "rust_odd"}) == 1 and "rust_plain" in gdev, str(gdev))
        check("the rest of a dev function's group is held back, never in the test set",
              len(gheld) == 1 and gheld <= {"rust_even", "rust_odd"} and not gtest & {"rust_even", "rust_odd"},
              f"{gheld} {gtest}")

        # events of two tagged runs (and one untagged), for report and compare
        os.makedirs(".lss/runs", exist_ok=True)
        meta = {"set": "dev", "units": ["u1@A", "u2@A", "u3@A"], "kinds": {"u1@A": ["loop"], "u2@A": [], "u3@A": ["loop"]},
                "paths": {"A": "/s/a"}, "overrides": {}}
        for tag, res in (("base", {"u1": "proved_total", "u2": "unknown"}),
                         ("new", {"u1": "proved_total", "u2": "proved_partial", "u3": "unknown"})):
            os.makedirs(f".lss/bench/{tag}", exist_ok=True)
            with open(f".lss/bench/{tag}/meta.json", "w") as f:
                json.dump(meta, f)
            with open(f".lss/runs/run_{tag}.events.jsonl", "w") as f:
                f.write(json.dumps({"kind": "run_start", "tag": tag, "project": "/s/a"}) + "\n")
                for u, st in res.items():
                    f.write(json.dumps({"kind": "llm", "unit": u, "usd": 0.5, "input_tokens": 100, "output_tokens": 10}) + "\n")
                    f.write(json.dumps({"kind": "llm", "unit": u, "usd": 0.25, "input_tokens": 50, "output_tokens": 5}) + "\n")
                    f.write(json.dumps({"kind": "unit_result", "unit": u, "status": st, "seconds": 60,
                                        "proved": 1, "generated": 3}) + "\n")
        with open(".lss/runs/run_other.events.jsonl", "w") as f:
            f.write(json.dumps({"kind": "run_start", "tag": "", "project": "/s/a"}) + "\n")
            f.write(json.dumps({"kind": "unit_result", "unit": "u3", "status": "proved_total"}) + "\n")
        _, rows = bench.results("base")
        check("a function's dollars and tokens are summed from its own events",
              rows["u1@A"]["usd"] == 0.75 and rows["u1@A"]["input"] == 150 and rows["u1@A"]["output"] == 15,
              str(rows["u1@A"]))
        check("a function with no result is unknown, and another run's result is not used",
              rows["u3@A"]["status"] == "unknown" and rows["u3@A"]["reason"] == "no result", str(rows["u3@A"]))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            bench.report("base")
        check("yield counts unknown functions in its denominator, with a Wilson interval",
              "yield: 1 of 3 functions have a kernel-proved spec (33%, 95% CI 6%-79%)" in out.getvalue(), out.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            gains, losses = bench.compare("base", "new")
        check("compare pairs functions and tests the changed ones",
              gains == ["u2@A"] and losses == [] and "p = 1.000" in out.getvalue(), out.getvalue())
    finally:
        os.chdir(old_cwd)

    lo, hi = bench.wilson(0, 10)
    lo5, hi5 = bench.wilson(5, 10)
    check("the Wilson interval matches published values",
          lo == 0.0 and abs(hi - 0.2775) < 1e-4 and abs(lo5 - 0.2366) < 1e-4 and abs(hi5 - 0.7634) < 1e-4,
          f"{(lo, hi)} {(lo5, hi5)}")
    check("the sign test is exact",
          bench.sign_test(6, 0) == 0.03125 and bench.sign_test(8, 2) == 0.109375 and bench.sign_test(0, 0) == 1.0)


def run_full_select():
    """the dev pick on FeatureSuite's real unit graph (the suite itself is picked on
    Bobbi's machine by the last step of this PR)."""
    import contextlib
    import io
    import tempfile
    import lss_config
    from tools import bench

    print("[full: select on FeatureSuite]")
    rust_dir = os.path.expanduser("~/rust_benchmarks")
    if not os.path.isdir(os.path.join(rust_dir, "FeatureSuite", "Code")):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, "not a directory")
        return
    cfg = lambda: {"suite": [rust_dir], "dev_size": 5, "seed": 0}  # noqa: E731
    old_cwd = os.getcwd()
    os.chdir(tempfile.mkdtemp())
    try:
        with Patch((lss_config, "bench_cfg", cfg)), contextlib.redirect_stdout(io.StringIO()):
            split = bench.select(5, 0)
            first = open(bench.SPLIT, encoding="utf-8").read()
            bench.select(5, 0)
            second = open(bench.SPLIT, encoding="utf-8").read()
    finally:
        os.chdir(old_cwd)
    sets = split["dev"] + split["test"] + split["held_back"]
    units = {u["lean_name"]: u for u in sets}
    check("every FeatureSuite function lands in exactly one of dev, test and held back",
          len(units) == len(sets) == split["suite"].get("FeatureSuite"),
          f"{len(split['dev'])}+{len(split['test'])}+{len(split['held_back'])} vs {split['suite']}")
    loop = units.get("FeatureSuite.search.linear_search_loop", {})
    ident = units.get("FeatureSuite.identity", {})
    check("the kinds are read off the unit graph: a loop is a loop, identity is plain",
          "loop" in loop.get("kinds", []) and not set(ident.get("kinds", ["?"])) - {"large"},
          f"{loop} {ident}")
    # FeatureSuite is one crate, so the pick stops at the per-crate cap
    check("on one real crate the dev set stops at the per-crate cap and is fixed by the seed",
          len(split["dev"]) == min(5, bench.PER_CRATE) and first == second,
          str([u["bench"] for u in split["dev"]]))


class Patch:
    """set attributes for the length of a `with` block."""

    def __init__(self, *triples):
        self.triples = triples
        self.saved = []

    def __enter__(self):
        for obj, name, value in self.triples:
            self.saved.append((obj, name, getattr(obj, name)))
            setattr(obj, name, value)
        return self

    def __exit__(self, *_):
        for obj, name, value in reversed(self.saved):
            setattr(obj, name, value)


if static:
    run_static_metrics()
    run_static_results()
    run_static_bench()
else:
    import lean_server
    run_full_select()
    lean_server.shutdown_all()

print()
if fails:
    print(f"FAILED: {fails}")
    sys.exit(1)
print("all pass")
