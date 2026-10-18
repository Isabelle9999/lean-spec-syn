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
    check("refuted when nothing is proved and a candidate was refuted",
          st([_spec("refuted"), _spec("unproved")]) == "refuted" and st([]) == "unknown")
    check("unknown functions stay in the yield denominator, skipped ones leave it",
          metrics.yield_counts(["proved_total", "proved_partial", "unknown", "refuted", "skipped"]) == (2, 4))
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


if static:
    run_static_metrics()
    run_static_results()

print()
if fails:
    print(f"FAILED: {fails}")
    sys.exit(1)
print("all pass")
