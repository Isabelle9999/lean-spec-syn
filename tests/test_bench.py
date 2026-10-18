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


if static:
    run_static_metrics()

print()
if fails:
    print(f"FAILED: {fails}")
    sys.exit(1)
print("all pass")
