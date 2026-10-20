import sys; import os; sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]
import argparse
import builtins
import contextvars
import json
import re
import time
import shutil
import threading
import lss_config as _lss_config

from lean import LeanChecker, ExampleStore, Cache, get_lean_calls
import lean_server as _lean_server
from synth import LLMClient, synthesize, refine, _func_name, get_llm_calls
import events
from benchmarks import BENCHMARKS, evaluate
from metrics import functional_correctness, spec_coverage, generate_report, save_report, summary_table, yield_counts
from incremental import (
    lean_version, load_hashes, save_hashes,
    compute_current_hashes, affected_benches,
    load_cached_specs, save_cached_specs,
)
from traits import check_trait_obligations
from divergence import detect_divergent, mark_divergent_specs


_run_id = 0
_log_path = ""


def _start_log():
    """tee every print of this run into .lss/runs/run_<id>.txt. called by main, so
    importing run has no side effects."""
    global _run_id, _log_path
    os.makedirs(".lss/runs", exist_ok=True)
    # one past the highest id in use, so deleting old runs never reuses an id
    ids = [int(m.group(1)) for f in os.listdir(".lss/runs") if (m := re.match(r"run_(\d+)\.", f))]
    _run_id = max(ids, default=0) + 1
    _log_path = f".lss/runs/run_{_run_id}.txt"
    log_file = open(_log_path, "w", encoding="utf-8")
    orig = builtins.print

    def tee(*args, **kwargs):
        orig(*args, **kwargs)
        kwargs["file"] = log_file
        orig(*args, **kwargs)
        log_file.flush()
    builtins.print = tee


def _with_timeout(fn, timeout):
    result = [None]
    exc = [None]
    done = threading.Event()
    ctx = contextvars.copy_context()  # the worker's events keep the caller's unit

    def worker():
        try:
            result[0] = fn()
        except Exception as e:
            exc[0] = e
        finally:
            done.set()

    t = threading.Thread(target=lambda: ctx.run(worker), daemon=True)
    t.start()

    finished = done.wait(timeout=timeout)

    if not finished:
        return None, True

    if exc[0] is not None:
        raise exc[0]

    return result[0], False


def run_bench(bm, args, llm, checker, store, baseline="none", project_dir=None, func_source=None):
    """one function. every LLM and Lean call it makes is logged with unit=<bench name>, and it ends with
    one unit_result event: the status, the spec counts and the wall seconds, also
    after a timeout or a crash (status unknown, with the reason)."""
    t0 = time.time()
    with events.context(unit=bm["name"]):
        try:
            score, report = _run_bench(bm, args, llm, checker, store, baseline, project_dir, func_source)
        except Exception as e:
            events.emit("unit_result", status="unknown", reason=f"crash: {type(e).__name__}",
                        seconds=time.time() - t0)
            raise
        if report is None:
            events.emit("unit_result", status="unknown", reason="timeout", seconds=time.time() - t0)
        else:
            events.emit("unit_result", status=report["status"], seconds=time.time() - t0,
                        **{k: report[k + "_count"] for k in ("generated", "proved", "refuted", "unproved")})
    return score, report


def _run_bench(bm, args, llm, checker, store, baseline="none", project_dir=None, func_source=None):
    fn = bm.get("func_name") or _func_name(bm["lean_code"])
    ti = bm.get("test_inputs", [])
    tpl = bm.get("templates", [])
    if bm.get("source") == "rust-aeneas" and project_dir:
        # prompts get the unit, its types and its callees' specs, not the whole crate
        func_source = checker.unit_context(project_dir, bm.get("lean_name") or fn)
        events.emit("prompt_context", func=fn, chars=len(func_source), chars_whole=len(bm.get("func_source") or ""))
    bm_eval = {**bm, "func_name": fn, "func_source": func_source}

    t0 = time.time()
    get_lean_calls()  # reset counter
    get_llm_calls()   # reset counter

    vb = args.verbose
    debug_dir = None
    if getattr(args, "debug", False):
        debug_dir = os.path.join(".lss", "debug", bm["name"])
        os.makedirs(debug_dir, exist_ok=True)

    def _synth():
        postcond_defs = bm.get("postcond_defs", {})
        lean_code = bm["lean_code"] + bm.get("lean_preamble", "")
        s = synthesize(lean_code, ti, tpl, llm, checker, store, func_name=fn, verbose=vb, debug_dir=debug_dir, postcond_defs=postcond_defs, project_dir=project_dir, func_source=func_source, source=bm.get("source"))
        if baseline == "no-mutation":
            return s
        if not args.quick:
            max_tier = 1 if baseline == "no-adversarial" else 3
            s = refine(s, bm["lean_code"], fn, ti, checker, llm, store, max_tier=max_tier, verbose=vb, project_dir=project_dir, func_source=func_source, source=bm.get("source"))
        return s

    timeout = getattr(args, "timeout", 600)
    specs, timed_out = _with_timeout(_synth, timeout)
    if timed_out:
        label = bm["name"] + (f" ({baseline})" if baseline != "none" else "")
        print(f"\n--- {label} ---")
        print(f"  timeout after {timeout}s")
        return None, None

    divergent = detect_divergent(bm.get("lean_code", ""))
    if divergent and specs:
        for dfn in divergent:
            mark_divergent_specs(specs, divergent, dfn)
    if specs:
        save_cached_specs(bm["name"], specs)

    elapsed = time.time() - t0

    eval_checker = None if baseline == "no-mutation" or args.quick else checker
    score = evaluate(specs, bm_eval, lean_checker=eval_checker, project_dir=project_dir)
    lean_calls_count = get_lean_calls()
    llm_calls_count = get_llm_calls()

    gt = bm.get("ground_truth", [])
    postcond_defs = bm.get("postcond_defs", {})
    if gt:
        lc = bm["lean_code"] + bm.get("lean_preamble", "")
        fc = functional_correctness(specs, gt, checker, postcond_defs,
                                    lean_code=lc, project_dir=project_dir)
        sc = spec_coverage(specs, gt, checker, postcond_defs,
                           lean_code=lc, project_dir=project_dir)
    else:
        fc = {"score": None}
        sc = {"score": None}

    report = generate_report(bm["name"], specs, elapsed, llm_calls_count, lean_calls_count,
                             kill_rate=score["kill_rate"])
    report["functional_correctness"] = fc
    report["spec_coverage"] = sc
    os.makedirs(".lss/reports", exist_ok=True)
    save_report(report, f".lss/reports/{bm['name']}.json")

    proved = [s for s in specs if s["status"] == "proved"]
    rejected = report["rejected_count"]
    label = bm["name"] + (f" ({baseline})" if baseline != "none" else "")
    print(f"\n--- {label} ---")
    print(f"  status:     {report['status']}")
    print(f"  generated:  {len(specs)}")
    print(f"  proved:     {len(proved)} (kernel-checked; only these count)")
    if report["unproved_count"]:
        print(f"  unproved:   {report['unproved_count']} (passed the gates, no proof; not counted)")
    if rejected:
        print(f"  rejected:   {rejected}")
        g1 = sum(1 for s in specs if s.get("fail_gate") == "g1")
        vac = sum(1 for s in specs if s.get("fail_gate") == "vacuous")
        print(f"  failure breakdown: {g1} gate, {vac} vacuous")
    refuted = [s for s in specs if s["status"] == "refuted"]
    if refuted:
        kern = sum(1 for s in refuted if s.get("refuted_by") == "kernel")
        print(f"  refuted:    {len(refuted)} ({kern} by a kernel-checked witness)")
    mc = score.get("mutation_counts")
    if mc:
        total_m = sum(mc.values())
        scored_m = mc["KILLED"] + mc["SURVIVED"]
        print(f"  mutants:    {total_m} total, {mc['KILLED']} killed, {mc['SURVIVED']} survived, "
              f"{mc['EQUIVALENT']} equiv, {mc['INCONCLUSIVE']} inconclusive, {mc['STILLBORN']} stillborn"
              + (f" (score {mc['KILLED']}/{scored_m})" if scored_m else " (score unavailable)"))
    if fc["score"] is not None:
        fc_skip = fc.get("skipped_comparisons", 0)
        sc_skip = sc.get("skipped_comparisons", 0)
        fc_nm = fc.get("not_matchable", 0)
        sc_nm = sc.get("not_matchable", 0)
        print(f"  func_correct: {fc['score']:.2f}  matched={fc['matched']} unmatched={fc['unmatched']} undetermined={fc['undetermined']}"
              + (f" not_matchable={fc_nm}" if fc_nm else "")
              + (f" skipped={fc_skip}" if fc_skip else ""))
        print(f"  spec_coverage: {sc['score']:.2f}  covered={sc['covered']} uncovered={sc['uncovered']} undetermined={sc['undetermined']}"
              + (f" not_matchable={sc_nm}" if sc_nm else "")
              + (f" skipped={sc_skip}" if sc_skip else ""))
    elif fc.get("total_proved", 0) > 0 or sc.get("total_ground_truth", 0) > 0:
        # gt exists but no proved match possible (all undetermined)
        fc_skip = fc.get("skipped_comparisons", 0)
        sc_skip = sc.get("skipped_comparisons", 0)
        fc_nm = fc.get("not_matchable", 0)
        sc_nm = sc.get("not_matchable", 0)
        print(f"  func_correct: -  matched={fc.get('matched',0)} unmatched={fc.get('unmatched',0)} undetermined={fc.get('undetermined',0)}"
              + (f" not_matchable={fc_nm}" if fc_nm else "")
              + (f" skipped={fc_skip}" if fc_skip else ""))
        print(f"  spec_coverage: -  covered={sc.get('covered',0)} uncovered={sc.get('uncovered',0)} undetermined={sc.get('undetermined',0)}"
              + (f" not_matchable={sc_nm}" if sc_nm else "")
              + (f" skipped={sc_skip}" if sc_skip else ""))
    else:
        print("  func_correct: - (no ground truth)")
        print("  spec_coverage: - (no ground truth)")
    print(f"  llm calls:  {llm_calls_count}")
    print(f"  lean calls: {lean_calls_count}")
    for s in proved:
        tag = f" [{s['method']}]" if s.get("method") else ""
        print(f"    kernel-proved{tag}  {s['name']}: {s['stmt'][:80]}")

    if divergent:
        print(f"  divergent defs: {', '.join(sorted(divergent))}")
        n_blocked = sum(1 for s in specs if s.get('blocked_by_divergence'))
        if n_blocked:
            print(f"  blocked by divergence: {n_blocked} specs")
    else:
        print("  divergent: none detected")

    _fn = bm.get("func_name") or _func_name(bm["lean_code"])
    _proved = [s for s in (specs or []) if s.get('status') == 'proved']
    _spec_map = {_fn: [s['stmt'] for s in _proved]} if _proved else {}
    _lc = bm["lean_code"] + bm.get("lean_preamble", "")
    tr = check_trait_obligations(_spec_map, _lc, checker, project_dir)
    if tr['trait_found']:
        if tr['per_edge']:
            print(f"  traits: {len(tr['traits_detected'])} trait(s), "
                  f"{len(tr['impls_detected'])} impl(s)")
            for (tn, impl, meth, st) in tr['per_edge']:
                tag = " *** VIOLATED ***" if st == 'violated' else ""
                print(f"    {tn}.{meth} [{impl}]: {st}{tag}")
            if tr['violated']:
                print(f"  *** {len(tr['violated'])} trait obligation(s) VIOLATED ***")
        else:
            print(f"  traits: {len(tr['traits_detected'])} trait(s), "
                  f"{len(tr['impls_detected'])} impl(s) detected, no impl pairs to check")
    else:
        print(f"  trait detection ({_fn}): no traits found")

    return score, report


def _ablation_table(name, variants):
    keys = ["proved_count", "mutation_score"]
    full = next(r for n, _, r in variants if n == "none")
    w, col = 12, 22
    hdr = f"{'baseline':<{col}}" + "".join(f"{k[:w]:>{w}}" for k in keys)
    print(f"\nablation: {name}")
    print(hdr)
    print("-" * len(hdr))
    for bl, _, r in variants:
        vals = [f"{r[k]:.3f}" if r.get(k) is not None else "-" for k in keys]
        print(f"{bl:<{col}}" + "".join(f"{v:>{w}}" for v in vals))
    print()
    for bl, _, r in variants:
        if bl == "none":
            continue
        label = f"delta({bl})"
        deltas = []
        for k in keys:
            v, fv = r.get(k), full.get(k)
            deltas.append(f"{v - fv:+.3f}" if v is not None and fv is not None else "-")
        print(f"{label:<{col}}" + "".join(f"{d:>{w}}" for d in deltas))


def _write_pins_header():
    repo = os.path.dirname(os.path.abspath(__file__))
    try:
        import subprocess as _sp
        sha = _sp.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True,
                      cwd=repo).stdout.strip()
        dirty = _sp.run(["git", "status", "--porcelain"], capture_output=True, text=True,
                        cwd=repo).stdout.strip()
        commit = sha + (" dirty" if dirty else "")
    except Exception:
        commit = "unknown"
    print(f"pins: repo={commit}")
    for name, pdir in _lss_config.all_projects().items():
        tc = "missing"
        tc_path = os.path.join(pdir, "lean-toolchain")
        if os.path.exists(tc_path):
            tc = open(tc_path).read().strip()
        print(f"  project={name} toolchain={tc}")
        mf_path = os.path.join(pdir, "lake-manifest.json")
        if os.path.exists(mf_path):
            with open(mf_path) as f:
                mf = json.load(f)
            for pkg in mf.get("packages", []):
                if pkg["name"] in ("aeneas", "mathlib", "repl", "Hammer"):
                    print(f"    {pkg['name']}={pkg.get('rev', '?')}")


def main():
    _start_log()
    _t_main_start = time.time()
    p = argparse.ArgumentParser()
    p.add_argument("--quick", action="store_true")
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--debug", action="store_true")
    p.add_argument("--bench", nargs="+", default=None, help="one or more benchmark names")
    p.add_argument("--baseline", choices=["none", "no-mutation", "no-adversarial"],
                   default="none")
    p.add_argument("--ablation", action="store_true")
    p.add_argument("--verina", action="store_true")
    p.add_argument("--clever", action="store_true")
    p.add_argument("--verina-path", default=r"C:\Users\User\projects\verina")
    p.add_argument("--clever-path", default=r"C:\Users\User\projects\clever")
    p.add_argument("--limit", type=int)
    p.add_argument("--timeout", type=int, default=1800)
    p.add_argument("--lean-project", type=str,
                   default=_lss_config.project_dir("aeneas"),
                   help="Lean project dir for synthesis and checking")
    p.add_argument("--rust-project", type=str, default=None,
                   help="Path to Aeneas-translated Rust project")
    p.add_argument("--force-full", action="store_true",
                   help="force full re-run, ignore incremental cache")
    args = p.parse_args()

    lean_project_dir = os.path.abspath(args.lean_project)
    rust_project_dir = os.path.abspath(args.rust_project) if args.rust_project else lean_project_dir

    _write_pins_header()

    # the config hash covers lss.toml with any bench overrides (LSS_OVERRIDES)
    _cfg_obj = {"toml": _lss_config.config(), "args": {k: v for k, v in vars(args).items() if isinstance(v, (str, int, float, bool, type(None)))}}
    events.configure(_run_id, _cfg_obj)
    events.emit("run_start", tag=os.environ.get("LSS_BENCH_TAG", ""),
                project=os.path.abspath(args.rust_project) if args.rust_project else "")

    cache = Cache(os.environ.get("LSS_CACHE_PATH", ".lss/cache.json"))  # the harness gives each tag its own
    llm = LLMClient()
    checker = LeanChecker(cache=cache, project_dir=lean_project_dir)
    store = ExampleStore()

    if args.rust_project:
        from loader import load_rust_project
        import callgraph
        benches = load_rust_project(args.rust_project)
        run_dir = rust_project_dir
        print(f"loaded {len(benches)} rust functions from {args.rust_project}")
        topo = callgraph.for_project(args.rust_project).topo_sorted_names()
        # build the crate env first: from the first unit on, every rust text runs in it
        checker._aeneas_env_for(rust_project_dir)
        order = {n: i for i, n in enumerate(topo)}
        benches.sort(key=lambda b: order.get(b.get("lean_name"), len(topo)))
    elif args.verina or args.clever:
        from loader import load_verina, load_clever
        benches = []
        if args.verina:
            benches += load_verina(args.verina_path, limit=args.limit)
        if args.clever:
            benches += load_clever(args.clever_path, limit=args.limit)
        if not benches:
            print("no benchmarks loaded")
            return
        run_dir = lean_project_dir
    else:
        benches = BENCHMARKS
        run_dir = lean_project_dir

    if args.bench:
        benches = [b for b in benches if b["name"] in args.bench]
        if not benches:
            available = ", ".join(b["name"] for b in BENCHMARKS)
            print(f"unknown: {args.bench}. available: {available}")
            return

    lean_ver = lean_version()
    prev_hashes = None if args.force_full else load_hashes()
    curr_hashes = compute_current_hashes(benches, lean_ver)
    need_rerun = affected_benches(prev_hashes, curr_hashes)
    n_reverified = 0
    n_carried = 0

    reports = []
    statuses = []  # every function attempted; a timeout or a crash is unknown
    if args.ablation:
        baselines = ["none", "no-mutation", "no-adversarial"]
        for bm in benches:
            variants = []
            for bl in baselines:
                score, report = run_bench(bm, args, llm, checker, store, bl, project_dir=run_dir, func_source=bm.get("func_source"))
                if score is not None:
                    variants.append((bl, score, report))
            if variants:
                _ablation_table(bm["name"], variants)
                full = next((r for n, _, r in variants if n == "none"), variants[0][2])
                reports.append(full)
    else:
        for bm in benches:
            if bm["name"] not in need_rerun:
                cached = load_cached_specs(bm["name"])
                if cached is not None:
                    print(f"\n--- {bm['name']} (carried forward, {len(cached)} specs) ---")
                    n_carried += 1
                    continue
            n_reverified += 1
            try:
                _, report = run_bench(bm, args, llm, checker, store, args.baseline, project_dir=run_dir, func_source=bm.get("func_source"))
                statuses.append(report["status"] if report is not None else "unknown")
                if report is not None:
                    reports.append(report)
            except Exception as e:
                statuses.append("unknown")
                print(f"  CRASH on {bm['name']}: {e}")
                import traceback
                traceback.print_exc()
                continue

    print(f"\nincremental: {n_reverified} re-verified, {n_carried} carried forward")
    save_hashes(curr_hashes)

    if len(reports) > 1:
        print("\n" + summary_table(reports))
    if statuses:
        k, n = yield_counts(statuses)
        print(f"yield: {k} of {n} functions attempted have a kernel-proved spec (timeouts and crashes count as unknown)")

    _ev = events.get_stats()
    _wall = time.time() - _t_main_start
    print(f"events: llm_calls={_ev['llm_calls']} input={_ev['input_tokens']} "
          f"output={_ev['output_tokens']} cached={_ev['cached_tokens']} "
          f"usd=${_ev['usd']:.4f} lean_calls={_ev['lean_calls']} "
          f"lean_s={_ev['lean_s']:.1f} wall_s={_wall:.1f}")

    for pdir, st in _lean_server.all_stats().items():
        name = os.path.basename(pdir)
        print(f"lean server {name}: calls={st['calls']} repl={st['repl_calls']} "
              f"lake={st['lake_calls']} env_hits={st['env_hits']} "
              f"timeouts={st['timeouts']} restarts={st['restarts']}")

    # Lean seconds per layer, prompt size per function, hammer closes per track
    if events.log_path():
        from tools import cost_report
        print("\ncost report")
        cost_report.report(events.log_path())

    if reports:
        best_path = ".lss/runs/best.txt"
        total_proved = sum(r["proved_count"] for r in reports)
        prev_best = 0
        prev_run = "none"
        if os.path.exists(best_path):
            with open(best_path) as f:
                for line in f:
                    if line.startswith("proved:"):
                        try:
                            prev_best = int(line.split(":")[1].strip())
                        except ValueError:
                            pass
                    elif line.startswith("run:"):
                        prev_run = line.split(":", 1)[1].strip()
        if total_proved >= prev_best:
            with open(best_path, "w") as f:
                f.write(f"proved: {total_proved}\nrun: run_{_run_id}\n")
            shutil.copy(_log_path, ".lss/runs/best_run.txt")
            print(f"new best: {total_proved} kernel-proved (previous: {prev_best} from {prev_run})")
        else:
            print(f"below best ({total_proved} vs {prev_best} from {prev_run})")


if __name__ == "__main__":
    main()
