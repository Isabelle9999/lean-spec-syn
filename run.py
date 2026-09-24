import sys; import os; sys.stdout.reconfigure(encoding="utf-8")
os.makedirs(".lss/runs", exist_ok=True)
_existing = [f for f in os.listdir(".lss/runs") if f.startswith("run_")]
_run_id = len(_existing) + 1
_log_path = f".lss/runs/run_{_run_id}.txt"
_log_file = open(_log_path, "w", encoding="utf-8")
import builtins
_orig_print = builtins.print
def _tee_print(*args, **kwargs):
    _orig_print(*args, **kwargs)
    kwargs["file"] = _log_file
    _orig_print(*args, **kwargs)
    _log_file.flush()
builtins.print = _tee_print
print = _tee_print

import argparse
import json
import time
import shutil
import threading
import lss_config as _lss_config

from lean import LeanChecker, ExampleStore, Cache, get_lean_calls
from synth import LLMClient, synthesize, refine, _func_name, get_llm_calls
from benchmarks import BENCHMARKS, evaluate
from metrics import (
    soundness_score, precision_score, clarity_score,
    uniqueness_score, admissibility_check,
    functional_correctness, spec_coverage,
    generate_report, save_report, summary_table,
)
from incremental import (
    lean_version, load_hashes, save_hashes,
    compute_current_hashes, affected_benches,
    load_cached_specs, save_cached_specs,
)
from traits import check_trait_obligations
from divergence import detect_divergent, mark_divergent_specs


def _naive_run(bm, llm, checker):
    specs = llm.generate_specs(bm["lean_code"], bm.get("templates", []))
    for spec in specs:
        code = bm["lean_code"] + f"\ntheorem {spec['name']} : {spec['stmt']} := sorry"
        ok, _ = checker.typecheck(code)
        spec["status"] = "validated" if ok else "rejected"
    return specs


def _metrics(specs, bm, kill_rate, checker, quick=False, verbose=False):
    proved = [s for s in specs if s["status"] in ("proved", "validated")]
    sound = soundness_score(specs)
    prec = precision_score(kill_rate) if kill_rate is not None else None
    avg_clarity = (
        sum(clarity_score(s["stmt"])["score"] for s in proved) / len(proved)
        if proved else 0.0
    )
    avg_uniq = None
    if not quick and proved:
        fn = bm.get("func_name") or _func_name(bm["lean_code"])
        ti = bm.get("test_inputs", [])
        if verbose:
            print(f"  [debug] uniqueness inputs: {len(ti)} test inputs")
        if fn and ti:
            uniqs = [
                uniqueness_score(s["stmt"], fn, bm["lean_code"], ti, checker)["score"]
                for s in proved
            ]
            avg_uniq = sum(uniqs) / len(uniqs)
    adm = (
        admissibility_check(proved[0]["stmt"], bm["lean_code"], checker,
                            test_inputs=bm.get("test_inputs"), func_name=bm.get("func_name"))
        if proved else None
    )
    return {
        "soundness": sound,
        "precision": prec,
        "avg_clarity": avg_clarity,
        "impl_independence": None,
        "avg_uniqueness": avg_uniq,
        "admissibility": adm,
        "convergence_iterations": 0,
    }


def _with_timeout(fn, timeout):
    result = [None]
    exc = [None]
    done = threading.Event()

    def worker():
        try:
            result[0] = fn()
        except Exception as e:
            exc[0] = e
        finally:
            done.set()

    t = threading.Thread(target=worker, daemon=True)
    t.start()

    finished = done.wait(timeout=timeout)

    if not finished:
        return None, True

    if exc[0] is not None:
        raise exc[0]

    return result[0], False


def run_bench(bm, args, llm, checker, store, baseline="none", project_dir=None, func_source=None):
    fn = bm.get("func_name") or _func_name(bm["lean_code"])
    ti = bm.get("test_inputs", [])
    tpl = bm.get("templates", [])
    bm_eval = {**bm, "func_name": fn}

    t0 = time.time()
    get_lean_calls()  # reset counter
    get_llm_calls()   # reset counter

    vb = args.verbose
    debug_dir = None
    if getattr(args, "debug", False):
        debug_dir = os.path.join(".lss", "debug", bm["name"])
        os.makedirs(debug_dir, exist_ok=True)

    def _synth():
        if baseline == "naive":
            return _naive_run(bm, llm, checker)
        postcond_defs = bm.get("postcond_defs", {})
        lean_code = bm["lean_code"] + bm.get("lean_preamble", "")
        s = synthesize(lean_code, ti, tpl, llm, checker, store, func_name=fn, verbose=vb, debug_dir=debug_dir, postcond_defs=postcond_defs, project_dir=project_dir, func_source=func_source)
        if baseline == "no-mutation":
            return s
        if not args.quick:
            max_tier = 1 if baseline == "no-adversarial" else 3
            s = refine(s, bm["lean_code"], fn, ti, checker, llm, store, max_tier=max_tier, verbose=vb, project_dir=project_dir, func_source=func_source)
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

    eval_checker = None if baseline in ("naive", "no-mutation") or args.quick else checker
    score = evaluate(specs, bm_eval, lean_checker=eval_checker, project_dir=project_dir)

    md = _metrics(specs, bm, score["kill_rate"], checker, quick=args.quick, verbose=vb)
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

    report = generate_report(bm["name"], specs, md, elapsed, llm_calls_count, lean_calls_count)
    report["functional_correctness"] = fc
    report["spec_coverage"] = sc
    os.makedirs(".lss/reports", exist_ok=True)
    save_report(report, f".lss/reports/{bm['name']}.json")

    kernel_proved = sum(1 for s in specs if s["status"] == "proved")
    validated = sum(1 for s in specs if s["status"] == "validated")
    rejected = sum(1 for s in specs if s["status"] == "rejected")
    total_survived = kernel_proved + validated
    survived = [s for s in specs if s["status"] in ("proved", "validated")]
    label = bm["name"] + (f" ({baseline})" if baseline != "none" else "")
    print(f"\n--- {label} ---")
    print(f"  generated:  {len(specs)}")
    print(f"  survived:   {total_survived} ({kernel_proved} kernel-proved, {validated} validated)")
    if rejected:
        print(f"  rejected:   {rejected}")
        g1 = sum(1 for s in specs if s.get("fail_gate") == "g1")
        g2 = sum(1 for s in specs if s.get("fail_gate") == "g2")
        g3 = sum(1 for s in specs if s.get("fail_gate") == "g3")
        print(f"  failure breakdown: {g1} typecheck, {g2} eval, {g3} vacuity")
    print(f"  soundness:  {md['soundness']:.2f}")
    print(f"  recall:     {score['recall']:.2f}")
    p = md["precision"]
    print(f"  precision:  {p:.2f}" if p is not None else "  precision:  -")
    mc = score.get("mutation_counts")
    if mc:
        total_m = sum(mc.values())
        scored_m = mc["KILLED"] + mc["SURVIVED"]
        print(f"  mutants:    {total_m} total, {mc['KILLED']} killed, {mc['SURVIVED']} survived, "
              f"{mc['EQUIVALENT']} equiv, {mc['INCONCLUSIVE']} inconclusive, {mc['STILLBORN']} stillborn"
              + (f" (score {mc['KILLED']}/{scored_m})" if scored_m else " (score unavailable)"))
    print(f"  clarity:    {md['avg_clarity']:.3f}")
    u = md["avg_uniqueness"]
    print(f"  uniqueness: {u:.2f}" if u is not None else "  uniqueness: -")
    adm = md["admissibility"]
    if adm is not None:
        print(f"  admissible: {adm['admissible']}")
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
    for s in survived:
        tag = f" [{s['method']}]" if s.get("method") else ""
        display = "kernel-proved" if s["status"] == "proved" else "validated (unproved)"
        print(f"    {display:20}{tag}  {s['name']}: {s['stmt'][:80]}")

    pc_data = [s["post_completeness"] for s in survived if s.get("post_completeness")]
    if pc_data:
        valid_pc = [d["post_completeness"] for d in pc_data if d["post_completeness"] is not None]
        if valid_pc:
            avg_pc = sum(valid_pc) / len(valid_pc)
            print(f"  post_completeness: {avg_pc:.2f} avg over {len(valid_pc)} specs")

    if divergent:
        print(f"  divergent defs: {', '.join(sorted(divergent))}")
        n_blocked = sum(1 for s in specs if s.get('blocked_by_divergence'))
        if n_blocked:
            print(f"  blocked by divergence: {n_blocked} specs")
    else:
        print("  divergent: none detected")

    _fn = bm.get("func_name") or _func_name(bm["lean_code"])
    _proved = [s for s in (specs or []) if s.get('status') in ('proved', 'validated')]
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
    keys = ["soundness", "precision", "avg_clarity", "avg_uniqueness"]
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
    p = argparse.ArgumentParser()
    p.add_argument("--quick", action="store_true")
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--debug", action="store_true")
    p.add_argument("--bench", nargs="+", default=None, help="one or more benchmark names")
    p.add_argument("--baseline", choices=["none", "naive", "no-mutation", "no-adversarial"],
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

    cache = Cache()
    llm = LLMClient()
    checker = LeanChecker(cache=cache, project_dir=lean_project_dir)
    store = ExampleStore()

    if args.rust_project:
        from loader import load_rust_project
        benches = load_rust_project(args.rust_project)
        run_dir = rust_project_dir
        print(f"loaded {len(benches)} rust functions from {args.rust_project}")
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
    if args.ablation:
        baselines = ["none", "naive", "no-mutation", "no-adversarial"]
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
                if report is not None:
                    reports.append(report)
            except Exception as e:
                print(f"  CRASH on {bm['name']}: {e}")
                import traceback
                traceback.print_exc()
                continue

    print(f"\nincremental: {n_reverified} re-verified, {n_carried} carried forward")
    save_hashes(curr_hashes)

    if len(reports) > 1:
        print("\n" + summary_table(reports))

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
