import re
import json
import os
from lean import _parse_forall_vars, _parse_forall_types


def soundness_score(specs):
    total = len(specs)
    if not total:
        return 0.0
    proved = sum(1 for s in specs if s["status"] == "proved")
    return proved / total


def precision_score(kill_rate):
    return float(kill_rate)


def clarity_score(spec_stmt):
    tokens = len(spec_stmt.split())
    quantifiers = len(re.findall(r'\bforall\b|∀|\bexists\b|∃', spec_stmt))
    depth = 0
    max_depth = 0
    for ch in spec_stmt:
        if ch in "([":
            depth += 1
            max_depth = max(max_depth, depth)
        elif ch in ")]":
            depth = max(0, depth - 1)
    score = 1.0 / (1 + tokens / 50 + quantifiers / 3)
    return {"tokens": tokens, "quantifiers": quantifiers, "nesting": max_depth, "score": score}


def impl_independence(spec_stmt, alternative_impls, lean_checker):
    n = len(alternative_impls)
    if not n:
        return {"total_impls": 0, "accepted": 0, "score": 0.0}
    accepted = 0
    for alt_code in alternative_impls:
        code = alt_code.rstrip() + f"\ntheorem _t : {spec_stmt} := sorry"
        ok, _ = lean_checker.typecheck(code)
        if ok:
            accepted += 1
    return {"total_impls": n, "accepted": accepted, "score": accepted / n}


def _alt_outputs(val):
    val = val.strip()
    try:
        n = int(val)
        alts = [str(n + 1)]
        if n > 0:
            alts.append(str(n - 1))
        if n > 1:
            alts.append("0")
        return alts[:3]
    except ValueError:
        pass
    if val.startswith("[") and val.endswith("]"):
        inner = val[1:-1].strip()
        if not inner:
            return ["[0]"]
        parts = [p.strip() for p in inner.split(",")]
        return ["[" + ", ".join(parts[::-1]) + "]", "[]"]
    return []


def uniqueness_score(spec_stmt, func_name, lean_code, test_inputs, lean_checker):
    inputs_tested = 0
    total_alternatives = 0
    alternatives_rejected = 0
    for inp in test_inputs:
        correct = lean_checker.eval_expr(f"{func_name} {inp}", prelude=lean_code)
        if not correct or "error" in correct.lower():
            continue
        alts = _alt_outputs(correct)
        if not alts:
            continue
        inputs_tested += 1
        for alt in alts:
            total_alternatives += 1
            # replace function body with constant wrong output, check if spec still holds
            const = re.sub(r':=.*', lambda m: ':= ' + alt, lean_code, count=1, flags=re.DOTALL)
            r = lean_checker.try_proof(const, spec_stmt)
            if not r.proved:
                alternatives_rejected += 1
    score = alternatives_rejected / total_alternatives if total_alternatives else 1.0
    return {"inputs_tested": inputs_tested, "alternatives_rejected": alternatives_rejected, "score": score}


def admissibility_check(spec_stmt, lean_code, lean_checker, test_inputs=None, func_name=None):
    if func_name:
        func = func_name
    else:
        m = re.search(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code)
        if not m:
            return {"admissible": False, "witness_input": None}
        func = m.group(1)
    inputs_to_try = test_inputs if test_inputs else ["0", "1", "[]", "#[]"]
    for inp in inputs_to_try:
        val = lean_checker.eval_expr(f"{func} {inp}", prelude=lean_code)
        if val and "error" not in val.lower() and "unknown" not in val.lower():
            return {"admissible": True, "witness_input": inp}
    return {"admissible": False, "witness_input": None}


def _normalize_for_compare(stmt):
    s = stmt.strip()
    s = re.sub(r'\s+', ' ', s)
    s = re.sub(r'[()]', '', s)
    s = s.lower()
    return s


def _extract_postcond_properties(body):
    props = []
    depth = 0
    current = []
    for c in body:
        if c in '([':
            depth += 1
            current.append(c)
        elif c in ')]':
            depth = max(0, depth - 1)
            current.append(c)
        elif c == '∧' and depth == 0:
            prop = ''.join(current).strip()
            if prop.startswith('(') and prop.endswith(')'):
                prop = prop[1:-1].strip()
            if prop:
                props.append(prop)
            current = []
        else:
            current.append(c)
    prop = ''.join(current).strip()
    if prop.startswith('(') and prop.endswith(')'):
        prop = prop[1:-1].strip()
    if prop:
        props.append(prop)
    return props


def _idents(stmt):
    return set(re.findall(r"[a-zA-Z_][a-zA-Z0-9_'!?]*", stmt))


def _strip_forall_body(stmt):
    s = stmt.strip()
    m0 = re.match(r'^∀\s*', s)
    if not m0:
        return s
    s = s[m0.end():]
    while s and s[0] == '(':
        depth, end = 0, -1
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end == -1:
            break
        s = s[end + 1:].strip().lstrip(',').strip()
    return s


def _build_entail_stmts(s_stmt, p_stmt):
    """candidate implication statements to typecheck, most direct first."""
    cands = [f"({s_stmt}) → ({p_stmt})"]
    vs = _parse_forall_vars(s_stmt)
    ts = _parse_forall_types(s_stmt)
    if vs and ts and len(vs) == len(ts):
        body_s = _strip_forall_body(s_stmt)
        binders = " ".join(f"({v} : {t})" for v, t in zip(vs, ts))
        cands.append(f"∀ {binders}, ({body_s}) → ({p_stmt})")
    return cands


_MAX_FC_COMPARISONS = 50


def _func_type(lean_code, func_name):
    """derive lean type of func_name as '(a : T) → ... → R'. returns None if unparseable.
    uses the same regex as _parse_signature in synth.py."""
    m = re.search(r'def\s+' + re.escape(func_name) + r'\b(.*?)(?::=|\n\s*\|)', lean_code, re.DOTALL)
    if not m:
        return None
    sig = m.group(1).strip()
    arg_groups = re.findall(r'\(([^)]+)\)', sig)
    params = []
    for group in arg_groups:
        colon = group.find(':')
        if colon == -1:
            continue
        names = group[:colon].split()
        typ = group[colon+1:].strip()
        for n in names:
            if n.strip():
                params.append((n.strip(), typ))
    after = sig[sig.rfind(')')+1:] if arg_groups else sig
    ret_m = re.match(r'\s*:\s*(.*)', after.split(':=')[0])
    ret_type = ret_m.group(1).strip() if ret_m else ""
    if not ret_type:
        return None
    if params:
        return " → ".join(f"({n} : {t})" for n, t in params) + " → " + ret_type
    return ret_type


def _topo_sort_funcs(funcs, raw_types):
    """sort so each function's type-dependencies appear before it."""
    order = []
    remaining = list(funcs)
    for _ in range(len(funcs) + 1):
        if not remaining:
            break
        for fn in list(remaining):
            deps = [f for f in remaining
                    if f != fn and re.search(r'\b' + re.escape(f) + r'\b', raw_types.get(fn, ""))]
            if not deps:
                order.append(fn)
                remaining.remove(fn)
                break
        else:
            order.extend(remaining)
            break
    return order


def _attempt_entailment(lean_code, s_stmt, p_stmt, lean_checker, project_dir=None, nm_cache=None):
    """prove s_stmt → p_stmt with shared user-defined functions abstracted.
    returns 'proved' | 'not_matchable' | 'proof_failed' | 'tc_failed' | 'skipped_ids'.
    nm_cache: dict keyed by abstracted-gt-stmt; when provided, checks antecedent failure
    (Beer et al. 2001) on the abstracted consequent before attempting entailment."""
    if _idents(s_stmt).isdisjoint(_idents(p_stmt)):
        return "skipped_ids"
    user_funcs = set(re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code))
    common_funcs = user_funcs & _idents(s_stmt) & _idents(p_stmt)
    if not common_funcs:
        return "tc_failed"
    raw_types = {}
    for fn in common_funcs:
        t = _func_type(lean_code, fn)
        if t is None:
            return "tc_failed"
        raw_types[fn] = t
    sorted_fns = _topo_sort_funcs(common_funcs, raw_types)
    abs_vars = {fn: f"_af{i}" for i, fn in enumerate(sorted_fns)}

    def do_abstract(s):
        for fn, av in abs_vars.items():
            s = re.sub(r'\b' + re.escape(fn) + r'\b', av, s)
        return s

    abs_types = [f"({abs_vars[fn]} : {do_abstract(raw_types[fn])})" for fn in sorted_fns]
    quant = "∀ " + " ".join(abs_types) + ", "
    s_abs = do_abstract(s_stmt)
    p_abs = do_abstract(p_stmt)

    # antecedent-failure check on abstracted GT (Beer et al. 2001).
    # the abstraction replaces user-defined functions with universally-quantified
    # variables, so the concrete definition cannot be used to prove p_abs.
    # if the abstracted property is still provable for all such functions, every
    # entailment against it is vacuous and no spec can meaningfully match it.
    if nm_cache is not None:
        abs_p_stmt = quant + p_abs
        if abs_p_stmt not in nm_cache:
            ctx2 = lean_code.rstrip() + "\n" if lean_code else ""
            ok2, _ = lean_checker.typecheck(ctx2 + f"theorem _vpc : {abs_p_stmt} := sorry",
                                            project_dir=project_dir)
            if not ok2:
                nm_cache[abs_p_stmt] = False
            else:
                pr0 = lean_checker.try_proof(lean_code, abs_p_stmt, project_dir=project_dir)
                if pr0.proved:
                    nm_cache[abs_p_stmt] = True
                else:
                    pr0h = lean_checker.try_hammer(lean_code, abs_p_stmt, project_dir=project_dir)
                    nm_cache[abs_p_stmt] = pr0h.proved
        if nm_cache[abs_p_stmt]:
            return "not_matchable"

    ctx = lean_code.rstrip() + "\n" if lean_code else ""
    for inner in _build_entail_stmts(s_abs, p_abs):
        impl = quant + inner
        ok, _ = lean_checker.typecheck(ctx + f"theorem _fc : {impl} := sorry",
                                       project_dir=project_dir)
        if not ok:
            continue
        pr = lean_checker.try_proof(lean_code, impl, project_dir=project_dir)
        if pr.proved:
            return "proved"
        pr2 = lean_checker.try_hammer(lean_code, impl, project_dir=project_dir)
        if pr2.proved:
            return "proved"
        return "proof_failed"
    return "tc_failed"


def _build_gt_properties(ground_truth_specs, postcond_defs):
    props = []
    for gt in ground_truth_specs:
        gt_stmt = _gt_prop(gt.strip())
        expanded = False
        if postcond_defs:
            for pc_name, pc_body in postcond_defs.items():
                if pc_name in gt_stmt:
                    props.extend(_extract_postcond_properties(pc_body))
                    expanded = True
                    break
        if not expanded:
            props.append(gt_stmt)
    return props


def _gt_prop(gt_stmt):
    # extract proposition from "theorem name (p: T) ... : prop := ..."
    # find the ':' at paren depth 0 that separates params from proposition
    m = re.match(r'^(?:theorem|lemma)\s+\S+', gt_stmt)
    if not m:
        return gt_stmt.strip()
    pos = m.end()
    depth = 0
    for i in range(pos, len(gt_stmt)):
        c = gt_stmt[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == ':' and depth == 0:
            if gt_stmt[i:i+2] == ':=':
                break
            assign = gt_stmt.find(':=', i + 1)
            end = assign if assign != -1 else len(gt_stmt)
            return gt_stmt[i + 1:end].strip()
    return gt_stmt.strip()


def functional_correctness(generated_specs, ground_truth_specs, lean_checker,
                           postcond_defs=None, lean_code="", project_dir=None,
                           max_comparisons=_MAX_FC_COMPARISONS):
    """how many proved generated specs imply at least one ground truth property (kernel-confirmed)?"""
    if not ground_truth_specs:
        return {"matched": 0, "unmatched": 0, "undetermined": 0,
                "total_proved": len(generated_specs), "score": None}

    gt_props = _build_gt_properties(ground_truth_specs, postcond_defs)
    proved_specs = [s for s in generated_specs if s["status"] == "proved"]

    nm_cache = {}         # abs_p_stmt -> bool; shared across all pairs, one proof per abstracted GT
    not_matchable_gts = set()  # gt_props confirmed not_matchable (de-dup across specs)

    matched = 0
    unmatched = 0
    undetermined = 0
    matches = []
    comparisons_used = 0
    skipped_comparisons = 0

    for gen in proved_specs:
        gen_stmt = gen["stmt"].strip()
        gen_norm = _normalize_for_compare(gen_stmt)

        spec_matched = False
        spec_attempted = False

        for gt_p in gt_props:
            if spec_matched:
                break
            if gt_p in not_matchable_gts:
                continue
            if gen_norm == _normalize_for_compare(gt_p):
                spec_matched = True
                matches.append({"generated": gen["name"], "ground_truth": gt_p[:80], "method": "exact"})
                break
            if comparisons_used >= max_comparisons:
                skipped_comparisons += 1
                continue
            result = _attempt_entailment(lean_code, gen_stmt, gt_p, lean_checker, project_dir,
                                         nm_cache=nm_cache)
            if result == "not_matchable":
                not_matchable_gts.add(gt_p)
                # don't count as attempted: gt_p is uninformative regardless of spec
            elif result in ("skipped_ids", "tc_failed"):
                skipped_comparisons += 1
            elif result == "proved":
                comparisons_used += 1
                spec_matched = True
                spec_attempted = True
                matches.append({"generated": gen["name"], "ground_truth": gt_p[:80], "method": "entailment"})
                break
            else:
                comparisons_used += 1
                spec_attempted = True

        if spec_matched:
            matched += 1
        elif spec_attempted:
            unmatched += 1
        else:
            undetermined += 1

    denom = matched + unmatched
    return {
        "matched": matched,
        "unmatched": unmatched,
        "undetermined": undetermined,
        "not_matchable": len(not_matchable_gts),
        "total_proved": len(proved_specs),
        "score": matched / denom if denom > 0 else None,
        "skipped_comparisons": skipped_comparisons,
        "matches": matches,
    }


def spec_coverage(generated_specs, ground_truth_specs, lean_checker,
                  postcond_defs=None, lean_code="", project_dir=None,
                  max_comparisons=_MAX_FC_COMPARISONS):
    """what fraction of ground truth properties are implied by some proved generated spec (kernel-confirmed)?"""
    if not ground_truth_specs:
        return {"covered": 0, "uncovered": 0, "undetermined": 0,
                "total_ground_truth": 0, "score": None}

    gt_props = _build_gt_properties(ground_truth_specs, postcond_defs)
    proved_specs = [s for s in generated_specs if s["status"] == "proved"]

    nm_cache = {}         # abs_p_stmt -> bool; shared across all pairs, one proof per abstracted GT
    not_matchable_gts = set()

    covered = 0
    uncovered = 0
    undetermined = 0
    covered_list = []
    comparisons_used = 0
    skipped_comparisons = 0

    for gt_p in gt_props:
        gt_norm = _normalize_for_compare(gt_p)

        gt_covered = False
        gt_attempted = False
        gt_not_matchable = False

        for gen in proved_specs:
            if gt_covered or gt_not_matchable:
                break
            gen_stmt = gen["stmt"].strip()
            if gt_norm == _normalize_for_compare(gen_stmt):
                gt_covered = True
                covered_list.append(gt_p[:80])
                break
            if comparisons_used >= max_comparisons:
                skipped_comparisons += 1
                continue
            result = _attempt_entailment(lean_code, gen_stmt, gt_p, lean_checker, project_dir,
                                         nm_cache=nm_cache)
            if result == "not_matchable":
                gt_not_matchable = True
            elif result in ("skipped_ids", "tc_failed"):
                skipped_comparisons += 1
            elif result == "proved":
                comparisons_used += 1
                gt_covered = True
                gt_attempted = True
                covered_list.append(gt_p[:80])
                break
            else:
                comparisons_used += 1
                gt_attempted = True

        if gt_not_matchable:
            not_matchable_gts.add(gt_p)
        elif gt_covered:
            covered += 1
        elif gt_attempted:
            uncovered += 1
        else:
            undetermined += 1

    denom = covered + uncovered
    return {
        "covered": covered,
        "uncovered": uncovered,
        "undetermined": undetermined,
        "not_matchable": len(not_matchable_gts),
        "total_ground_truth": len(gt_props),
        "score": covered / denom if denom > 0 else None,
        "skipped_comparisons": skipped_comparisons,
        "covered_specs": covered_list,
    }


def generate_report(benchmark_name, specs, metrics_dict, timing, llm_calls, lean_calls):
    proved = [s for s in specs if s["status"] == "proved"]
    validated = [s for s in specs if s["status"] == "validated"]
    rejected = [s for s in specs if s["status"] == "rejected"]
    spec_entries = []
    for s in specs:
        c = clarity_score(s["stmt"])
        spec_entries.append({
            "name": s["name"],
            "stmt": s["stmt"],
            "status": s["status"],
            "method": s.get("method", ""),
            "clarity_score": c["score"],
        })
    return {
        "name": benchmark_name,
        "generated_count": len(specs),
        "proved_count": len(proved),
        "validated_count": len(validated),
        "rejected_count": len(rejected),
        "soundness": metrics_dict.get("soundness", 0.0),
        "precision": metrics_dict.get("precision"),
        "avg_clarity": metrics_dict.get("avg_clarity", 0.0),
        "impl_independence": metrics_dict.get("impl_independence"),
        "avg_uniqueness": metrics_dict.get("avg_uniqueness"),
        "admissibility": metrics_dict.get("admissibility"),
        "convergence_iterations": metrics_dict.get("convergence_iterations", 0),
        "llm_calls": llm_calls,
        "lean_calls": lean_calls,
        "elapsed_seconds": timing,
        "specs": spec_entries,
    }


def save_report(report, path):
    d = os.path.dirname(path)
    if d:
        os.makedirs(d, exist_ok=True)
    with open(path, "w") as f:
        json.dump(report, f, indent=2)


def summary_table(reports):
    if not reports:
        return ""
    header = (
        f"{'benchmark':<20} {'proved':>7} {'sound':>6} {'prec':>6}"
        f" {'clarity':>8} {'unique':>7} {'llm':>5} {'lean':>5} {'sec':>6}"
    )
    sep = "-" * len(header)
    rows = [header, sep]
    for r in reports:
        prec = f"{r['precision']:.2f}" if r["precision"] is not None else "    -"
        uniq = f"{r['avg_uniqueness']:.2f}" if r["avg_uniqueness"] is not None else "     -"
        rows.append(
            f"{r['name']:<20} "
            f"{r['proved_count']:>3}/{r['generated_count']:<3} "
            f"{r['soundness']:>6.2f} "
            f"{prec:>6} "
            f"{r['avg_clarity']:>8.3f} "
            f"{uniq:>7} "
            f"{r['llm_calls']:>5} "
            f"{r['lean_calls']:>5} "
            f"{r['elapsed_seconds']:>6.1f}"
        )
    return "\n".join(rows)
