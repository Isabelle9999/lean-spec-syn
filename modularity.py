import re
from metrics import _func_type
from lean import _parse_forall_vars, _parse_forall_types

_MAX_RESTORE = 5
_MAX_OBL = 3  # max pre obligation checks per function


def _abs_var(i):
    return f"_ag{i}"


def _sub(text, name, replacement):
    return re.sub(r'\b' + re.escape(name) + r'\b', replacement, text)


def _sub_stmts(stmts, pairs):
    """apply [(name, replacement), ...] to each stmt."""
    result = []
    for stmt in stmts:
        s = stmt
        for name, repl in pairs:
            s = _sub(s, name, repl)
        result.append(s)
    return result


def _build_f_mabs(func_name, def_text, callee_names, abs_names, callee_types):
    """generate parameterized version of func with callees replaced by abs vars.
    handles both ':=' and pattern-matching ('| ...') styles.
    returns (mabs_name, mabs_code) or (None, None)."""
    last = func_name.split('.')[-1]
    mabs_name = last + '_mabs'
    abs_call = (mabs_name + ' ' + ' '.join(abs_names)) if abs_names else mabs_name

    # find body start: := takes priority over first pipe line
    m_assign = re.search(r':=', def_text)
    m_pipe = re.search(r'\n[ \t]*\|', def_text)

    if m_assign:
        header = def_text[:m_assign.end()]
        body = def_text[m_assign.end():]
    elif m_pipe:
        # pattern-matching style without :=
        header = def_text[:m_pipe.start()]
        body = def_text[m_pipe.start():]
    else:
        return None, None

    new_body = body
    for callee, av in zip(callee_names, abs_names):
        new_body = _sub(new_body, callee, av)
    if re.search(r'\b' + re.escape(last) + r'\b', new_body):
        new_body = _sub(new_body, last, abs_call)

    abs_params = ' '.join(f'({av} : {t})' for av, t in zip(abs_names, callee_types))
    new_header = re.sub(
        r'\bdef\s+' + re.escape(last) + r'\b',
        ('def ' + mabs_name + ' ' + abs_params).rstrip(),
        header, count=1
    )
    if new_header == header:
        return None, None

    return mabs_name, new_header + new_body


def _build_check_stmt(abs_names, callee_types, callee_specs_abs, func_specs_abs):
    """build the ∀-quantified modularity check theorem statement."""
    if not func_specs_abs:
        return None
    conclusion = ' ∧ '.join(f'({s})' for s in func_specs_abs)
    if not abs_names:
        # zero-abstract: just prove the conclusion (all callees restored)
        return conclusion
    binders = ' '.join(f'({av} : {t})' for av, t in zip(abs_names, callee_types))
    if callee_specs_abs:
        hyps = ' → '.join(f'({s})' for s in callee_specs_abs)
        return f'∀ {binders}, {hyps} → {conclusion}'
    return f'∀ {binders}, {conclusion}'


def _ladder_names(abs_names, callee_specs_abs, func_specs_abs):
    """generate fresh intro names: (abs_func_vars, hyp_vars, conclusion_vars)."""
    gf = [f'_gf{i}' for i in range(len(abs_names))]
    hc = [f'_hc{i}' for i in range(len(callee_specs_abs))]
    # conclusion vars: parse leading ∀ from single spec (before _build_check_stmt wraps it)
    vs = []
    if len(func_specs_abs) == 1:
        vs = [f'_v{i}' for i in range(len(_parse_forall_vars(func_specs_abs[0])))]
    return gf, hc, vs


def _mod_tactics(mabs_name, gf, hc, vs):
    """tactic ladder shaped for the modularity check goal form."""
    intro_parts = gf + hc + vs
    simp_h = ', '.join([mabs_name] + hc)
    hyp_only = ', '.join(hc)

    tactics = [f'grind [{mabs_name}]']
    if intro_parts:
        intro = ' '.join(intro_parts)
        tactics += [
            f'intro {intro}; simp [{simp_h}]; omega',
            f'intro {intro}; simp [{simp_h}]; ring',
            f'intro {intro}; simp [{simp_h}]',
        ]
        if hc:
            tactics += [
                f'intro {intro}; unfold {mabs_name}; simp [{hyp_only}]; omega',
                f'intro {intro}; unfold {mabs_name}; simp [{hyp_only}]; aesop',
            ]
    # simp_all fallbacks cover zero-abstract case and miss-cases
    tactics += [
        f'simp_all [{mabs_name}]; omega',
        f'simp_all [{mabs_name}]; ring',
        f'simp_all [{mabs_name}]',
    ]
    return tactics


def _try_prove(lean_code, mabs_code, check_stmt, lean_checker, project_dir,
               mabs_name=None, abs_names=None, callee_specs_abs=None, func_specs_abs=None):
    """try the tactic ladder then fall through to try_proof / try_hammer.
    returns 'proved' | 'undetermined'."""
    full = lean_code.rstrip() + '\n' + mabs_code.rstrip() + '\n'
    ok, _ = lean_checker.typecheck(full + f'theorem _mc : {check_stmt} := sorry\n',
                                   project_dir=project_dir)
    if not ok:
        return 'undetermined'

    # tactic ladder (requires mabs info for intro names and simp set)
    if mabs_name and abs_names is not None and callee_specs_abs is not None and func_specs_abs is not None:
        gf, hc, vs = _ladder_names(abs_names, callee_specs_abs, func_specs_abs)
        for tac in _mod_tactics(mabs_name, gf, hc, vs):
            ok2, _ = lean_checker.typecheck(full + f'theorem _mc : {check_stmt} := by {tac}\n',
                                            project_dir=project_dir)
            if ok2:
                return 'proved'

    pr = lean_checker.try_proof(full, check_stmt, func_name=mabs_name, project_dir=project_dir)
    if pr.proved:
        return 'proved'
    pr2 = lean_checker.try_hammer(full, check_stmt, project_dir=project_dir)
    return 'proved' if pr2.proved else 'undetermined'


def _split_impl(body):
    """find top-level → in body; return (antecedent, consequent) or (None, body)."""
    depth = 0
    for i, c in enumerate(body):
        if c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
        elif c == '→' and depth == 0:
            return body[:i].strip(), body[i + 1:].strip()
    return None, body


def _extract_pre_post(spec_stmt):
    """split spec into (pre, post); pre is None when there is no hypothesis.
    reuses binder parsing from _parse_forall_vars."""
    s = spec_stmt.strip()
    m0 = re.match(r'^∀\s*', s)
    if not m0:
        return None, s
    rest = s[m0.end():]
    while rest.startswith('('):
        depth, end = 0, -1
        for i, c in enumerate(rest):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end == -1:
            return None, spec_stmt
        rest = rest[end + 1:].lstrip(', ')
    return _split_impl(rest)


def _parse_call_args(body, pos):
    """extract argument expressions starting at pos in body.
    returns list of strings or None if unparseable."""
    s = body[pos:]
    args = []
    while True:
        s = s.lstrip(' \t')
        if not s or s[0] in '\n|,;)]\r':
            break
        if re.match(r'^(let|in|match|if|then|else|do|with|fun|have|show|by|where'
                    r'|termination_by|decreasing_by)\b', s):
            break
        if s[:2] in (':=', '--', '/-'):
            break
        if s[0] == '(':
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
                return None
            args.append(s[:end + 1])
            s = s[end + 1:]
        else:
            tok = re.match(r'^[\w.\']+', s)
            if not tok:
                break
            args.append(tok.group(0))
            s = s[tok.end():]
    return args or None


def _extract_call_sites(body, callee_name):
    """return list of arg expression lists for each call to callee_name in body."""
    sites = []
    for m in re.finditer(r'\b' + re.escape(callee_name) + r'\b', body):
        args = _parse_call_args(body, m.end())
        if args is not None:
            sites.append(args)
    return sites


def _prove_obligation(lean_code, obl_stmt, lean_checker, project_dir):
    """try to prove a call-site precondition obligation.
    returns 'discharged' | 'undetermined'."""
    ctx = lean_code.rstrip() + '\n'
    ok, _ = lean_checker.typecheck(ctx + f'theorem _obl : {obl_stmt} := sorry\n',
                                   project_dir=project_dir)
    if not ok:
        return 'undetermined'
    for tac in ('omega', 'simp; omega', 'aesop', 'decide', 'simp_all', 'norm_num', 'ring'):
        ok2, _ = lean_checker.typecheck(ctx + f'theorem _obl : {obl_stmt} := by {tac}\n',
                                        project_dir=project_dir)
        if ok2:
            return 'discharged'
    pr = lean_checker.try_proof(lean_code, obl_stmt, project_dir=project_dir)
    if pr.proved:
        return 'discharged'
    pr2 = lean_checker.try_hammer(lean_code, obl_stmt, project_dir=project_dir)
    return 'discharged' if pr2.proved else 'undetermined'


def _check_pre_obligation(lean_code, f_def_text, g_name, g_spec_stmts, f_spec_stmts,
                          lean_checker, project_dir):
    """check if f discharges g's precondition at each call site.
    returns 'trivial' | 'discharged' | 'undetermined'."""
    g_pre = None
    g_vars = []
    for g_spec in g_spec_stmts:
        gpre, _ = _extract_pre_post(g_spec)
        if gpre is not None:
            g_vars = _parse_forall_vars(g_spec)
            g_pre = gpre
            break
    if g_pre is None:
        return 'trivial'

    f_binders_str = ''
    f_pre = None
    for f_spec in f_spec_stmts:
        fvars = _parse_forall_vars(f_spec)
        ftypes = _parse_forall_types(f_spec)
        if fvars and ftypes and len(fvars) == len(ftypes):
            f_binders_str = ' '.join(f'({v} : {t})' for v, t in zip(fvars, ftypes))
            f_pre, _ = _extract_pre_post(f_spec)
            break

    bm = re.search(r':=(.*)', f_def_text, re.DOTALL)
    if not bm:
        bm = re.search(r'\n[ \t]*\|(.*)', f_def_text, re.DOTALL)
    body = bm.group(1) if bm else f_def_text

    call_sites = _extract_call_sites(body, g_name)
    if not call_sites:
        return 'undetermined'

    for args in call_sites:
        pre_applied = g_pre
        for var, arg in zip(g_vars, args):
            pre_applied = re.sub(r'\b' + re.escape(var) + r'\b', arg, pre_applied)
        if f_binders_str:
            if f_pre:
                obl = f'∀ {f_binders_str}, ({f_pre}) → ({pre_applied})'
            else:
                obl = f'∀ {f_binders_str}, ({pre_applied})'
        else:
            obl = f'({pre_applied})'
        status = _prove_obligation(lean_code, obl, lean_checker, project_dir)
        if status == 'undetermined':
            return 'undetermined'

    return 'discharged'


def _classify_edges(func_name, lean_code, callees, callee_spec_lists, func_spec_stmts,
                    call_graph, lean_checker, project_dir, underspec_callees):
    """three-way classification for each callee edge after a failed modularity check.
    returns list of {'callee', 'classification', 'pre_status'}."""
    results = []
    f_def_text = call_graph.def_text(func_name)
    for i, (callee, specs) in enumerate(zip(callees, callee_spec_lists)):
        if i >= _MAX_OBL:
            break
        if f_def_text:
            pre_status = _check_pre_obligation(
                lean_code, f_def_text, callee, specs, func_spec_stmts,
                lean_checker, project_dir
            )
        else:
            pre_status = 'undetermined'

        pre_ok = pre_status in ('trivial', 'discharged')
        if pre_ok and callee in underspec_callees:
            cls = 'CALLEE_UNDERSPECIFIED'
        elif not pre_ok:
            cls = 'PRECONDITION_UNDISCHARGED'
        else:
            cls = 'UNDETERMINED'

        results.append({'callee': callee, 'classification': cls, 'pre_status': pre_status})
    return results


def check_function_modularity(func_name, lean_code, func_spec_stmts,
                               call_graph, spec_map, lean_checker, project_dir=None):
    """check if func_name's specs are provable from callee specs alone (∀-quantified encoding).

    spec_map: {callee_name: [spec_stmt_str, ...]}
    returns dict with status 'proved' | 'undetermined' | 'skipped' and supporting data."""
    if not func_spec_stmts:
        return {'status': 'skipped', 'reason': 'no specs'}

    callees = call_graph.callees_outside_scc(func_name)
    if not callees:
        return {'status': 'skipped', 'reason': 'no external callees'}

    callees_with_specs = [c for c in callees if spec_map.get(c)]
    if not callees_with_specs:
        return {'status': 'skipped', 'reason': 'no callee specs'}

    abs_names = [_abs_var(i) for i in range(len(callees_with_specs))]
    callee_types = []
    for callee in callees_with_specs:
        t = _func_type(lean_code, callee)
        if t is None:
            return {'status': 'undetermined', 'reason': f'no type for {callee}', 'callees': []}
        callee_types.append(t)

    def_text = call_graph.def_text(func_name)
    if def_text is None:
        return {'status': 'undetermined', 'reason': 'def not found', 'callees': callees_with_specs,
                'abs_names': abs_names, 'callee_types': callee_types}

    mabs_name, mabs_code = _build_f_mabs(func_name, def_text, callees_with_specs, abs_names, callee_types)
    if mabs_code is None:
        return {'status': 'undetermined', 'reason': 'could not build abstract def',
                'callees': callees_with_specs, 'abs_names': abs_names, 'callee_types': callee_types}

    last = func_name.split('.')[-1]
    abs_call = mabs_name + ' ' + ' '.join(abs_names)
    repls = list(zip(callees_with_specs, abs_names)) + [(last, abs_call)]

    callee_specs_abs = []
    for callee, av in zip(callees_with_specs, abs_names):
        for s in spec_map[callee]:
            callee_specs_abs.append(_sub(s, callee, av))

    func_specs_abs = _sub_stmts(func_spec_stmts, repls)
    check_stmt = _build_check_stmt(abs_names, callee_types, callee_specs_abs, func_specs_abs)
    if check_stmt is None:
        return {'status': 'undetermined', 'reason': 'could not build check stmt',
                'callees': callees_with_specs, 'abs_names': abs_names, 'callee_types': callee_types}

    status = _try_prove(lean_code, mabs_code, check_stmt, lean_checker, project_dir,
                        mabs_name=mabs_name, abs_names=abs_names,
                        callee_specs_abs=callee_specs_abs, func_specs_abs=func_specs_abs)
    result = {
        'status': status,
        'callees': callees_with_specs,
        'abs_names': abs_names,
        'callee_types': callee_types,
        'mabs_name': mabs_name,
        'check_stmt': check_stmt,
        'callee_specs_abs': callee_specs_abs,
        'func_specs_abs': func_specs_abs,
    }
    if status == 'undetermined':
        callee_spec_lists = [spec_map[c] for c in callees_with_specs]
        underspec = localize_failure(
            func_name, lean_code, callees_with_specs, abs_names, callee_types,
            callee_spec_lists, func_spec_stmts, call_graph, lean_checker, project_dir
        )
        edge_cls = _classify_edges(
            func_name, lean_code, callees_with_specs, callee_spec_lists, func_spec_stmts,
            call_graph, lean_checker, project_dir, underspec
        )
        result['localization'] = underspec
        result['edge_classifications'] = edge_cls
    return result


def localize_failure(func_name, lean_code, callees, abs_names, callee_types,
                     callee_spec_lists, func_spec_stmts, call_graph,
                     lean_checker, project_dir=None, max_restore=_MAX_RESTORE):
    """restore callees cumulatively until the abstract proof passes.

    callees, abs_names, callee_types, callee_spec_lists are parallel lists (same order).
    returns list of callee names restored when proof succeeded, or [] if cap reached/failed."""
    n = len(callees)

    for k in range(1, min(n, max_restore) + 1):
        abstract_callees = callees[k:]
        abstract_abs = abs_names[k:]
        abstract_types = callee_types[k:]
        abstract_specs = callee_spec_lists[k:]

        def_text = call_graph.def_text(func_name)
        if not def_text:
            if not abstract_callees:
                break
            continue

        mabs_name, mabs_code = _build_f_mabs(
            func_name, def_text, abstract_callees, abstract_abs, abstract_types
        )
        if not mabs_code:
            if not abstract_callees:
                break
            continue

        callee_specs_abs = []
        for callee, av, specs in zip(abstract_callees, abstract_abs, abstract_specs):
            for s in specs:
                callee_specs_abs.append(_sub(s, callee, av))

        last = func_name.split('.')[-1]
        abs_call = (mabs_name + ' ' + ' '.join(abstract_abs)) if abstract_abs else mabs_name
        repls = list(zip(abstract_callees, abstract_abs)) + [(last, abs_call)]
        func_specs_abs_loc = _sub_stmts(func_spec_stmts, repls)

        check_stmt = _build_check_stmt(abstract_abs, abstract_types, callee_specs_abs, func_specs_abs_loc)
        if not check_stmt:
            if not abstract_callees:
                break
            continue

        status = _try_prove(lean_code, mabs_code, check_stmt, lean_checker, project_dir,
                            mabs_name=mabs_name, abs_names=abstract_abs,
                            callee_specs_abs=callee_specs_abs,
                            func_specs_abs=func_specs_abs_loc)
        if status == 'proved':
            return callees[:k]

        if not abstract_callees:
            break

    return []


def check_project_modularity(func_spec_map, lean_code, call_graph, lean_checker, project_dir=None):
    """run modularity check for all functions in func_spec_map that have external callees.

    func_spec_map: {func_name: [spec_stmt_str, ...]}
    returns report dict:
      contract_discharged: [(caller, callee), ...]
      undetermined: [(caller, callee), ...]
      underspecified_pairs: [(caller, callee), ...]  -- from localization
      modular: bool
      per_func: {func_name: result_dict}  -- extended with obligation_results, edge_classifications
    """
    contract_discharged = []
    undetermined_pairs = []
    underspecified_pairs = []
    per_func = {}

    for func_name, func_spec_stmts in func_spec_map.items():
        callees = call_graph.callees_outside_scc(func_name)
        spec_map = {c: func_spec_map.get(c, []) for c in callees}
        callees_with_specs = [c for c in callees if spec_map.get(c)]

        if not callees_with_specs:
            per_func[func_name] = {'status': 'skipped', 'reason': 'no callee specs'}
            continue

        result = check_function_modularity(
            func_name, lean_code, func_spec_stmts,
            call_graph, spec_map, lean_checker, project_dir
        )
        per_func[func_name] = result

        f_def_text = call_graph.def_text(func_name)
        obl_results = {}

        if result['status'] == 'proved':
            for callee in result.get('callees', []):
                callee_specs = func_spec_map.get(callee, [])
                if f_def_text:
                    pre_status = _check_pre_obligation(
                        lean_code, f_def_text, callee, callee_specs, func_spec_stmts,
                        lean_checker, project_dir
                    )
                else:
                    pre_status = 'undetermined'
                obl_results[callee] = pre_status
                # contract-discharged only when both abstract proof and pre obligation hold
                if pre_status in ('trivial', 'discharged'):
                    contract_discharged.append((func_name, callee))

        elif result['status'] == 'undetermined':
            for callee in result.get('callees', callees_with_specs):
                undetermined_pairs.append((func_name, callee))

            rc = result.get('callees', [])
            if rc and result.get('abs_names'):
                callee_spec_lists = [func_spec_map.get(c, []) for c in rc]
                underspec = localize_failure(
                    func_name, lean_code,
                    rc, result['abs_names'], result['callee_types'],
                    callee_spec_lists, func_spec_stmts,
                    call_graph, lean_checker, project_dir
                )
                for c in underspec:
                    underspecified_pairs.append((func_name, c))

                edge_cls = _classify_edges(
                    func_name, lean_code, rc, callee_spec_lists, func_spec_stmts,
                    call_graph, lean_checker, project_dir, underspec
                )
                result['edge_classifications'] = edge_cls
                for ecl in edge_cls:
                    obl_results[ecl['callee']] = ecl['pre_status']

        result['obligation_results'] = obl_results

    all_pairs = [(f, c) for f, r in per_func.items()
                 for c in r.get('callees', []) if r.get('status') != 'skipped']
    modular = bool(all_pairs) and len(contract_discharged) == len(all_pairs)

    return {
        'contract_discharged': contract_discharged,
        'undetermined': undetermined_pairs,
        'underspecified_pairs': underspecified_pairs,
        'modular': modular,
        'per_func': per_func,
    }
