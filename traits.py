import re


def detect_trait_structs(lean_code):
    """return {trait_name: [method_names]} for Aeneas-translated trait structures."""
    result = {}
    pat = re.compile(
        r'\bstructure\s+([\w.\']+)\s*\([^)]*\)\s+where\b([\s\S]*?)(?=\n\S|\Z)'
    )
    field_re = re.compile(r'^\s+([\w.\']+)\s*:', re.MULTILINE)
    for m in pat.finditer(lean_code):
        name = m.group(1)
        body = m.group(2)
        methods = [f.group(1) for f in field_re.finditer(body)]
        if methods:
            result[name] = methods
    return result


def detect_trait_impls(lean_code):
    """return list of {impl_name, trait_name, methods: {field: func_name}}."""
    results = []
    impl_re = re.compile(
        r'@\[reducible\]\s*\ndef\s+([\w.\']+)(?:\s+[^:=\n]*)?\s*:\s*([\w.\']+)(?:\s+[^=\n]+)?\s*:=\s*\{([^}]*)\}',
        re.DOTALL
    )
    assign_re = re.compile(r'([\w.\']+)\s*:=\s*([\w.\']+)')
    for m in impl_re.finditer(lean_code):
        impl_name = m.group(1)
        trait_name = m.group(2)
        body = m.group(3)
        methods = {a.group(1): a.group(2) for a in assign_re.finditer(body)}
        if methods:
            results.append({
                'impl_name': impl_name,
                'trait_name': trait_name,
                'methods': methods,
            })
    return results


def _sub(text, old, new):
    return re.sub(r'\b' + re.escape(old) + r'\b', new, text)


def _try_prove_stmt(lean_code, stmt, lean_checker, project_dir):
    """returns 'satisfied'|'violated'|'undetermined'."""
    ctx = lean_code.rstrip() + '\n'
    ok, _ = lean_checker.typecheck(ctx + f'theorem _tc : {stmt} := sorry\n',
                                   project_dir=project_dir)
    if not ok:
        return 'undetermined'
    pr = lean_checker.try_proof(lean_code, stmt, project_dir=project_dir)
    if pr.proved:
        return 'satisfied'
    pr2 = lean_checker.try_hammer(lean_code, stmt, project_dir=project_dir)
    if pr2.proved:
        return 'satisfied'
    for tac in ('rfl', 'simp_all', 'omega', 'aesop', 'decide'):
        ok2, _ = lean_checker.typecheck(ctx + f'theorem _tc : {stmt} := by {tac}\n',
                                        project_dir=project_dir)
        if ok2:
            return 'satisfied'
    neg = f'¬ ({stmt})'
    ok_n, _ = lean_checker.typecheck(ctx + f'theorem _neg : {neg} := sorry\n',
                                     project_dir=project_dir)
    if ok_n:
        for tac in ('decide', 'simp_all', 'omega', 'aesop'):
            ok_n2, _ = lean_checker.typecheck(ctx + f'theorem _neg : {neg} := by {tac}\n',
                                              project_dir=project_dir)
            if ok_n2:
                return 'violated'
    return 'undetermined'


def check_trait_obligations(func_spec_map, lean_code, lean_checker, project_dir=None):
    """for each proved impl method spec, check every other impl of the same trait method.

    returns {trait_found, traits_detected, impls_detected, per_edge, violated}
    per_edge: [(trait_name, impl_name, method, status)]
    violated: [(trait_name, impl_name, method)]
    """
    traits = detect_trait_structs(lean_code)
    impls = detect_trait_impls(lean_code)

    if not traits and not impls:
        return {
            'trait_found': False,
            'traits_detected': [],
            'impls_detected': [],
            'per_edge': [],
            'violated': [],
        }

    impls_by_trait = {}
    for imp in impls:
        impls_by_trait.setdefault(imp['trait_name'], []).append(imp)

    per_edge, violated = [], []

    for trait_name, method_names in traits.items():
        trait_impls = impls_by_trait.get(trait_name, [])
        if len(trait_impls) < 2:
            continue

        for method in method_names:
            sources = []
            for imp in trait_impls:
                func = imp['methods'].get(method)
                if func and func_spec_map.get(func):
                    sources.append((imp['impl_name'], func, func_spec_map[func]))
            if not sources:
                continue

            for src_impl, src_func, src_specs in sources:
                for tgt in trait_impls:
                    if tgt['impl_name'] == src_impl:
                        continue
                    tgt_func = tgt['methods'].get(method)
                    if not tgt_func:
                        continue
                    for spec in src_specs:
                        obl = _sub(spec, src_func, tgt_func)
                        if obl == spec:
                            continue
                        status = _try_prove_stmt(lean_code, obl, lean_checker, project_dir)
                        per_edge.append((trait_name, tgt['impl_name'], method, status))
                        if status == 'violated':
                            violated.append((trait_name, tgt['impl_name'], method))
                        break

    return {
        'trait_found': bool(traits or impls),
        'traits_detected': list(traits),
        'impls_detected': [{'impl_name': i['impl_name'], 'trait_name': i['trait_name']}
                           for i in impls],
        'per_edge': per_edge,
        'violated': violated,
    }
