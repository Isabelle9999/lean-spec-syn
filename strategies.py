import os
import re
import callgraph
from lean import LeanChecker, _errors, run_in_project
import events


_SPEC_RE = re.compile(
    r"theorem\s+([a-zA-Z_][a-zA-Z0-9_'!?]*)\s*(?:\([^)]*\)\s*)*:\s*([\s\S]*?)\s*:=\s*(?:sorry|by)\b"
)


def _parse_specs(text):
    m = re.search(r'```\w*\s*([\s\S]*?)```', text)
    block = m.group(1) if m else text
    specs = []
    for m2 in _SPEC_RE.finditer(block):
        specs.append({"name": m2.group(1), "stmt": m2.group(2).strip(), "status": "pending", "method": ""})
    return specs


def _wrong_outputs(val):
    val = val.strip()
    try:
        n = int(val)
        seen = set()
        result = []
        for a in [n + 1, n - 1, 0, n * 2]:
            s = str(a)
            if a >= 0 and s != val and s not in seen:
                seen.add(s)
                result.append(s)
        return result[:4]
    except ValueError:
        pass
    if val == "true":
        return ["false"]
    if val == "false":
        return ["true"]
    if val == "none":
        return ["some 0", "some 1"]
    if val.startswith("some "):
        return ["none"]
    if val.startswith("[") and val.endswith("]"):
        inner = val[1:-1].strip()
        if not inner:
            return ["[0]", "[1, 2]"]
        parts = [p.strip() for p in inner.split(",")]
        alts = ["[]"]
        rev = "[" + ", ".join(reversed(parts)) + "]"
        if rev != val:
            alts.append(rev)
        if len(parts) > 1:
            alts.append("[" + parts[0] + "]")
        return alts[:4]
    return []


def generate_from_examples(lean_code, func_name, test_inputs, lean_checker, llm):
    with events.context(stage="gen_examples"):
        pairs = []
        for inp in test_inputs:
            out = lean_checker.eval_expr(f"{func_name} {inp}", prelude=lean_code)
            if out and "error" not in out.lower():
                pairs.append((inp, out))
        if not pairs:
            return []
        obs = "\n".join(f"{func_name} {inp} = {out}" for inp, out in pairs)
        prompt = (
            f"here are observed input-output behaviors of a lean 4 function:\n{obs}\n\n"
            "what mathematical pattern do these suggest? write 2-4 theorem statements capturing the pattern.\n"
            "format: theorem name : statement := sorry\n"
            "return only a ```lean block."
        )
        return _parse_specs(llm._ask(prompt))


def generate_from_negatives(lean_code, func_name, test_inputs, lean_checker, llm):
    with events.context(stage="gen_negatives"):
        neg_pairs = []
        for inp in test_inputs:
            correct = lean_checker.eval_expr(f"{func_name} {inp}", prelude=lean_code)
            if not correct or "error" in correct.lower():
                continue
            for wrong in _wrong_outputs(correct):
                neg_pairs.append((inp, wrong))
        if not neg_pairs:
            return []
        lines = "\n".join(f"{func_name} {inp} ≠ {wrong}" for inp, wrong in neg_pairs)
        prompt = (
            f"this lean 4 function must never produce these outputs:\n{lines}\n\n"
            "write 2-3 theorem statements that a correct specification would have, "
            "which would reject all these wrong behaviors.\n"
            "format: theorem name : statement := sorry\n"
            "return only a ```lean block."
        )
        return _parse_specs(llm._ask(prompt))


def generate_with_proof(lean_code, func_name, llm, lean_checker, project_dir=None):
    with events.context(stage="gen_with_proof"):
        prompt = (
            f"here is a lean 4 function:\n{lean_code}\n\n"
            "write 5-8 theorems about this function, each WITH a complete proof.\n"
            "every theorem must typecheck with zero sorry.\n\n"
            "rules:\n"
            "- do NOT use Mathlib imports\n"
            "- do NOT reference List.Sorted, List.Perm, Multiset, or any external definition\n"
            "- if you need a helper predicate, define it before using it\n"
            "- each theorem must have a COMPLETE proof (no sorry)\n"
            "- use forall quantifiers in theorem statements, not explicit arguments\n"
            f"- prefer short proofs using simp [{func_name}], omega, induction, cases\n"
            f"- the function name is '{func_name}'\n\n"
            "format:\n"
            "```lean\n"
            "-- any helper definitions here\n\n"
            "theorem name1 : statement := by\n"
            "  proof tactics\n\n"
            "theorem name2 : statement := by\n"
            "  proof tactics\n"
            "```"
        )
        text = llm._ask(prompt)
        m = re.search(r'```\w*\s*([\s\S]*?)```', text)
        if not m:
            return []
        block = m.group(1)

        thm_starts = [mo.start() for mo in re.finditer(r'^theorem\s', block, re.MULTILINE)]
        if not thm_starts:
            return []

        helpers = block[:thm_starts[0]].strip()
        results = []
        for i, start in enumerate(thm_starts):
            end = thm_starts[i + 1] if i + 1 < len(thm_starts) else len(block)
            chunk = block[start:end].strip()
            m2 = re.match(
                r'theorem\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)\s*(?:\([^)]*\)\s*)*:\s*([\s\S]*?)\s*:=\s*by\b([\s\S]*)',
                chunk
            )
            if not m2:
                continue
            name = m2.group(1)
            stmt = m2.group(2).strip()
            proof = m2.group(3).strip()
            # don't duplicate if LLM already included the function definition
            if helpers and re.search(r'\bdef\s+' + re.escape(func_name) + r'\b', helpers):
                env = helpers.rstrip()
            else:
                env = lean_code.rstrip() + ("\n" + helpers.rstrip() if helpers else "")
            full = env + "\n" + chunk
            stdout, stderr, rc = run_in_project(full, project_dir=project_dir)
            combined = stdout + stderr
            if rc == 0 and not _errors(combined) and "sorry" not in combined:
                results.append({
                    "name": name,
                    "stmt": stmt,
                    "status": "proved",
                    "method": "llm-gen-with-proof",
                    "proof": proof,
                })
        return results


def generate_from_slices(lean_code, func_name, llm, lean_checker, verbose=False, project_dir=None, func_source=None):
    """SLD-Spec-style program slicing: spec helpers bottom-up, then per-arm cases."""
    with events.context(stage="gen_slices"):
        code = func_source or lean_code
        specs = []
        proved_helper_specs = []

        # use call graph for topo-ordered helper discovery: the project graph
        # when project_dir has a manifest, else build from the inline code
        has_manifest = project_dir and (
            os.path.exists(os.path.join(project_dir, "rust-spec-synthesis.json"))
            or os.path.exists(os.path.join(project_dir, "translation.json")))
        cg = callgraph.for_project(project_dir) if has_manifest else callgraph.build_call_graph(code)
        topo = cg.topo_sorted_names()
        trans_callees = cg.transitive_callees(func_name)

        all_defs = list(re.finditer(
            r'((?:@\[.*?\]\s*)?def\s+(\S+)\s+.*?:=[\s\S]*?)(?=\n(?:@\[|def\s|end\s|#)|\Z)', code))
        def_texts = {m.group(2): m.group(1).strip() for m in all_defs}
        main_m = next((m for m in all_defs if m.group(2) == func_name), None)

        # helpers in topo order (callees before callers), filtered to transitive callees of func_name
        helpers = [
            (n, def_texts[n]) for n in topo
            if n != func_name and n in trans_callees
            and n in def_texts
            and '_precond' not in n and '_postcond' not in n
        ]
        main_def = main_m

        for helper_name, helper_code in helpers:
            if verbose:
                print(f"  [slice] generating specs for helper: {helper_name}")
            prompt = (
                f"This is a helper function used by {func_name}:\n"
                f"```lean\n{helper_code}\n```\n\n"
                f"Write 2-3 theorems about what {helper_name} guarantees.\n"
                f"Focus on: what it returns, how output relates to input, edge cases.\n"
                f"Format: theorem name : ∀ (args), statement := sorry\n"
                f"Return only a ```lean code block."
            )
            resp = llm._ask(prompt)
            if resp:
                for m2 in re.finditer(
                    r'theorem\s+(\w+)\s*:\s*([\s\S]*?)\s*:=\s*(?:by\s+[\s\S]*?(?=\ntheorem|\n```|\Z)|sorry)',
                    resp):
                    specs.append({
                        "name": m2.group(1),
                        "stmt": m2.group(2).strip(),
                        "status": "pending",
                        "method": None,
                        "preamble": "",
                    })
                    proved_helper_specs.append(f"  {m2.group(2).strip()[:100]}")

        if verbose and helpers:
            print(f"  [slice] {len(helpers)} helpers produced {len(specs)} specs")

        if main_def and helpers:
            helper_context = ""
            if proved_helper_specs:
                helper_context = (
                    "\nProved properties of helper functions (you can reference these):\n"
                    + "\n".join(proved_helper_specs[:10]) + "\n\n"
                )
            prompt = (
                f"Main function that calls helpers:\n"
                f"```lean\n{main_def.group(1)}\n```\n\n"
                f"{helper_context}"
                f"Write 5 theorems about {func_name} using the helper properties above.\n"
                f"Focus on: end-to-end behavior, composition of helper guarantees.\n"
                f"Format: theorem name : ∀ (args), statement := sorry\n"
                f"Return only a ```lean code block."
            )
            resp = llm._ask(prompt)
            if resp:
                for m2 in re.finditer(
                    r'theorem\s+(\w+)\s*:\s*([\s\S]*?)\s*:=\s*(?:by\s+[\s\S]*?(?=\ntheorem|\n```|\Z)|sorry)',
                    resp):
                    specs.append({
                        "name": m2.group(1),
                        "stmt": m2.group(2).strip(),
                        "status": "pending",
                        "method": None,
                        "preamble": "",
                    })
            if verbose:
                print(f"  [slice] main with helper context: {len(specs)} total specs")

        if main_def:
            body = main_def.group(1)
            arms = re.findall(r'\|\s*([^\n]*(?:\n(?!\s*\|)[^\n]*)*)', body)
            if len(arms) >= 2:
                for i, arm in enumerate(arms[:5]):
                    arm = arm.strip()
                    if not arm:
                        continue
                    if verbose:
                        print(f"  [slice] generating specs for arm {i+1}: {arm[:50]}")
                    prompt = (
                        f"Full function:\n```lean\n{code}\n```\n\n"
                        f"Focus ONLY on this specific pattern match case:\n"
                        f"  | {arm}\n\n"
                        f"Write 1-2 theorems about what happens when the input matches this case.\n"
                        f"The theorem should have a hypothesis that constrains the input to this case.\n"
                        f"Format: theorem name : ∀ (args), statement := sorry\n"
                        f"Return only a ```lean code block."
                    )
                    resp = llm._ask(prompt)
                    if resp:
                        for m2 in re.finditer(
                            r'theorem\s+(\w+)\s*:\s*([\s\S]*?)\s*:=\s*(?:by\s+[\s\S]*?(?=\ntheorem|\n```|\Z)|sorry)',
                            resp):
                            specs.append({
                                "name": m2.group(1),
                                "stmt": m2.group(2).strip(),
                                "status": "pending",
                                "method": None,
                                "preamble": "",
                            })
                if verbose:
                    print(f"  [slice] case-specific: {len(specs)} total specs")

        if verbose:
            print(f"  [slice] total from slicing: {len(specs)} specs")

        return specs


def generate_failure_freedom(lean_code, func_name, llm, lean_checker,
                              verbose=False, project_dir=None, func_source=None):
    """wp-style: scan body for arithmetic overflow, indexing, and div-by-zero sites;
    conjoin per-site guards into P; emit ∀ args, P → ∃ r, def args = ok r.
    processes each definition in the function family separately so aeneas-lifted
    loop parameters are resolved from each definition's own signature.
    precondition satisfiability check filters vacuously-true implications.
    """
    with events.context(stage="gen_failure_freedom"):
        import os
        import glob as _gl
        from lean import (_find_def_in_text, _witnesses_for_type, _diverse_tuples,
                          _parse_struct_defs, run_in_project, _errors)

        UNSIGNED_BARE = {"U8", "U16", "U32", "U64", "U128", "Usize"}
        SIGNED_BARE   = {"I8", "I16", "I32", "I64", "I128", "Isize"}
        SUFFIX_TO_TYPE = {
            "usize": "Usize", "u8": "U8", "u16": "U16", "u32": "U32",
            "u64": "U64", "u128": "U128", "isize": "Isize", "i8": "I8",
            "i16": "I16", "i32": "I32", "i64": "I64", "i128": "I128",
        }

        # locate function definition (same resolution order as generate_mutants)
        fn_def = None
        fn_src_text = None
        for src in [lean_code, func_source]:
            if not src:
                continue
            fn_def, _ = _find_def_in_text(src, func_name)
            if fn_def:
                fn_src_text = src
                break
        if fn_def is None and project_dir and os.path.isdir(project_dir):
            for path in sorted(_gl.glob(
                    os.path.join(project_dir, "**", "*.lean"), recursive=True)):
                if ".lake" in path.replace("\\", "/"):
                    continue
                try:
                    text = open(path, encoding="utf-8").read()
                except (OSError, UnicodeDecodeError):
                    continue
                fn_def, _ = _find_def_in_text(text, func_name)
                if fn_def:
                    fn_src_text = text
                    break
        if fn_def is None:
            if verbose:
                print(f"  [ff] cannot locate body for {func_name!r}")
            return []

        # only process Result-returning function families
        if "Result" not in fn_def:
            return []

        # collect the function family: top-level + all defs extending func_name with "_"
        defs_to_scan = [(func_name, fn_def)]
        if fn_src_text:
            fam_pat = re.compile(r'def\s+(' + re.escape(func_name) + r'_\S+)')
            seen: set = set()
            for m in fam_pat.finditer(fn_src_text):
                mname = m.group(1)
                if mname in seen:
                    continue
                seen.add(mname)
                mdef, _ = _find_def_in_text(fn_src_text, mname)
                if mdef:
                    defs_to_scan.append((mname, mdef))

        # helpers independent of arg_types
        def _bare(typ):
            t = typ.split(".")[-1] if "." in typ else typ
            if not t or not t.strip():
                return ""
            return t.split()[0]

        def _lit_type(expr):
            m = re.match(r'^\d+#(\w+)$', expr.strip())
            return SUFFIX_TO_TYPE.get(m.group(1)) if m else None

        def _is_literal(expr):
            return bool(re.match(r'^\d+(?:#\w+)?$', expr.strip()))

        def _val(expr):
            m = re.match(r'^(\d+)(?:#\w+)?$', expr.strip())
            return m.group(1) if m else f"{expr}.val"

        arith_re = re.compile(
            r'let\s+\w+\s*←\s*'
            r'(\w+(?:#\w+)?)\s*'
            r'([+\-*/%])\s*'
            r'(\w+(?:#\w+)?)'
        )
        idx_re = re.compile(
            r'let\s+\w+\s*←\s*(Array|Slice)\.index_usize\s+(\w+)\s+(\w+)'
        )

        struct_defs = _parse_struct_defs(fn_src_text or "")
        sat_env = (lean_code or "").rstrip() + "\n"
        # strip shared namespace prefix for readable spec names
        ns_prefix = (func_name.split(".")[0] + ".") if "." in func_name else ""

        specs = []

        for def_name, def_text in defs_to_scan:
            if "Result" not in def_text:
                continue

            # parse this definition's own parameter list
            sig_m = re.search(r'def\s+\S+\s+(.*?)(?:\s*:=|\n\s*\|)', def_text, re.DOTALL)
            if not sig_m:
                continue
            sig = sig_m.group(1)
            arg_types = {}
            for grp in re.findall(r'\(([^)]+)\)', sig):
                colon = grp.find(':')
                if colon == -1:
                    continue
                for n in grp[:colon].split():
                    if n:
                        arg_types[n] = grp[colon + 1:].strip()
            if not arg_types:
                continue

            body_m = re.search(r':=(.*)', def_text, re.DOTALL)
            if not body_m:
                continue
            body = body_m.group(1)

            # arg_scalar uses this definition's arg_types (captured by default arg)
            def _arg_scalar(name, _at=arg_types):
                t = _at.get(name, "")
                b = _bare(t)
                return b if (b in UNSIGNED_BARE or b in SIGNED_BARE) else None

            guards: list = []
            skipped: list = []

            for m in arith_re.finditer(body):
                lhs, op, rhs = m.group(1), m.group(2), m.group(3)
                if op in ('/', '%'):
                    if _is_literal(rhs):
                        lit_m = re.match(r'^(\d+)', rhs)
                        if lit_m and int(lit_m.group(1)) != 0:
                            continue
                    if not (rhs in arg_types or lhs in arg_types):
                        skipped.append(f"{lhs} {op} {rhs} (no func-arg operand)")
                        continue
                    g = f"{_val(rhs)} ≠ 0"
                    if g not in guards:
                        guards.append(g)
                    continue

                typ = (_arg_scalar(lhs) or _arg_scalar(rhs)
                       or _lit_type(lhs) or _lit_type(rhs))
                if typ is None:
                    skipped.append(f"{lhs} {op} {rhs} (unknown type)")
                    continue
                if not _is_literal(lhs) and lhs not in arg_types:
                    skipped.append(f"{lhs} {op} {rhs} (lhs is local)")
                    continue
                if not _is_literal(rhs) and rhs not in arg_types:
                    skipped.append(f"{lhs} {op} {rhs} (rhs is local)")
                    continue

                tmax = f"{typ}.max"
                if typ in UNSIGNED_BARE:
                    if op == '+':
                        g = f"{_val(lhs)} + {_val(rhs)} ≤ {tmax}"
                    elif op == '-':
                        g = f"{_val(rhs)} ≤ {_val(lhs)}"
                    elif op == '*':
                        g = f"{_val(lhs)} * {_val(rhs)} ≤ {tmax}"
                    else:
                        continue
                else:
                    tmin = f"{typ}.min"
                    if op == '+':
                        g = (f"{tmin} ≤ {_val(lhs)} + {_val(rhs)} ∧ "
                             f"{_val(lhs)} + {_val(rhs)} ≤ {tmax}")
                    elif op == '-':
                        g = (f"{tmin} ≤ {_val(lhs)} - {_val(rhs)} ∧ "
                             f"{_val(lhs)} - {_val(rhs)} ≤ {tmax}")
                    elif op == '*':
                        g = (f"{tmin} ≤ {_val(lhs)} * {_val(rhs)} ∧ "
                             f"{_val(lhs)} * {_val(rhs)} ≤ {tmax}")
                    else:
                        continue
                if g not in guards:
                    guards.append(g)

            for m in idx_re.finditer(body):
                coll, idx = m.group(2), m.group(3)
                if idx not in arg_types:
                    skipped.append(f"index_usize {coll}[{idx}] (idx is local)")
                    continue
                coll_type = arg_types.get(coll, "")
                size_m = re.search(r'Array\s+\S+\s+(\d+)#usize', coll_type)
                if size_m:
                    g = f"{_val(idx)} < {size_m.group(1)}"
                elif coll in arg_types:
                    is_slice = "Slice" in coll_type or m.group(1) == "Slice"
                    size_fn = "Slice.len" if is_slice else "Array.size"
                    g = f"{_val(idx)} < {size_fn} {coll}"
                else:
                    skipped.append(f"index_usize {coll}[{idx}] (coll not an arg)")
                    continue
                if g not in guards:
                    guards.append(g)

            if not guards:
                if verbose:
                    msg = (f" ({len(skipped)} skipped: {'; '.join(skipped[:2])})"
                           if skipped else "")
                    print(f"  [ff] {def_name!r}: no guards{msg}")
                continue

            if len(guards) == 1:
                precond = guards[0]
            else:
                precond = " ∧\n    ".join(f"({g})" for g in guards)

            binders = " ".join(f"({n} : {t})" for n, t in arg_types.items())
            args_str = " ".join(arg_types.keys())
            stmt = (f"∀ {binders},\n    {precond} →\n    ∃ r, {def_name} {args_str} = ok r")

            display = def_name[len(ns_prefix):] if def_name.startswith(ns_prefix) else def_name
            spec_name = display.replace(".", "_") + "_no_fail"

            # satisfiability check: prove ∃ args, P to filter vacuous specs
            sat_outcome = "undetermined"
            sat_witness = None
            n_candidates = 0

            if project_dir:
                ex_stmt = f"∃ {binders}, {precond}"
                per_arg = [_witnesses_for_type(t, struct_defs) for t in arg_types.values()]
                candidates = _diverse_tuples(per_arg, 12)
                n_candidates = len(candidates)
                sat_tacs = ["native_decide", "decide", "omega", "simp; omega"]

                for tup in candidates:
                    witness_str = ", ".join(tup)
                    for tac in sat_tacs:
                        code = (sat_env
                                + f"theorem _ff_sat : {ex_stmt} :=\n"
                                + f"  ⟨{witness_str}, by {tac}⟩\n")
                        out, err, rc = run_in_project(code, project_dir=project_dir)
                        combined = (out or "") + (err or "")
                        if rc == 0 and not _errors(combined):
                            sat_outcome = "satisfiable"
                            sat_witness = witness_str
                            break
                    if sat_outcome == "satisfiable":
                        break

                if sat_outcome != "satisfiable" and candidates:
                    names_str = " ".join(arg_types.keys())
                    for tac in ["omega", "simp; omega", "decide"]:
                        code = (sat_env
                                + f"theorem _ff_unsat : ¬{ex_stmt} := by\n"
                                + f"  push_neg\n  intro {names_str}\n  {tac}\n")
                        out, err, rc = run_in_project(code, project_dir=project_dir)
                        combined = (out or "") + (err or "")
                        if rc == 0 and not _errors(combined):
                            sat_outcome = "unsatisfiable"
                            break

            if verbose:
                print(f"  [ff] {def_name!r}: {len(guards)} guards, "
                      f"{len(skipped)} skipped, sat={sat_outcome}")
                if skipped:
                    print(f"       skipped: {'; '.join(skipped[:3])}")
                if sat_outcome == "satisfiable":
                    print(f"       witness: {sat_witness}")
                elif sat_outcome == "unsatisfiable":
                    print(f"       conflicting guards: {'; '.join(guards[:3])}")
                elif n_candidates > 0:
                    print(f"       undetermined ({n_candidates} candidates)")

            if sat_outcome == "unsatisfiable":
                continue
            if sat_outcome == "undetermined" and n_candidates > 0:
                continue

            specs.append({
                "name": spec_name,
                "stmt": stmt,
                "status": "pending",
                "method": None,
                "strategy": "failure-freedom",
                "preamble": "",
            })

        return specs


if __name__ == "__main__":
    import sys
    sys.stdout.reconfigure(encoding="utf-8")

    from lean import Cache
    from synth import LLMClient

    lean_code = "def double (n : Nat) : Nat := n + n"
    func_name = "double"
    test_inputs = ["0", "1", "3", "5"]

    checker = LeanChecker(cache=Cache())
    llm = LLMClient()

    print("strategy 1: spec by example")
    specs = generate_from_examples(lean_code, func_name, test_inputs, checker, llm)
    for s in specs:
        print(f"  {s['name']}: {s['stmt']}")

    print("\nstrategy 2: negative i/o")
    specs = generate_from_negatives(lean_code, func_name, test_inputs, checker, llm)
    for s in specs:
        print(f"  {s['name']}: {s['stmt']}")

    print("\nstrategy 3: generate with proof")
    gwp = generate_with_proof(lean_code, func_name, llm, checker)
    print(f"  {len(gwp)} specs, all proved: {all(s['status'] == 'proved' for s in gwp)}")
    for s in gwp:
        print(f"  {s['name']}: {s['stmt']}")
        print(f"    proof: {s['proof'][:60]!r}")
