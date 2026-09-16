import re
from lean import LeanChecker, _run_lean, _errors, run_in_project
from callgraph import CallGraph


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
    code = func_source or lean_code
    specs = []
    proved_helper_specs = []

    # use call graph for topo-ordered helper discovery
    cg = CallGraph(code)
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
