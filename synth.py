import re
import json
import os
import time
import hashlib
import itertools
import anthropic
from lean import _errors, run_in_project, ProofResult, TACTICS, check_proof, MIN_TRY
from strategies import generate_from_examples, generate_from_negatives, generate_with_proof, theorems, normalize_call
import events
import pricing
import lss_config as _lss_config
import gate as _gate
import bounded as _bounded

def _key():
    import os
    k = os.environ.get("ANTHROPIC_API_KEY")
    if k: return k.strip()
    for p in [r"C:\Users\User\projects\anthropic_api.txt", "/mnt/c/Users/User/projects/anthropic_api.txt"]:
        if os.path.exists(p):
            with open(p) as f: return f.read().strip()
    raise FileNotFoundError("No API key found")
_PROSE_PHRASES = ("Looking at", "Let me", "The key", "I need", "The issue", "The goal")
_LEAN_START = re.compile(r'^\s*(theorem|example|def|∀|```)')

def _strip_prose(text):
    lines = text.splitlines()
    result = []
    in_lean = False
    depth = 0
    for line in lines:
        s = line.strip()
        if not in_lean:
            if _LEAN_START.match(line):
                in_lean = True
            else:
                continue
        line_depth = depth
        depth += s.count('(') + s.count('[') + s.count('{') + s.count('⟨')
        depth -= s.count(')') + s.count(']') + s.count('}') + s.count('⟩')
        depth = max(0, depth)
        if line_depth == 0 and s and any(s.startswith(p) for p in _PROSE_PHRASES):
            continue
        result.append(line)
    if not result:
        return text
    return "\n".join(result)


_llm_call_count = 0

def get_llm_calls():
    global _llm_call_count
    c = _llm_call_count
    _llm_call_count = 0
    return c


class LLMClient:
    def __init__(self):
        self.c = anthropic.Anthropic(api_key=_key())
        self._method_ctx = ""
        self._last_prompt = ""
        self._last_response = ""

    def _ask(self, prompt):
        global _llm_call_count
        _llm_call_count += 1
        self._last_prompt = prompt
        import time
        for attempt in range(3):
            t0 = time.time()
            try:
                r = self.c.messages.create(
                    model="claude-sonnet-4-6",
                    max_tokens=4096,
                    messages=[{"role": "user", "content": prompt}]
                )
                wall_s = time.time() - t0
                u = r.usage
                inp = getattr(u, "input_tokens", 0) or 0
                out = getattr(u, "output_tokens", 0) or 0
                cr = getattr(u, "cache_read_input_tokens", 0) or 0
                cw = getattr(u, "cache_creation_input_tokens", 0) or 0
                usage_dict = {"input_tokens": inp, "output_tokens": out,
                              "cache_read_input_tokens": cr,
                              "cache_creation_input_tokens": cw}
                usd = pricing.cost_usd(r.model, usage_dict)
                events.emit("llm", model=r.model, method=self._method_ctx,
                            input_tokens=inp, output_tokens=out,
                            cache_read_input_tokens=cr, cache_creation_input_tokens=cw,
                            usd=usd, wall_s=wall_s, attempt=attempt, ok=True)
                self._last_response = r.content[0].text
                return self._last_response
            except Exception as e:
                events.emit("llm", model="claude-sonnet-4-6", method=self._method_ctx,
                            ok=False, error_class=type(e).__name__, attempt=attempt,
                            wall_s=time.time() - t0)
                if attempt < 2:
                    time.sleep(2)
                else:
                    print(f"  llm api error: {e}")
                    raise

    def _ask_parsed(self, prompt, parser_fn):
        text = self._ask(prompt)
        try:
            return parser_fn(text)
        except (ValueError, KeyError) as e:
            err = str(e)
        for _ in range(2):
            retry = prompt + f"\n\nyour previous reply could not be parsed: {err}. reply again with only the required format."
            text = self._ask(retry)
            try:
                return parser_fn(text)
            except (ValueError, KeyError) as e:
                err = str(e)
        return None

    def generate_specs(self, lean_code, type_templates, func_name=None, postcond_defs=None, func_source=None):
        self._method_ctx = "generate_specs"
        fn = func_name or _func_name(lean_code)
        sig_ctx = ""
        type_hints = ""
        if fn:
            args, ret_type = _parse_signature(func_source if func_source else lean_code, fn)
            if args is not None:
                args = [(n, _qualify_types(t, lean_code, func_source)) for n, t in args]
                ret_type = _qualify_types(ret_type, lean_code, func_source)
                sig_ctx = f"function signature: {fn} takes {len(args)} argument{'s' if len(args) != 1 else ''}:\n"
                for i, (n, t) in enumerate(args, 1):
                    sig_ctx += f"  arg{i}: {n} : {t}\n"
                if ret_type:
                    sig_ctx += f"  returns: {ret_type}\n"
                sig_ctx += "every theorem must match this exact signature.\n\n"
                precond_params = [(n, t) for n, t in args if "precond" in t.lower() or t.strip() == "Prop"]
                if precond_params:
                    sig_ctx += "important: this function has precondition parameters that must appear in every theorem:\n"
                    for n, t in precond_params:
                        sig_ctx += f"  ({n} : {t})\n"
                    sig_ctx += "example: theorem name : ∀ (x : T) (h : f_precond x), ... := sorry\n"
                    sig_ctx += "do not omit the precondition parameter or the theorem will not typecheck.\n\n"
            if ret_type:
                if "List" in ret_type:
                    type_hints = (
                        "\nSince this returns a List, consider specs about:"
                        "\n- length preservation: output.length = input.length"
                        "\n- membership: elements in output were in input"
                        "\n- ordering: output is sorted if this is a sort function"
                        "\n- structure: relationship between head/tail of output and input\n"
                    )
                elif "Nat" in ret_type or "Int" in ret_type:
                    type_hints = (
                        "\nSince this returns a number, consider specs about:"
                        "\n- bounds: output ≤ input, output ≥ 0"
                        "\n- identity cases: f 0 = ..., f 1 = ..."
                        "\n- monotonicity: if a ≤ b then f a ≤ f b"
                        "\n- relationship to known functions: f a b = Nat.gcd a b\n"
                    )
                elif "Bool" in ret_type:
                    type_hints = (
                        "\nSince this returns a Bool, consider specs about:"
                        "\n- specific inputs: f 0 = true, f [] = false"
                        "\n- relationship to conditions on input\n"
                    )
                elif "Option" in ret_type:
                    type_hints = (
                        "\nSince this returns an Option, consider specs about:"
                        "\n- when it returns some vs none"
                        "\n- the value inside some relates to input\n"
                    )
        prompt = (
            f"lean 4 function:\n{func_source or lean_code}\n\n"
            f"type hints: {', '.join(type_templates)}\n\n"
            + sig_ctx
            + type_hints
        )
        mathlib_examples = self._retrieve_mathlib_examples(func_source or lean_code, fn)
        if mathlib_examples:
            prompt += "\nSimilar Mathlib theorems (follow this style and naming convention):\n"
            prompt += "\n".join(mathlib_examples) + "\n"
            prompt += "Generate specs that follow the same patterns as these Mathlib theorems.\n\n"
        similar_specs = self._retrieve_similar_proved_specs(fn, func_source or lean_code)
        if similar_specs:
            prompt += "\nProved specs from similar functions (adapt these patterns):\n"
            prompt += "\n".join(similar_specs) + "\n"
            prompt += "Write analogous specs for the current function.\n\n"
        prompt += (
            "FORMAT: theorem name : statement := sorry\n"
            "Return only a ```lean code block.\n\n"
            "RULES:\n"
            "- every theorem MUST use ∀ (forall) quantifiers over ALL function arguments\n"
            "- write ONE property per theorem — do not combine multiple claims\n"
            "- every theorem conclusion MUST reference the function call — do not restate input properties alone\n"
            "- do NOT write concrete-value theorems like 'f 3 = 5'\n"
            "- you MAY use standard Mathlib definitions: List.Perm, List.Sorted, Multiset, Nat.gcd, Nat.Prime, Array.size\n"
            "- use standard import paths: import Mathlib.Data.List.Sort, import Mathlib.Data.List.Perm\n\n"
            "GENERATE 10-15 THEOREMS covering these categories (at least one per category):\n"
            "  CATEGORY 1 — Base cases: what does f return on empty/zero/trivial input?\n"
            "  CATEGORY 2 — Size/length: does output have same size as input?\n"
            "  CATEGORY 3 — Element preservation: are the same elements in the output?\n"
            "  CATEGORY 4 — Structural properties: is output sorted/balanced/ordered?\n"
            "  CATEGORY 5 — Recursive relationship: how does f(n+1) relate to f(n)?\n"
            "  CATEGORY 6 — Equivalence: does f equal a known standard library function?\n"
            "  CATEGORY 7 — Idempotence/involution: does f(f(x)) = x or f(f(x)) = f(x)?\n"
        )
        returns_result = "Result" in (func_source or lean_code)
        if returns_result:
            prompt += (
                "\nIMPORTANT: This function returns Result T (it can fail).\n"
                "SPEC FORM: every theorem's conclusion must be a Hoare triple on the call itself:\n"
                "  f args ⦃ r => P r ⦄\n"
                "meaning: `f args` succeeds (it neither fails nor runs forever) with a value `r`, and\n"
                "`P r` holds. so the theorem is false on any input where the call fails: state as\n"
                "hypotheses what the inputs need for it to succeed (e.g. `h : i.val < l.length`).\n"
                "you never write `ok`, `Result.ok`, `.isOk` or `exists r, ... = ok r` yourself — the\n"
                "⦃ ⦄ notation already says the call succeeds and names its value `r`.\n"
                "AENEAS SYNTAX RULES:\n"
                "- Use exact struct field names from type definitions (first/second, NOT x/y/fst/snd)\n"
                "- Integer literals carry their type as a suffix: 0#u32, 5#i8, 1#usize (never (0 : Std.U32))\n"
                "- Apply the function only to distinct bound variables; state a case as a hypothesis:\n"
                "  ∀ (l : CList T) (x : T) (tl : CList T), l = CList.CCons x tl → f l ⦃ r => P r ⦄, never f (CList.CCons x tl)\n"
                "- Write the crate's own types with the crate name, as in the signature above (e.g. Bst.Ord T)\n"
                "- A generic function's theorem stays generic, over all T. For a trait argument (OrdInst : <Crate>.Ord T),\n"
                "  assume what the property needs of its methods as a hypothesis, with a Mathlib class for T if needed:\n"
                "  ∀ {T : Type} (OrdInst : <Crate>.Ord T) [LinearOrder T] (hcmp : ∀ a b, OrdInst.cmp a b = ok (if a < b then\n"
                "  <Crate>.Ordering.Less else if a = b then <Crate>.Ordering.Equal else <Crate>.Ordering.Greater)) ..., f OrdInst ... ⦃ r => P r ⦄\n"
                "- Arithmetic can fail: a + b returns Result, not a plain value\n"
                "- Vec type is alloc.vec.Vec Std.U32, not Vec or List\n"
                "- to state a property of a recursive crate type (a list, a tree), define a helper\n"
                "  before the theorems that turns it into a Lean value, then use it in the statement.\n"
                "  a helper uses only the crate's types and Lean's own functions, never a crate\n"
                "  function (the unit or any other): it is vocabulary, and the gate rejects one that\n"
                "  calls a crate function. for example (the names are illustrative):\n"
                "    def toList {T : Type} : <Crate>.List T → _root_.List T\n"
                "      | .Cons x tl => x :: toList tl\n"
                "      | .Nil => []\n"
                "    theorem nth_spec : ∀ {T : Type} (l : <Crate>.List T) (i : Std.U32), i.val < (toList l).length →\n"
                "      nth l i ⦃ r => (toList l)[i.val]? = some r ⦄ := sorry\n"
                "- if (and only if) this function loops or recurses, you may instead write\n"
                "  f args ⦃ r => P r ⦄div: the call never fails, and returns `r` with `P r` or runs\n"
                "  forever; never use ⦃ ⦄div on a function that always terminates\n"
                "CORRECT EXAMPLES:\n"
                "  theorem swap_correct : forall (p : records.Pair), records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄ := sorry\n"
                "  theorem head_or_spec (xs : lists.List) (d : Std.U32) : lists.head_or xs d ⦃ r => r = match xs with | .Nil => d | .Cons x _ => x ⦄ := sorry\n"
                "  theorem swap_ordered (p : records.Pair) (h : p.first.val ≤ p.second.val) : records.swap p ⦃ r => r.second.val ≤ r.first.val ⦄ := sorry\n"
                "WRONG (never write these):\n"
                "  records.swap p = ok { first := p.second, second := p.first }\n"
                "  exists r, records.swap p = ok r ∧ r.first = p.second\n"
                "  r.x = p.y  (use .first .second)\n"
                "  (records.swap p).isOk\n"
            )
        if postcond_defs:
            for pc_name, pc_body in postcond_defs.items():
                func_in_pc = pc_name.replace("_postcond", "")

                # split into individual conjuncts
                conjuncts = []
                depth = 0
                current = ""
                for char in pc_body:
                    if char == '(':
                        depth += 1
                        current += char
                    elif char == ')':
                        depth -= 1
                        current += char
                    elif char == '∧' and depth == 0:
                        if current.strip():
                            conjuncts.append(current.strip())
                        current = ""
                    else:
                        current += char
                if current.strip():
                    conjuncts.append(current.strip())

                # separate output properties from input properties
                output_props = []
                input_props = []
                for c in conjuncts:
                    if 'result' in c.lower() or func_in_pc in c:
                        output_props.append(c)
                    else:
                        input_props.append(c)

                if output_props:
                    prompt += (
                        "\nThis function has a known postcondition. "
                        "Focus on these OUTPUT properties (these are about what the function RETURNS):\n"
                    )
                    for i, prop in enumerate(output_props, 1):
                        prompt += f"  {i}. {prop}\n"
                    prompt += (
                        f"\nDo NOT generate specs about input constraints like list length > 0. "
                        f"Every spec must reference {func_in_pc} in the conclusion.\n"
                    )

                # also suggest proving the full postcondition
                prompt += (
                    f"\nAlso try to prove the full postcondition:\n"
                    f"  theorem {func_in_pc}_meets_postcond : ∀ args (h : {func_in_pc}_precond args), "
                    f"{pc_name} args ({func_in_pc} args h) h := sorry\n"
                )
        def _parse(text):
            m = re.search(r'```\w*\s*([\s\S]*?)```', text)
            if not m:
                raise ValueError("no code block")
            block = m.group(1)
            th_start = re.search(r'^theorem\s', block, re.MULTILINE)
            preamble = block[:th_start.start()].strip() if th_start else ""
            # remove defs from preamble that duplicate what's already in lean_code
            if preamble:
                existing = set(re.findall(r'\bdef\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code))
                chunks = re.split(r'(?=\ndef\s)', "\n" + preamble)
                kept = []
                for chunk in chunks:
                    dm = re.match(r'\ndef\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', chunk)
                    if dm and dm.group(1) in existing:
                        continue
                    kept.append(chunk)
                preamble = "".join(kept).strip()
                # drop preamble if it's only comments and whitespace
                if not re.search(r'^(?!--)[^\s]', preamble, re.MULTILINE):
                    preamble = ""
            specs = []
            for name, stmt, _ in theorems(block):
                spec = {"name": name, "stmt": stmt, "status": "pending", "method": ""}
                if preamble:
                    spec["preamble"] = preamble
                specs.append(spec)
            if not specs:
                raise ValueError("no theorems found")
            return specs
        return self._ask_parsed(prompt, _parse) or []

    def generate_proof(self, lean_code, theorem_stmt, feedback="", func_name=None, helpers=None, prev_proofs=None):
        self._method_ctx = "generate_proof"
        fb = f"\nprevious error:\n{feedback}" if feedback else ""
        hints = ""
        if func_name:
            all_defs = re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code)
            helper_names = helpers if helpers is not None else [d for d in all_defs if d != func_name]
            names = ", ".join([func_name] + helper_names)
            hints = (
                f"\nhints:"
                f"\n- the main function is '{func_name}'"
                f"\n- try: simp [{names}]"
                f"\n- for recursive functions, try: fun_induction {func_name} <args> <;> simp [{names}, *]"
                f"\n- fun_induction automatically follows the function's recursion pattern"
                f"\n- fallback: induction <arg> <;> simp [{names}, *]"
                f"\n- if induction doesn't close all goals, try adding <;> omega after simp"
            )
        stmt_lower = theorem_stmt.lower()
        lemma_hints = []
        if "nat" in lean_code.lower() or "nat" in stmt_lower:
            lemma_hints.extend(["Nat.zero_le", "Nat.succ_pos", "Nat.le_refl", "Nat.mul_comm", "Nat.mul_assoc", "Nat.add_comm", "Nat.add_assoc", "Nat.sub_add_cancel", "Nat.div_add_mod", "Nat.mod_def", "Nat.mul_div_cancel", "Nat.succ_sub", "Nat.lt_of_lt_of_le"])
        if "list" in lean_code.lower() or "list" in stmt_lower:
            lemma_hints.extend(["List.length_nil", "List.length_cons", "List.length_append", "List.mem_cons", "List.mem_nil_iff", "List.append_nil", "List.nil_append", "List.cons_append"])
        if "dvd" in stmt_lower or "∣" in stmt_lower:
            lemma_hints.extend(["Nat.dvd_refl", "Nat.dvd_trans", "Nat.dvd_zero", "Nat.zero_dvd", "Nat.dvd_add", "Nat.dvd_sub'"])
        if lemma_hints:
            hints += f"\n- potentially useful lemmas: {', '.join(lemma_hints)}"
        hist = ""
        if prev_proofs:
            lines = ["PREVIOUS ATTEMPTS THAT FAILED (do not repeat these strategies):"]
            for j, (p, e) in enumerate(prev_proofs[:5], 1):
                p_short = repr(p[:100])
                e_short = repr(e[:80])
                lines.append(f"Attempt {j}: {p_short} -> Error: {e_short}")
            lines.append("Try a FUNDAMENTALLY DIFFERENT approach.")
            hist = "\n".join(lines) + "\n\n"
        prompt = (
            f"lean 4 context:\n{lean_code}\n\n"
            f"{hist}"
            f"prove: {theorem_stmt}{fb}{hints}\n\n"
            "CRITICAL: output ONLY tactic code. no english text, no comments, no explanations.\n"
            "do NOT start with 'Looking at', 'Let me think', 'The key', etc.\n"
            "do NOT use these unavailable tactics: ring, ring_nf, positivity, split_ifs, rename_i, push_neg, linarith, norm_cast, field_simp, convert, exact?, apply?\n"
            "available tactics: simp, omega, decide, aesop, grind, tauto, rfl, trivial, constructor, intro, intros, induction, cases, rcases, obtain, have, rw, ext, funext, exact, assumption, contradiction, exfalso, unfold, dsimp, simp_all, norm_num\n"
            "return only the tactic body (what goes after 'by'). no surrounding code."
        )
        def _parse(text):
            m = re.search(r'```\w*\s*([\s\S]*?)```', text)
            if m:
                text = m.group(1).strip()
            else:
                text = text.strip()
            text = text.removeprefix("by").strip()
            text = _strip_prose(text)
            if not text:
                raise ValueError("empty proof")
            return text
        return self._ask_parsed(prompt, _parse) or ""

    def repair_proof(self, lean_code, theorem_stmt, parsed_error, func_name=None, helpers=None, prev_proofs=None):
        self._method_ctx = "generate_proof"
        hints = ""
        if func_name:
            all_defs = re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code)
            helper_names = helpers if helpers is not None else [d for d in all_defs if d != func_name]
            names = ", ".join([func_name] + helper_names)
            hints = (
                f"\nhints:"
                f"\n- the main function is '{func_name}'"
                f"\n- try: simp [{names}]"
                f"\n- for recursive functions, try: fun_induction {func_name} <args> <;> simp [{names}, *]"
                f"\n- fun_induction automatically follows the function's recursion pattern"
                f"\n- fallback: induction <arg> <;> simp [{names}, *]"
                f"\n- if induction doesn't close all goals, try adding <;> omega after simp"
            )
        stmt_lower = theorem_stmt.lower()
        lemma_hints = []
        if "nat" in lean_code.lower() or "nat" in stmt_lower:
            lemma_hints.extend(["Nat.zero_le", "Nat.succ_pos", "Nat.le_refl", "Nat.mul_comm", "Nat.mul_assoc", "Nat.add_comm", "Nat.add_assoc", "Nat.sub_add_cancel", "Nat.div_add_mod", "Nat.mod_def", "Nat.mul_div_cancel", "Nat.succ_sub", "Nat.lt_of_lt_of_le"])
        if "list" in lean_code.lower() or "list" in stmt_lower:
            lemma_hints.extend(["List.length_nil", "List.length_cons", "List.length_append", "List.mem_cons", "List.mem_nil_iff", "List.append_nil", "List.nil_append", "List.cons_append"])
        if "dvd" in stmt_lower or "∣" in stmt_lower:
            lemma_hints.extend(["Nat.dvd_refl", "Nat.dvd_trans", "Nat.dvd_zero", "Nat.zero_dvd", "Nat.dvd_add", "Nat.dvd_sub'"])
        if lemma_hints:
            hints += f"\n- potentially useful lemmas: {', '.join(lemma_hints)}"
        hist = ""
        if prev_proofs:
            lines = ["PREVIOUS ATTEMPTS THAT FAILED (do not repeat these strategies):"]
            for j, (p, e) in enumerate(prev_proofs[:5], 1):
                p_short = repr(p[:100])
                e_short = repr(e[:80])
                lines.append(f"Attempt {j}: {p_short} -> Error: {e_short}")
            lines.append("Try a FUNDAMENTALLY DIFFERENT approach.")
            hist = "\n".join(lines) + "\n\n"
        kind = parsed_error.get("kind", "other")
        if kind == "unsolved_goals":
            goals = parsed_error["goals"]
            if len(goals) == 1:
                g = goals[0]
                hyps = g["hyps"] or "none"
                task = (
                    f"One goal remains unsolved.\n"
                    f"Goal: {g['target']}\n"
                    f"Hypotheses: {hyps}\n"
                    "Write tactics to close ONLY this goal."
                )
            else:
                lines = [f"There are {len(goals)} unsolved goals after the tactic attempt."]
                for j, g in enumerate(goals, 1):
                    label = g["case"] or f"goal {j}"
                    lines.append(f"Goal {j} (case {label}): {g['target']}")
                lines.append(f"Write a tactic block that handles all {len(goals)} cases.")
                task = "\n".join(lines)
        elif kind == "type_mismatch":
            task = (
                f"Type mismatch error.\n"
                f"Expected: {parsed_error.get('expected', '')}\n"
                f"Actual: {parsed_error.get('actual', '')}\n"
                "Fix the tactic to produce the expected type."
            )
        else:
            task = f"prove: {theorem_stmt}\nprevious error:\n{parsed_error.get('raw', '')}"
        prompt = (
            f"lean 4 context:\n{lean_code}\n\n"
            f"{hist}"
            f"{task}{hints}\n\n"
            "CRITICAL: output ONLY tactic code. no english text, no comments, no explanations.\n"
            "do NOT start with 'Looking at', 'Let me think', 'The key', etc.\n"
            "do NOT use these unavailable tactics: ring, ring_nf, positivity, split_ifs, rename_i, push_neg, linarith, norm_cast, field_simp, convert, exact?, apply?\n"
            "available tactics: simp, omega, decide, aesop, grind, tauto, rfl, trivial, constructor, intro, intros, induction, cases, rcases, obtain, have, rw, ext, funext, exact, assumption, contradiction, exfalso, unfold, dsimp, simp_all, norm_num\n"
            "return only the tactic body (what goes after 'by'). no surrounding code."
        )
        def _parse(text):
            m = re.search(r'```\w*\s*([\s\S]*?)```', text)
            if m:
                text = m.group(1).strip()
            else:
                text = text.strip()
            text = text.removeprefix("by").strip()
            text = _strip_prose(text)
            if not text:
                raise ValueError("empty proof")
            return text
        return self._ask_parsed(prompt, _parse) or ""

    def generate_proofs_multi(self, lean_code, theorem_stmt, n=2, func_name=None, helpers=None):
        self._method_ctx = "generate_proof"
        strategies = [
            "try induction on the main argument, then simp with function names",
            "try cases analysis or direct simplification",
        ]
        proofs = []
        for i in range(n):
            strategy = strategies[i % len(strategies)]
            proof = self.generate_proof(
                lean_code, theorem_stmt,
                feedback=f"strategy for this attempt: {strategy}",
                func_name=func_name, helpers=helpers,
            )
            proofs.append(proof)
        return [p for p in proofs if p]

    def generate_calc_proof(self, lean_code, theorem_stmt, func_name=None):
        self._method_ctx = "generate_proof"
        fn_note = f"\nthe main function is '{func_name}'." if func_name else ""
        prompt = (
            "prove this theorem using a calc block that shows step-by-step equalities.\n\n"
            "example:\ncalc expr\n  _ = step1 := by simp [f]\n  _ = final := by omega\n\n"
            f"function:\n{lean_code}\n"
            f"theorem: {theorem_stmt}{fn_note}\n"
            "CRITICAL: output ONLY the calc block. no english. start with 'calc'."
        )
        text = self._ask(prompt).strip()
        m = re.search(r'```\w*\s*([\s\S]*?)```', text)
        if m:
            text = m.group(1).strip()
        text = text.removeprefix("by").strip()
        text = _strip_prose(text)
        return text if "calc" in text else ""

    def generate_adversarial(self, specs, signature, prev_failures=None, lean_code=None,
                              func_name=None, test_pairs=None):
        self._method_ctx = "generate_adversarial"
        stmts = "\n".join(f"  {s['stmt']}" for s in specs)

        fail_ctx = ""
        if prev_failures:
            fail_ctx = "\nPrevious attempts that FAILED (do NOT repeat these):\n"
            for pf in prev_failures[-3:]:
                fail_ctx += f"---\n{pf[:200]}\n"

        body = ""
        if lean_code and func_name:
            m = re.search(rf'def\s+{re.escape(func_name)}\s+.*?:=([\s\S]*?)(?=\ndef\s|\Z)', lean_code)
            if m:
                body = m.group(1).strip()

        pairs_ctx = ""
        if test_pairs:
            pairs_ctx = "\nConcrete input-output pairs (your function MUST differ on at least one):\n"
            for inp, out in test_pairs[:3]:
                pairs_ctx += f"  input: {inp} → correct output: {out} → YOUR output must NOT be {out}\n"

        prompt = (
            f"I need a WRONG version of this Lean 4 function.\n\n"
            f"Function signature (DO NOT CHANGE THIS):\n"
            f"  {signature}\n\n"
            f"Current function body:\n"
            f"  := {body}\n\n"
            f"These theorems must still be provable with your wrong version:\n{stmts}\n\n"
            f"{pairs_ctx}\n"
            f"RULES:\n"
            f"1. Write ONLY the new function body starting with :=\n"
            f"2. Do NOT redefine any _precond functions\n"
            f"3. Do NOT change the function signature or name\n"
            f"4. Do NOT add any new definitions\n"
            f"5. The body must type-check with the given signature\n"
            f"6. All theorems above must still be provable\n"
            f"7. The function must return a DIFFERENT value on at least one input\n\n"
            f"Output ONLY the function body. Start with :=, on one line (use indented continuation lines if needed).\n"
            f"Do NOT include any explanation, reasoning, alternatives, or prose.\n"
            f"Any text other than a := body will be rejected by the parser.\n"
            f"If truly impossible, output exactly the single word: IMPOSSIBLE\n"
            f"{fail_ctx}"
        )
        return self._ask(prompt) or ""

    def propose_stronger(self, spec_stmt, lean_code):
        prompt = (
            f"Current theorem about this function:\n"
            f"  {spec_stmt}\n\n"
            f"Function:\n{lean_code[:500]}\n\n"
            f"Propose a STRICTLY STRONGER theorem that implies the current one.\n"
            f"Stronger means: the new statement logically implies the old one, but not vice versa.\n"
            f"Examples of strengthening:\n"
            f"  - ∀ l, f l ≥ 0  →  ∀ l, f l = l.length  (exact value instead of bound)\n"
            f"  - ∀ l, f l = f l  →  ∀ l, f l = l.reverse  (meaningful instead of trivial)\n"
            f"  - ∀ l, l.length > 0 → ...  →  ∀ l, ...  (remove unnecessary precondition)\n\n"
            f"Return ONLY the new theorem statement (after the colon, before := sorry).\n"
            f"If no meaningful strengthening exists, return exactly: NONE"
        )
        return self._ask(prompt).strip()

    def _retrieve_mathlib_examples(self, lean_code, func_name):
        """retrieve similar mathlib theorems via loogle + leansearch apis."""
        import urllib.request
        import urllib.parse
        import json as _json
        results = []

        args, ret_type = _parse_signature(lean_code, func_name) if func_name else (None, None)
        ret_type = ret_type or ""

        loogle_queries = []
        if "List" in ret_type:
            loogle_queries.extend(["List _ → List _", "List.length", "List.Perm"])
        if "Nat" in ret_type or "Int" in ret_type:
            loogle_queries.extend(["Nat → Nat → Nat", "Nat.dvd", "_ ∣ _"])
        if "Array" in ret_type:
            loogle_queries.extend(["Array.size", "Array _ → Array _"])
        if "Bool" in ret_type:
            loogle_queries.extend(["_ → Bool", "Bool.and"])
        if "Option" in ret_type:
            loogle_queries.extend(["Option.isSome", "Option _"])
        if args:
            for name, typ in args:
                if "List" in typ and "List" not in ret_type:
                    loogle_queries.append("List _ → _")
                if "Nat" in typ and "Nat" not in ret_type:
                    loogle_queries.append("Nat → _")

        for query in loogle_queries[:3]:
            try:
                url = "https://loogle.lean-lang.org/json?q=" + urllib.parse.quote(query)
                req = urllib.request.Request(url, headers={"User-Agent": "lean-spec-synth"})
                with urllib.request.urlopen(req, timeout=5) as resp:
                    data = _json.loads(resp.read().decode())
                    for hit in data.get("hits", [])[:2]:
                        name = hit.get("name", "")
                        typ = hit.get("type", "")
                        if name and typ:
                            results.append(f"-- Mathlib: {name} : {typ}")
            except Exception:
                pass

        if func_name:
            words = re.sub(r'([A-Z])', r' \1', func_name).strip().lower()
            try:
                url = "https://leansearch.net/api/search?q=" + urllib.parse.quote(words)
                req = urllib.request.Request(url, headers={"User-Agent": "lean-spec-synth"})
                with urllib.request.urlopen(req, timeout=5) as resp:
                    data = _json.loads(resp.read().decode())
                    for hit in data[:3]:
                        name = hit.get("name", "")
                        statement = hit.get("statement", "")
                        if name and statement:
                            results.append(f"-- Mathlib: {name} : {statement[:120]}")
            except Exception:
                pass

        seen = set()
        unique = []
        for r in results:
            if r not in seen:
                seen.add(r)
                unique.append(r)
        return unique[:5]

    def _retrieve_similar_proved_specs(self, func_name, lean_code, max_results=5):
        """SpecSyn-style: find proved specs from previous runs for similar functions."""
        import os
        import glob
        similar = []
        name_words = set(re.findall(r'[a-z]+', func_name.lower()))
        run_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".lss", "runs")
        if not os.path.isdir(run_dir):
            return []
        run_files = sorted(glob.glob(os.path.join(run_dir, "run_*.txt")), reverse=True)
        for rf in run_files[:5]:
            try:
                with open(rf, encoding="utf-8", errors="replace") as f:
                    text = f.read()
                blocks = re.split(r'(?=^--- )', text, flags=re.MULTILINE)
                for block in blocks:
                    name_match = re.match(r'--- (\S+) ---', block)
                    if not name_match:
                        continue
                    bench_name = name_match.group(1)
                    bench_words = set(re.findall(r'[a-z]+', bench_name.lower()))
                    overlap = name_words & bench_words
                    if len(overlap) >= 2 or (len(overlap) >= 1 and len(name_words) <= 2):
                        proved = re.findall(r'kernel-proved\s+\[.*?\]\s+\w+:\s+(.+)', block)
                        for spec_stmt in proved[:2]:
                            similar.append(f"-- Similar function ({bench_name}): {spec_stmt.strip()[:120]}")
                if len(similar) >= max_results:
                    break
            except Exception:
                continue
        return similar[:max_results]

    def generate_specs_raw(self, prompt):
        """generate specs from a raw prompt string."""
        self._method_ctx = "generate_specs_raw"
        resp = self._ask(prompt)
        if not resp:
            return []
        specs = []
        for name, stmt, _ in theorems(resp):
            specs.append({
                "name": name,
                "stmt": stmt,
                "status": "pending",
                "method": None,
                "preamble": "",
            })
        return specs


class LLMLogger(LLMClient):
    def __init__(self):
        super().__init__()
        os.makedirs(".lss", exist_ok=True)
        self._log_path = ".lss/llm_log.jsonl"

    def _ask(self, prompt):
        h = hashlib.md5(prompt.encode()).hexdigest()
        self._append({"ts": time.time(), "method": self._method_ctx, "prompt_hash": h, "prompt_length": len(prompt)})
        result = super()._ask(prompt)
        if result:
            self._append({"ts": time.time(), "prompt_hash": h, "response_length": len(result), "model": "gemini-2.5-flash"})
        else:
            self._append({"ts": time.time(), "prompt_hash": h, "error": "empty response"})
        return result

    def _append(self, entry):
        with open(self._log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")


def _func_name(lean_code):
    m = re.search(r"def\s+([a-zA-Z_][a-zA-Z0-9_'!?]*)", lean_code)
    return m.group(1) if m else ""


def _func_signature(lean_code, func_name):
    m = re.search(rf'(def\s+{re.escape(func_name)}\b.*?)\s*:=', lean_code, re.DOTALL)
    return m.group(1).strip() if m else ""


def _get_signature_string(lean_code, func_name):
    m = re.search(rf'def\s+{re.escape(func_name)}\s+(.*?)(?::=|\bwhere\b)', lean_code, re.DOTALL)
    return m.group(1).strip() if m else ""


def _classify_complexity(lean_code, func_name):
    """AutoReSpec-style: classify function as simple, medium, or hard."""
    func_match = re.search(
        rf'def\s+{re.escape(func_name)}\s+.*?:=([\s\S]*?)(?=\ndef\s|\Z)', lean_code)
    if not func_match:
        return "simple"
    body = func_match.group(1)
    line_count = body.count("\n")
    all_defs = re.findall(r'def\s+(\w+)', lean_code)
    helper_count = len([d for d in all_defs if d != func_name and '_precond' not in d])
    complex_types = sum(1 for t in ["Array", "HashMap", "String", "Fin", "Subtype"] if t in lean_code)
    if line_count > 40 or helper_count >= 3 or complex_types >= 2:
        return "hard"
    elif line_count > 15 or helper_count >= 1 or complex_types >= 1:
        return "medium"
    else:
        return "simple"


def _qualify_types(t, lean_code, func_source):
    """a rust unit's signature type with the crate's own type names written in full
    (Ord T -> Bst.Ord T), so a statement copying it means the crate's type under
    `open <crate>`, never a same-named Lean one."""
    crate = re.search(r"^open (?!Aeneas\b)(\S+)\s*$", lean_code or "", re.MULTILINE)
    if not t or not crate or not func_source:
        return t
    local = set(re.findall(r"^(?:structure|inductive|class|abbrev)\s+([A-Za-z_][\w']*)", func_source, re.MULTILINE))
    for name in sorted(local, key=len, reverse=True):
        t = re.sub(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])", f"{crate.group(1)}.{name}", t)
    return t


def _parse_signature(lean_code, fn):
    """the explicit arguments [(name, type)] and the return type of `def fn`;
    binder groups nest, so `(t : Option (Node T))` is one argument."""
    m = re.search(r'def\s+' + re.escape(fn) + r"(?![\w'])", lean_code)
    if not m:
        return None, None
    text, i, n, args = lean_code, m.end(), len(lean_code), []
    while True:
        while i < n and text[i].isspace():
            i += 1
        if i >= n or text[i] not in "({[⦃":
            break
        depth, j = 0, i
        while j < n:
            depth += (text[j] in "({[⦃") - (text[j] in ")}]⦄")
            if depth == 0:
                break
            j += 1
        group = text[i + 1:j]
        if text[i] == "(" and ":" in group:
            names, typ = group.split(":", 1)
            args += [(nm, typ.strip()) for nm in names.split() if nm.strip()]
        i = j + 1
    ret = re.match(r"\s*:\s*([\s\S]*?)\s*(?::=|\n\s*\||\Z)", text[i:])
    return args, (ret.group(1).strip() if ret else "")


def _replace_body(lean_code):
    # replace impl with wrong default value
    return re.sub(r':=.*', ':= default', lean_code, count=1, flags=re.DOTALL)

def _make_wrong(lean_code, func_name):
    # use (?!\w) instead of \b so names ending in ' are found correctly
    ms = list(re.finditer(r'\bdef\s+' + re.escape(func_name) + r'(?!\w)', lean_code))
    if ms:
        pos = lean_code.find(':=', ms[-1].end())
        if pos != -1:
            return lean_code[:pos] + ':= default'
        # pattern-matching style: no := at def level, cut before first arm
        pipe_m = re.search(r'\n\s*\|', lean_code[ms[-1].end():])
        if pipe_m:
            cut = ms[-1].end() + pipe_m.start()
            return lean_code[:cut] + '\n  := default'
    return _replace_body(lean_code)

def _make_wrong_for_spec(lean_code, spec_stmt, all_funcs):
    # prefer non-precond functions
    for fname in all_funcs:
        if fname in spec_stmt and '_precond' not in fname:
            return _make_wrong(lean_code, fname)
    for fname in all_funcs:
        if fname in spec_stmt:
            return _make_wrong(lean_code, fname)
    return _make_wrong(lean_code, all_funcs[0]) if all_funcs else _replace_body(lean_code)

def _generate_wrong_values(lean_code, func_name):
    """generate wrong output values based on function return type."""
    m = re.search(r'def\s+' + re.escape(func_name) + r'[^:]*:\s*(\S+(?:\s+\S+)*?)\s*(?::=|\n\s*\|)', lean_code)
    ret_type = m.group(1) if m else ""
    wrongs = ["default"]
    if "List" in ret_type:
        wrongs.extend(["[0]", "[1, 0]", "[]"])
    elif "Array" in ret_type:
        wrongs.extend(["#[]", "#[0]"])
    elif "Nat" in ret_type:
        wrongs.extend(["0", "1", "42", "999"])
    elif "Int" in ret_type:
        wrongs.extend(["0", "-1", "42", "-999"])
    elif "Bool" in ret_type:
        wrongs.extend(["true", "false"])
    elif "Option" in ret_type:
        wrongs.extend(["none", "some default"])
    else:
        wrongs.extend(["default", "0"])
    return wrongs


def _perturb_correct_output(correct_out):
    """perturb the correct output to generate wrong outputs (LeetProof-style)."""
    s = str(correct_out).strip()
    wrongs = []
    try:
        n = int(s)
        wrongs.extend([str(n + 1), str(n - 1), str(-n), str(n * 2), str(n + 10)])
    except ValueError:
        pass
    if s.startswith("["):
        elements = s.strip("[]").split(",")
        elements = [e.strip() for e in elements if e.strip()]
        if len(elements) >= 2:
            swapped = elements.copy()
            swapped[0], swapped[1] = swapped[1], swapped[0]
            wrongs.append("[" + ", ".join(swapped) + "]")
            wrongs.append("[" + ", ".join(reversed(elements)) + "]")
            wrongs.append("[" + ", ".join(elements[:-1]) + "]")
            wrongs.append("[" + ", ".join(elements) + ", 0]")
        if len(elements) == 0:
            wrongs.extend(["[0]", "[1]"])
        elif len(elements) == 1:
            wrongs.extend(["[]", "[" + elements[0] + ", " + elements[0] + "]"])
    if s == "true":
        wrongs.append("false")
    elif s == "false":
        wrongs.append("true")
    if s == "none":
        wrongs.extend(["some 0", "some 1"])
    elif s.startswith("some"):
        wrongs.append("none")
        inner = s[4:].strip().strip("()")
        try:
            n = int(inner)
            wrongs.append(f"some {n+1}")
        except ValueError:
            pass
    return wrongs


def _type_constants(correct_out):
    """fallback constants based on output type."""
    s = str(correct_out).strip()
    if s.startswith("["):
        return ["[]", "[0]", "[1, 0]"]
    try:
        int(s)
        return ["0", "1", "999"]
    except ValueError:
        pass
    if s in ("true", "false"):
        return ["true", "false"]
    return ["default"]


def _make_wrong_for_spec_identity(lean_code, spec_stmt, all_funcs):
    target = None
    for fname in all_funcs:
        if fname in spec_stmt and '_precond' not in fname:
            target = fname
            break
    if not target:
        return lean_code
    m = re.search(
        rf'def\s+{re.escape(target)}\s+[^:]*:\s*([^:]*?)\s*:=',
        lean_code
    )
    if not m:
        return lean_code
    ret_type = m.group(1).strip()
    if "List" in ret_type:
        alt_val = "[0]"
    elif "Bool" in ret_type:
        alt_val = "true"
    elif "Int" in ret_type:
        alt_val = "1"
    elif "Nat" in ret_type:
        alt_val = "1"
    elif "Option" in ret_type:
        alt_val = "some default"
    else:
        alt_val = "default"
    wrong = re.sub(
        rf'(def\s+{re.escape(target)}\s+[^:]*:[^:]*):=[\s\S]*?(?=\ndef\s|\Z)',
        rf'\1:= {alt_val}',
        lean_code, count=1
    )
    return wrong

def _try_lean_proof(lean_code, stmt, proof_text, project_dir=None):
    """(proved, output): proved is the LSS_PROOF verdict of `theorem _t : stmt := by
    <proof_text>`; output keeps the Lean errors for repair prompts."""
    lines = [l.strip() for l in proof_text.splitlines() if l.strip()]
    if not lines:
        return False, "empty proof"
    indented = "\n".join("  " + l for l in lines)
    v, out = check_proof(lean_code, f"theorem _t : {stmt} := by\n{indented}", "_t", project_dir=project_dir)
    return v["ok"], out.strip()

def _try_lean_proof_partial(lean_code, stmt, proof_text, project_dir=None):
    """like _try_lean_proof but allows remaining sorry (for per-sorry filling verification)."""
    lines = [l.strip() for l in proof_text.splitlines() if l.strip()]
    if not lines:
        return False, "empty proof"
    indented = "\n".join("  " + l for l in lines)
    code = lean_code.rstrip() + f"\ntheorem _t : {stmt} := by\n{indented}"
    stdout, stderr, rc = run_in_project(code, project_dir=project_dir)
    combined = stdout + stderr
    errs = _errors(combined)
    ok = rc == 0 and not errs
    return ok, combined.strip()


def _parse_lean_error(error_text):
    if "type mismatch" in error_text:
        exp_m = re.search(r'expected to have type\s*\n\s*(.*)', error_text)
        act_m = re.search(r'has type\s*\n\s*(.*)', error_text)
        return {
            "kind": "type_mismatch",
            "expected": exp_m.group(1).strip() if exp_m else "",
            "actual": act_m.group(1).strip() if act_m else "",
        }
    if "unsolved goals" in error_text:
        idx = error_text.find("unsolved goals")
        after = error_text[idx + len("unsolved goals"):].lstrip('\n')
        goals = []
        for block in re.split(r'\n\s*\n', after.strip()):
            if not block.strip():
                continue
            lines = block.strip().splitlines()
            case_label = ""
            hyp_lines = []
            target = ""
            for line in lines:
                if line.startswith("case "):
                    case_label = line[5:].strip()
                elif line.startswith("⊢ "):
                    target = line[2:].strip()
                elif line.strip():
                    hyp_lines.append(line.strip())
            goals.append({"case": case_label, "hyps": "\n".join(hyp_lines), "target": target})
        if goals:
            return {"kind": "unsolved_goals", "goals": goals}
    return {"kind": "other", "raw": error_text}


def _tactic_of(method):
    """method labels look like 'l1:simp' or 'l2:hammer (16.5s)'.
    Strip the layer prefix and any timing suffix to get a usable tactic."""
    if not method:
        return ""
    t = method.split(":", 1)[1] if ":" in method else method
    return t.split("(")[0].strip()


def _prove_claim(lean_code, claim, lean_checker, project_dir=None, seconds=None):
    """try to prove a standalone claim using layer 1 then layer 2; return (proved, proof_body).
    with `seconds`, both layers share that time: layer 1 gets at least MIN_TRY
    seconds, hammer only what is left, and only if that is at least MIN_TRY."""
    fn = _func_name(lean_code)
    t0 = time.monotonic()
    l1 = None if seconds is None else max(MIN_TRY, min(_lss_config.server_cfg()["cmd_timeout"], seconds))
    pr = lean_checker.try_proof(lean_code, claim, func_name=fn, project_dir=project_dir, timeout=l1)
    if pr.proved:
        return True, _tactic_of(pr.method)
    left = None if seconds is None else seconds - (time.monotonic() - t0)
    if left is not None and left < MIN_TRY:
        return False, ""
    hammer = None if left is None else min(_lss_config.server_cfg()["hammer_timeout"], left)
    pr2 = lean_checker.try_hammer(lean_code, claim, project_dir=project_dir, timeout=hammer)
    if pr2.proved:
        return True, _tactic_of(pr2.method)
    return False, ""


_MAX_HAVES = 5

@events.layer("decompose")
def decompose_and_prove(lean_code, theorem_stmt, lean_checker, llm, project_dir=None, func_source=None):
    # layer 3: llm decomposes goal; try verbatim first, then fill have sub-lemmas.
    # the Lean work after the sketch shares one budget, [proof] split_seconds: each
    # sub-lemma gets an equal share of what is left, the final checks the rest.
    prompt = (
        "This theorem cannot be proved directly. Decompose it into intermediate steps using 'have' statements.\n"
        f"Function: {func_source or lean_code}\n"
        f"Theorem: {theorem_stmt}\n"
        f"Use at most {_MAX_HAVES} have statements. Return a proof sketch:\n"
        "by\n"
        "  have h1 : <intermediate_claim_1> := sorry\n"
        "  have h2 : <intermediate_claim_2> := sorry\n"
        "  <final tactic using h1, h2>"
    )
    text = llm._ask(prompt).strip()
    m = re.search(r'```\w*\s*([\s\S]*?)```', text)
    if m:
        text = m.group(1).strip()
    sketch = text.removeprefix("by").strip()
    deadline = time.monotonic() + _lss_config.proof_cfg()["split_seconds"]

    def left():
        return deadline - time.monotonic()

    def cap():
        return max(MIN_TRY, min(_lss_config.server_cfg()["cmd_timeout"], left()))

    # step 1: try the sketch verbatim — common case when llm fills its own holes
    if project_dir:
        _ml_ok, _ = lean_checker._precheck_env(project_dir)
        _hm_ok, _ = lean_checker._precheck_env(project_dir, requires_hammer=True)
    else:
        _ml_ok = _hm_ok = True
    preamble = (("import Mathlib\n" if _ml_ok else "") +
                ("import Hammer\n" if _hm_ok else "") +
                lean_code.rstrip() + "\n")
    verbatim = f"theorem _sketch_check : {theorem_stmt} := by\n"
    verbatim += "\n".join("  " + l for l in sketch.splitlines())
    v, _ = check_proof(preamble, verbatim, "_sketch_check", project_dir=project_dir, timeout=cap())
    if v["ok"]:
        return ProofResult(proved=True, method="l3:llm_sketch", error="", axioms=v["axioms"])

    # step 2: parse have statements; match := sorry OR := by <single or multi-line tactic>
    have_re = re.compile(
        r'have\s+(\w+)\s*:([\s\S]*?):=[ \t]*(?:sorry|by\b(?:[ \t]+[^\n]*)?(?:\n[ \t]+[^\n]*)*)',
        re.MULTILINE
    )
    haves = list(have_re.finditer(sketch))
    if not haves:
        return ProofResult(proved=False, method="", error=f"no have statements in sketch: {sketch[:300]}")
    haves = haves[:_MAX_HAVES]

    filled_haves = []
    have_names = []
    for i, hm in enumerate(haves):
        name = hm.group(1)
        claim = hm.group(2).strip()
        ok, proof_body = _prove_claim(lean_code, claim, lean_checker, project_dir=project_dir,
                                      seconds=left() / (len(haves) - i))
        if not ok:
            return ProofResult(proved=False, method="", error=f"cannot prove: {claim[:80]}")
        filled_haves.append(f"have {name} : {claim} := by {proof_body}")
        have_names.append(name)

    closing_section = sketch[haves[-1].end():].strip()
    filled = "\n".join(filled_haves)
    if closing_section:
        filled = filled + "\n" + closing_section

    if "sorry" in filled:
        return ProofResult(proved=False, method="", error="residual sorry after filling")

    # step 3: one final lean invocation — kernel checks the whole proof
    check_code = f"theorem _decomp_final : {theorem_stmt} := by\n"
    check_code += "\n".join("  " + l for l in filled.splitlines())
    v, combined = check_proof(preamble, check_code, "_decomp_final", project_dir=project_dir, timeout=cap())
    if v["ok"]:
        return ProofResult(proved=True, method="l3:decompose", error="", axioms=v["axioms"])

    # step 4: repair — replace LLM's closing tactic; filled_haves already correct
    have_body = "\n".join("  " + l for l in "\n".join(filled_haves).splitlines())
    candidates = [
        "assumption", "simp_all", "simp [*]", "omega", "aesop", "tauto",
    ] + [f"exact {n}" for n in have_names] + [f"apply {n}" for n in have_names]
    if have_names:
        candidates.append(f"simp [{', '.join(have_names)}, *]")
    for ct in candidates[:10]:
        if left() < MIN_TRY:
            break
        repair_code = f"theorem _decomp_repaired : {theorem_stmt} := by\n"
        repair_code += have_body + "\n  " + ct
        v, _ = check_proof(preamble, repair_code, "_decomp_repaired", project_dir=project_dir, timeout=cap())
        if v["ok"]:
            return ProofResult(proved=True, method="l3:decompose_repaired", error="", axioms=v["axioms"])
    return ProofResult(proved=False, method="", error="repair failed: " + combined.strip()[:200])


def prove_by_entailment(lean_code, unproved_spec, proved_specs, lean_checker):
    if not proved_specs:
        return None
    fn = _func_name(lean_code)
    u = unproved_spec["stmt"]
    single_tactics = ["intro h; simp [h]", "intro h; exact h", "intro h; tauto", "intro h; aesop"]
    for p in proved_specs:
        ent = f"({p['stmt']}) → ({u})"
        code = lean_code.rstrip() + f"\ntheorem _ent : {ent} := sorry"
        ok, _ = lean_checker.typecheck(code)
        if not ok:
            continue
        for tac in single_tactics:
            ok2, _ = _try_lean_proof(lean_code, ent, tac)
            if ok2:
                return f"entailment:{p['name']}"
    # conjunction (only when small set)
    if len(proved_specs) <= 6:
        conj_tactics = ["intro h1 h2; simp [h1, h2]", "intro h1 h2; tauto", "intro h1 h2; aesop"]
        if fn:
            conj_tactics.append(f"intro h1 h2; induction _ <;> simp [{fn}, h1, h2, *]")
        for i, p1 in enumerate(proved_specs):
            for p2 in proved_specs[i+1:]:
                ent = f"({p1['stmt']}) → ({p2['stmt']}) → ({u})"
                code = lean_code.rstrip() + f"\ntheorem _ent : {ent} := sorry"
                ok, _ = lean_checker.typecheck(code)
                if not ok:
                    continue
                for tac in conj_tactics:
                    ok2, _ = _try_lean_proof(lean_code, ent, tac)
                    if ok2:
                        return f"entailment:{p1['name']}+{p2['name']}"
    return None


def _write_debug(debug_dir, spec_name, attempt, prompt, response, lean_env, stmt, proof, lean_out, proved):
    if not debug_dir:
        return
    os.makedirs(debug_dir, exist_ok=True)
    path = os.path.join(debug_dir, f"{spec_name}_attempt_{attempt}.txt")
    lines = [l.strip() for l in proof.splitlines() if l.strip()]
    indented = "\n".join("  " + l for l in lines)
    full_lean = lean_env.rstrip() + f"\ntheorem _t : {stmt} := by\n{indented}"
    result_str = "proved" if proved else f"failed: {lean_out[:200]}"
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"=== PROMPT ===\n{prompt}\n")
        f.write(f"=== LLM RESPONSE ===\n{response}\n")
        f.write(f"=== LEAN CODE ===\n{full_lean}\n")
        f.write(f"=== LEAN OUTPUT ===\n{lean_out}\n")
        f.write(f"=== RESULT ===\n{result_str}\n")


def _try_proof_sketch(llm, lean_code, spec):
    prompt = (
        f"lean 4 context:\n{lean_code}\n\n"
        f"theorem to prove:\n{spec['stmt']}\n\n"
        "give only the high-level proof strategy with sorry for each goal. "
        "do not prove anything, just outline the structure. "
        "example:\n  induction n\n  · sorry\n  · sorry\n"
        "return only the tactic body (what goes after 'by')."
    )
    sketch = llm._ask(prompt).strip()
    m = re.search(r'```\w*\s*([\s\S]*?)```', sketch)
    if m:
        sketch = m.group(1).strip()
    sketch = sketch.removeprefix("by").strip()
    sketch = _strip_prose(sketch)
    if not sketch or "sorry" not in sketch:
        return
    for tactic in TACTICS:
        filled = sketch.replace("sorry", tactic)
        ok, _ = _try_lean_proof(lean_code, spec["stmt"], filled)
        if ok:
            spec["status"] = "proved"
            spec["method"] = f"sketch+{tactic}"
            return
    # phase 2: per-sorry targeted filling
    sorries = list(re.finditer(r'\bsorry\b', sketch))
    fn = _func_name(lean_code)
    all_defs = re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code)
    helper_names = [d for d in all_defs if d != fn]
    sorry_goals = []
    for sm in sorries:
        probed = sketch[:sm.start()] + "done" + sketch[sm.end():]
        _, raw = _try_lean_proof(lean_code, spec["stmt"], probed)
        parsed = _parse_lean_error(raw)
        sorry_goals.append(parsed if parsed["kind"] == "unsolved_goals" else None)
    fillers = []
    for sm, parsed_goal in zip(sorries, sorry_goals):
        filler = None
        if parsed_goal and parsed_goal.get("goals"):
            g = parsed_goal["goals"][0]
            case = g.get("case", "")
            hyps = g.get("hyps", "") or "none"
            target = g.get("target", "")
            fn_str = (fn + (f", {', '.join(helper_names)}" if helper_names else "")) if fn else ""
            tgt_prompt = (
                "You are filling one hole in a Lean 4 proof sketch.\n"
                f"Function:\n{lean_code}\n\n"
                f"Theorem: {spec['stmt']}\n"
                + (f"Case: {case}\n" if case else "")
                + f"Hypotheses:\n{hyps}\n"
                f"Goal: ⊢ {target}\n"
                + (f"Relevant functions: {fn_str}\n" if fn_str else "")
                + "Write ONLY the tactics to close this specific goal. No surrounding code."
            )
            raw_tactic = llm._ask(tgt_prompt).strip()
            m2 = re.search(r'```\w*\s*([\s\S]*?)```', raw_tactic)
            if m2:
                raw_tactic = m2.group(1).strip()
            raw_tactic = raw_tactic.removeprefix("by").strip()
            raw_tactic = _strip_prose(raw_tactic)
            if raw_tactic and "sorry" not in raw_tactic:
                test = sketch[:sm.start()] + raw_tactic + sketch[sm.end():]
                ok, _ = _try_lean_proof_partial(lean_code, spec["stmt"], test)
                if ok:
                    filler = raw_tactic
        if filler is None:
            for tac in TACTICS:
                test = sketch[:sm.start()] + tac + sketch[sm.end():]
                ok, _ = _try_lean_proof_partial(lean_code, spec["stmt"], test)
                if ok:
                    filler = tac
                    break
        fillers.append(filler)
    if all(f is not None for f in fillers):
        result = sketch
        offset = 0
        for sm, filler in zip(sorries, fillers):
            start = sm.start() + offset
            end = sm.end() + offset
            result = result[:start] + filler + result[end:]
            offset += len(filler) - len("sorry")
        ok, _ = _try_lean_proof(lean_code, spec["stmt"], result)
        if ok:
            spec["status"] = "proved"
            spec["method"] = "sketch+targeted"


def _classify_proof_error(error_text, spec_stmt):
    unknown_match = re.search(r"unknown identifier '([^']+)'", error_text)
    if unknown_match:
        ident = unknown_match.group(1)
        if ident in spec_stmt:
            return "spec_malformed"
    if "type mismatch" in error_text:
        if "theorem" in error_text.split("type mismatch")[0][-100:]:
            return "spec_malformed"
    goal_count = error_text.count("unsolved goals") + error_text.count("⊢")
    if goal_count <= 2:
        return "proof_close"
    elif goal_count > 2:
        return "proof_far"
    return "unknown"


def _llm_repair(llm, lean_code, spec, prev_proofs=None, verbose=False, debug_dir=None):
    _try_proof_sketch(llm, lean_code, spec)
    if spec["status"] == "proved":
        return
    fn = _func_name(lean_code)
    failed = list(prev_proofs) if prev_proofs else []
    attempt = 0
    # first proof attempt
    proof = llm.generate_proof(lean_code, spec["stmt"], func_name=fn, prev_proofs=failed)
    dbg_p = llm._last_prompt
    dbg_r = llm._last_response
    ok, raw = _try_lean_proof(lean_code, spec["stmt"], proof)
    attempt += 1
    _write_debug(debug_dir, spec["name"], attempt, dbg_p, dbg_r,
                 lean_code, spec["stmt"], proof, raw, ok)
    if verbose:
        status = "PROVED" if ok else f"FAIL: {raw[:100]}"
        print(f"  [llm] {spec['name']}: attempt {attempt} {status}")
        if not ok:
            print(f"  [llm] proof: {proof[:200]}")
    if ok:
        spec["status"] = "proved"
        spec["method"] = "llm"
        return
    failed.append((proof, raw))
    # classify after first failure
    classification = _classify_proof_error(raw, spec["stmt"])
    if classification == "spec_malformed":
        if verbose:
            print(f"  [skip] {spec['name']}: spec itself is malformed, skipping further proof attempts")
        return
    max_repairs = 4 if classification == "proof_close" else 2
    # blame-repair
    for r_i in range(max_repairs):
        parsed = _parse_lean_error(raw)
        proof = llm.repair_proof(lean_code, spec["stmt"], parsed, func_name=fn, prev_proofs=failed)
        dbg_p = llm._last_prompt
        dbg_r = llm._last_response
        ok, raw = _try_lean_proof(lean_code, spec["stmt"], proof)
        attempt += 1
        _write_debug(debug_dir, spec["name"], attempt, dbg_p, dbg_r,
                     lean_code, spec["stmt"], proof, raw, ok)
        if verbose:
            status = "PROVED" if ok else f"FAIL: {raw[:100]}"
            print(f"  [llm] {spec['name']}: repair {r_i+1} {status}")
            if not ok:
                print(f"  [llm] proof: {proof[:200]}")
        if ok:
            spec["status"] = "proved"
            spec["method"] = "llm"
            return
        failed.append((proof, raw))
    # calc-mode proof attempt
    calc = llm.generate_calc_proof(lean_code, spec["stmt"], func_name=fn)
    if calc:
        dbg_p = llm._last_prompt
        dbg_r = llm._last_response
        ok, raw = _try_lean_proof(lean_code, spec["stmt"], calc)
        attempt += 1
        _write_debug(debug_dir, spec["name"], attempt, dbg_p, dbg_r,
                     lean_code, spec["stmt"], calc, raw, ok)
        if verbose:
            print(f"  [calc] {spec['name']}: {'PROVED' if ok else 'FAIL'}")
        if ok:
            spec["status"] = "proved"
            spec["method"] = "llm-calc"
            return
    spec["status"] = "unproved"

def _verdict(spec, **fields):
    """one verdict event for spec, always with the statement it was decided on."""
    events.emit("verdict", stmt=spec["stmt"], **fields)


_DEF_START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s+([^\s:({\[]+)", re.M)
_HELPER_NAME = re.compile(r"^lss_hp_\w+_[0-9a-f]{8}$")


def rust_helpers(preamble, stmt):
    """(helpers, stmt) for a Rust spec: the preamble's `def` blocks only, each named
    `lss_hp_<name>_<8 hex of its text's sha256>` in every helper and in the statement,
    so two specs with the same helper share one name and two different ones never
    clash in the crate's env, and each tagged @[simp], as Aeneas's tutorial tags its
    toList, so simp unfolds it in proofs. they stay computable: the bounded check
    evaluates them."""
    starts = [m for m in _DEF_START.finditer(preamble or "")]
    blocks = []
    for i, m in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else len(preamble)
        text = preamble[m.start():end]
        # a block ends at the first later top-level line that is no part of it
        lines = text.splitlines()
        keep = [lines[0]] + list(itertools.takewhile(
            lambda ln: not ln.strip() or ln[:1].isspace() or ln.lstrip().startswith("|"), lines[1:]))
        blocks.append((m.group(1), "\n".join(keep).rstrip()))
    if not blocks:
        return "", stmt
    names = {}

    def rename(text):
        for old, new in names.items():
            text = re.sub(rf"(?<![\w.']){re.escape(old)}(?![\w'])", new, text)
        return text
    out = []
    for n, t in blocks:
        t = re.sub(r"^@\[[^\]]*\]\s*", "", t)
        t = re.sub(r"^(?:(?:private|protected|noncomputable)\s+)*", "", t)
        t = rename(t)  # the helpers before it, by their new names: the hash covers what it calls
        if not _HELPER_NAME.match(n):  # a helper copied from a callee's spec keeps its name
            names[n] = f"lss_hp_{re.sub(r'[^A-Za-z0-9_]', '_', n)}_{hashlib.sha256(t.encode('utf-8')).hexdigest()[:8]}"
        t = re.sub(r"^abbrev\s", "def ", t)
        out.append("@[simp] " + rename(t))
    return "\n\n".join(out), rename(stmt)


def validate(specs, lean_code, test_inputs, lean_checker, llm=None, func_name=None, verbose=False, debug_dir=None, project_dir=None, func_source=None, source=None):
    func = func_name or _func_name(lean_code)

    processed_stmts = set()

    with events.context(stage="validate", source=source or "lean-native"):
        for spec_idx, spec in enumerate(specs):
            with events.context(candidate_id=spec["name"]):
                if _gate.is_rust(source):
                    # the gate's normal form: the call on distinct variables, any other
                    # argument defined by a hypothesis (an equivalent statement)
                    spec["stmt"] = normalize_call(spec["stmt"], func)
                stmt_norm = _normalize_stmt(spec["stmt"])
                if stmt_norm in processed_stmts:
                    spec["status"] = "rejected"
                    spec["fail_gate"] = "dedup"
                    if verbose:
                        print(f"  [dedup] skipping duplicate in validate: {spec['name']}")
                    _verdict(spec, status="rejected", method="", fail_gate="dedup")
                    continue
                processed_stmts.add(stmt_norm)
                preamble = spec.get("preamble", "")
                if preamble and _gate.is_rust(source):
                    # a Rust spec's helpers: named by their text, @[simp], computable, and
                    # defined once in the crate's env, after the crate is opened
                    helpers, stmt_h = rust_helpers(preamble, spec["stmt"])
                    preamble = ""
                    if helpers:
                        ok_pre, errs_pre = lean_checker.ensure_helpers(project_dir, helpers)
                        if ok_pre:
                            spec["helpers"], spec["stmt"] = helpers, stmt_h
                        elif verbose:
                            print(f"  [pre] {spec['name']}: helper typecheck FAIL: {errs_pre[0][:80] if errs_pre else 'unknown'}")
                if _gate.is_rust(source) and hasattr(lean_checker, "known_helpers"):
                    # helpers a callee's proved spec defined and this statement reuses (its
                    # prompt shows them): the gate and the bounded check start from the crate
                    # env as built, so they get them as text too
                    reused = lean_checker.known_helpers(project_dir, spec["stmt"] + "\n" + spec.get("helpers", ""))
                    own = spec.get("helpers", "")
                    extra = "\n\n".join(b for b in reused.split("\n\n") if b and b not in own)
                    if extra:
                        spec["helpers"] = extra + ("\n\n" + own if own else "")
                if preamble:
                    preamble_clean = "\n".join(
                        line for line in preamble.split("\n")
                        if not line.strip().startswith("import") and not line.strip().startswith("open")
                    )
                    if preamble_clean.strip():
                        # the LLM's helper definitions only state the spec, never run: a
                        # helper that calls a function Lean cannot compile (an opaque
                        # crate function) is marked noncomputable, as it was inside the
                        # crate's own noncomputable section
                        preamble_clean = "noncomputable section\n" + preamble_clean.strip() + "\nend"
                        ok_pre, errs_pre = lean_checker.typecheck(lean_code.rstrip() + "\n" + preamble_clean, project_dir=project_dir)
                        if not ok_pre:
                            if verbose:
                                print(f"  [pre] {spec['name']}: preamble typecheck FAIL: {errs_pre[0][:80] if errs_pre else 'unknown'}")
                            preamble = ""
                        else:
                            preamble = preamble_clean
                    else:
                        preamble = ""
                # a Rust spec's helpers are already in its crate's env, where its text runs
                eff = lean_code.rstrip() + "\n" + preamble if preamble else lean_code

                # gate 1: well-formedness gate (shape, vocabulary, decidability -
                # replaces the old bare typecheck; a candidate that passes it is
                # already known to typecheck, since the gate elaborates it for real)
                candidate_text = f"theorem {spec['name']} : {spec['stmt']} := sorry"
                verdicts = _gate.check_candidate(lean_checker, candidate_text, func, eff, project_dir, source,
                                                  helpers=spec.get("helpers", ""))
                ok = _gate.is_well_formed(verdicts, source)
                if _gate.failing_check(verdicts) == "env":
                    # the crate/base environment never came up -- a setup error,
                    # not anything about this candidate, so no amount of LLM
                    # repair can fix it. fail loudly instead of burning a retry.
                    detail = next((v["detail"] for v in verdicts if not v.get("ok")), "")
                    raise RuntimeError(f"well-formedness gate environment unavailable: {detail}")
                if not ok and llm and spec.get("_g1_retries", 0) < 1:
                    spec["_g1_retries"] = 1
                    bad_check = _gate.failing_check(verdicts)
                    detail = next((v["detail"] for v in verdicts if not v.get("ok")), "")
                    fix_prompt = (
                        f"This Lean 4 theorem failed the well-formedness gate:\n"
                        f"  {candidate_text}\n\n"
                        f"Failing check: {bad_check}\n"
                        f"Detail: {detail}\n\n"
                        f"Function it is about:\n{func_source if func_source else lean_code}\n\n"
                        f"Fix the theorem statement so it passes the gate. Common fixes:\n"
                        f"- wrong argument count: check the function signature\n"
                        f"- undefined name: use the exact names from the function definition\n"
                        f"- type mismatch: match the exact types in the function signature\n"
                        f"- missing precondition parameter: include (h : f_precond args) if the function has one\n"
                        f"- conclusion_shape: the conclusion must apply the function to its own distinct bound variables, exactly once\n"
                        f"- vocabulary: the postcondition may not name the unit itself or any other crate function outside the call\n"
                        f"- decidable: use a decidable postcondition (avoid unbounded quantifiers)\n\n"
                        f"Return ONLY the fixed theorem line: theorem name : fixed_statement := sorry"
                    )
                    fixed = llm._ask(fix_prompt)
                    if fixed:
                        fm = theorems(fixed)
                        if fm:
                            spec["stmt"] = (normalize_call(fm[0][1], func) if _gate.is_rust(source)
                                            else fm[0][1])
                            candidate_text = f"theorem {spec['name']} : {spec['stmt']} := sorry"
                            verdicts = _gate.check_candidate(lean_checker, candidate_text, func, eff, project_dir, source,
                                                  helpers=spec.get("helpers", ""))
                            if _gate.is_well_formed(verdicts, source):
                                ok = True
                                if verbose:
                                    print(f"  [g1] {spec['name']}: fixed stmt passes the gate")
                spec["wf_verdicts"] = verdicts
                if verbose:
                    if ok:
                        print(f"  [g1] {spec['name']}: wf gate pass")
                    else:
                        fail_detail = next((v["detail"] for v in verdicts if not v.get("ok")), "")
                        print(f"  [g1] {spec['name']}: wf gate FAIL: {_gate.failing_check(verdicts)}: {fail_detail[:80]}")
                if not ok:
                    spec["status"] = "rejected"
                    spec["fail_gate"] = "g1"
                    spec["wf_fail_check"] = _gate.failing_check(verdicts)
                    if verbose:
                        print(f"         stmt: {spec['stmt'][:100]}")
                    _verdict(spec, status="rejected", method="", fail_gate="g1",
                                check=spec["wf_fail_check"],
                                detail=next((v["detail"] for v in verdicts if not v.get("ok")), "")[:300])
                    continue

                # bounded check (rust units): run the spec on sampled inputs before any
                # prover. a false spec is refuted with its shrunk witness, a vacuous
                # one rejected, and either gets one repair from the counterexample; a
                # narrow precondition only warns, and a timeout goes on to the provers.
                if _gate.is_rust(source) and func:
                    b = _bounded.check_spec(lean_checker, spec["stmt"], func, project_dir, helpers=spec.get("helpers", ""))
                    spec["bounded"] = b
                    events.emit("bounded", status=b["status"], warning=b.get("warning"),
                                detail=(b.get("detail") or "")[:300], kernel=b.get("kernel"))
                    if verbose:
                        print(f"  [b] {spec['name']}: {b['status']}"
                              + (f" ({b['warning']})" if b.get("warning") else ""))
                    if b["status"] in ("refuted", "vacuous"):
                        if llm and not spec.get("_b_repaired"):
                            fixed = llm._ask(
                                f"This Lean 4 theorem about a Rust function (translated by Aeneas) is wrong:\n"
                                f"  theorem {spec['name']} : {spec['stmt']}\n\n{b['feedback']}\n\n"
                                f"Function it is about:\n{func_source if func_source else lean_code}\n\n"
                                f"Fix the statement so it is true of the function and still says what it computes.\n"
                                f"Return ONLY the fixed theorem line: theorem name : fixed_statement := sorry")
                            fm = theorems(fixed)
                            if fm:
                                specs.append({"name": spec["name"] + "_r", "stmt": fm[0][1],
                                              "preamble": spec.get("preamble", ""), "helpers": spec.get("helpers", ""),
                                              "_b_repaired": True})
                        spec["status"] = "refuted" if b["status"] == "refuted" else "rejected"
                        spec["fail_gate"] = b["status"]
                        if b["status"] == "refuted":
                            spec["refuted_by"] = "kernel" if b["kernel"] else "evaluation"
                        _verdict(spec, status=spec["status"], method="bounded", fail_gate=b["status"],
                                **{k: b[k] for k in ("witness", "outcome", "value", "instantiation", "kernel", "feedback")
                                   if k in b})
                        continue

                # gate 4a: aeneas tactic layer, rust units only
                if source == "rust-aeneas" and _lss_config.proof_cfg()["aeneas_layer"]:
                    pr0 = lean_checker.try_aeneas(spec["stmt"], func, project_dir, candidate_id=spec["name"])
                    if pr0.blamed_callees:
                        spec["blamed_callees"] = pr0.blamed_callees
                    if pr0.proved:
                        spec["status"] = "proved"
                        spec["method"] = pr0.method
                        spec["proof"] = pr0.proof_text
                        spec["axioms"] = pr0.axioms
                        spec["modular"] = pr0.modular
                        spec["needs_callee_body"] = pr0.needs_callee_body
                        if verbose:
                            print(f"  [g4] {spec['name']}: proved (aeneas) by {pr0.method}")
                        _verdict(spec, status="proved", method=pr0.method)
                        continue

                # gate 4: three-layer proof search
                # layer 1: mathlib tactic portfolio
                pr = lean_checker.try_proof(eff, spec["stmt"], func_name=func, project_dir=project_dir)
                if pr.proved:
                    spec["status"] = "proved"
                    spec["method"] = pr.method
                    spec["axioms"] = pr.axioms
                    if verbose:
                        print(f"  [g4] {spec['name']}: proved (l1) by {pr.method}")
                    _verdict(spec, status="proved", method=pr.method)
                    continue

                # layer 2: hammer (60s timeout)
                pr2 = lean_checker.try_hammer(eff, spec["stmt"], project_dir=project_dir)
                if pr2.proved:
                    spec["status"] = "proved"
                    spec["method"] = pr2.method
                    spec["axioms"] = pr2.axioms
                    if verbose:
                        print(f"  [g4] {spec['name']}: proved (l2) by {pr2.method}")
                    _verdict(spec, status="proved", method=pr2.method)
                    continue

                # layer 3: auxiliary-lemma decomposition
                if llm:
                    r3 = decompose_and_prove(eff, spec["stmt"], lean_checker, llm, project_dir=project_dir,
                                             func_source=func_source)
                    if r3.proved:
                        spec["status"] = "proved"
                        spec["method"] = r3.method
                        spec["axioms"] = r3.axioms
                        if verbose:
                            print(f"  [g4] {spec['name']}: proved (l3) by {r3.method}")
                        _verdict(spec, status="proved", method=r3.method)
                        continue

                if verbose:
                    print(f"  [g4] {spec['name']}: all layers failed, unproved")
                spec["status"] = "unproved"
                _verdict(spec, status="unproved", method="")  # the statement is kept for replaying closers

    # pbt: final check for unproved specs
    for spec in specs:
        if spec["status"] in ("proved", "rejected", "refuted"):
            continue
        preamble = spec.get("preamble", "")
        eff_pbt = lean_code.rstrip() + "\n" + preamble if preamble else lean_code
        pr_pbt = lean_checker.run_pbt(eff_pbt, spec["stmt"])
        if pr_pbt.counterexample:
            spec["status"] = "rejected"
            spec["fail_gate"] = "pbt"
            if verbose:
                print(f"  [pbt] {spec['name']}: FAIL counterexample found")
            with events.context(candidate_id=spec["name"]):
                _verdict(spec, status="rejected", method="", fail_gate="pbt")
        elif verbose:
            print(f"  [pbt] {spec['name']}: pass")

    return specs


_LEAN_KEYWORDS = {
    "if", "then", "else", "match", "with", "let", "where", "return", "do",
    "fun", "have", "show", "by", "true", "false", "some", "none", "in",
    "def", "theorem", "lemma", "inductive", "structure", "class",
    "instance", "deriving", "and", "or", "not",
}


def _mech_obligations(lean_code):
    # last def is main function; earlier ones are helpers
    def_names = re.findall(r'\bdef\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_code)
    func_name = def_names[-1] if def_names else ""
    helper_set = set(def_names[:-1]) if len(def_names) > 1 else set()

    # all | arm lines in lean_code
    arm_lines = [l for l in lean_code.split('\n') if re.match(r'^\s*\|', l)]

    # body of last def: text after its :=, or full trailing text if pattern-matching style
    body = lean_code
    if func_name:
        # use (?!\w) instead of \b so names ending in ' are found correctly
        for m in re.finditer(r'\bdef\s+' + re.escape(func_name) + r'(?!\w)', lean_code):
            after = lean_code[m.end():]
            sep = after.find(':=')
            body = after[sep + 2:] if sep != -1 else after

    fn_pat = r'(?<!\w)' + re.escape(func_name) + r'(?!\w)' if func_name else None

    # helpers: known def names called in last def's body
    idents = set(re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_\'!?]*)\b', body))
    helpers = sorted((idents - _LEAN_KEYWORDS - {func_name}) & helper_set)

    # recursion: func_name appears in its own body
    func_recursive = bool(fn_pat and re.search(fn_pat, body))

    if_count = len(re.findall(r'\bif\b', body))

    obligations = []
    if arm_lines:
        for i, arm in enumerate(arm_lines):
            after_arrow = arm.split('=>', 1)[1] if '=>' in arm else ""
            arm_recursive = bool(fn_pat and re.search(fn_pat, after_arrow))
            arm_helpers = [h for h in helpers if h in after_arrow]
            obligations.append({
                "case": f"arm_{i + 1}: {arm.strip()}",
                "is_base": not arm_recursive,
                "is_recursive": arm_recursive,
                "helpers": arm_helpers,
                "properties": [],
                "depends_on": arm_helpers,
            })
    elif if_count > 0:
        for i in range(if_count):
            obligations.append({
                "case": f"if_branch_{i + 1}",
                "is_base": not func_recursive,
                "is_recursive": func_recursive,
                "helpers": helpers,
                "properties": [],
                "depends_on": helpers,
            })
    else:
        obligations.append({
            "case": "body",
            "is_base": not func_recursive,
            "is_recursive": func_recursive,
            "helpers": helpers,
            "properties": [],
            "depends_on": helpers,
        })

    if func_recursive:
        obligations.append({
            "case": "termination",
            "is_base": False,
            "is_recursive": True,
            "helpers": [],
            "properties": ["well-founded termination"],
            "depends_on": [],
        })

    return obligations, func_name, helpers


def plan_obligations(lean_code, llm):
    obligations, func_name, helpers = _mech_obligations(lean_code)

    n_arms = sum(1 for o in obligations if o["case"].startswith("arm_"))
    n_recursive = sum(1 for o in obligations if o["is_recursive"])
    helpers_str = ", ".join(helpers) if helpers else "none"

    prompt = (
        f"Analyze this Lean 4 function and identify what properties should be proved:\n\n"
        f"```lean\n{lean_code}\n```\n\n"
        f"The function has:\n"
        f"- {n_arms} pattern match arms\n"
        f"- {n_recursive} recursive calls\n"
        f"- helpers: {helpers_str}\n\n"
        f"For EACH match arm, list 1-2 specific properties that should hold.\n"
        f"For the overall function, list 3-5 key properties.\n"
        f"Be SPECIFIC — not 'output is correct' but 'output.length = input.length'.\n\n"
        f"Return a ```json array where each item has 'case' and 'properties' fields."
    )
    raw = llm._ask(prompt)
    m = re.search(r'```(?:json)?\s*([\s\S]*?)```', raw)
    text = m.group(1).strip() if m else raw.strip()
    try:
        enriched = json.loads(text)
        if isinstance(enriched, list) and all(isinstance(o, dict) and "case" in o for o in enriched):
            return enriched
    except Exception:
        pass
    return obligations


def generate_from_plan(obligations, lean_code, llm, existing_specs=None):
    specs = []
    proved_names = [s["name"] for s in (existing_specs or [])]
    func_name = _func_name(lean_code)
    for ob in obligations:
        prompt = (
            f"Generate theorem statements for this case of the function: {ob['case']}.\n"
            f"Expected properties: {', '.join(ob.get('properties', []))}.\n"
            f"Already proved (do not duplicate): {', '.join(proved_names) if proved_names else 'none'}.\n\n"
            f"Function:\n```lean\n{lean_code}\n```\n\n"
        )
        ml_examples = llm._retrieve_mathlib_examples(lean_code, func_name)
        if ml_examples:
            prompt += "Similar Mathlib theorems for reference:\n" + "\n".join(ml_examples[:3]) + "\n\n"
        prompt += (
            "Write 1-3 theorems. Use ∀ quantifiers. One property per theorem.\n"
            "Each theorem must reference the function in its conclusion.\n"
            "Format: theorem name : statement := sorry\n"
            "Return only a ```lean code block."
        )
        text = llm._ask(prompt)
        m = re.search(r'```\w*\s*([\s\S]*?)```', text)
        if not m:
            continue
        for name, stmt, _ in theorems(m.group(1)):
            specs.append({"name": name, "stmt": stmt, "status": "pending", "method": ""})
    return specs


_TYPE_PREDS = {
    "List":   "List.length, List.Perm, List.Sorted, List.Nodup, List.mem, List.head?, List.last?, List.reverse, List.filter, List.map",
    "Array":  "Array.size, Array.get, Array.set, Array.push, Array.data, Array.toList",
    "Nat":    ">, <, >=, <=, +, -, *, /, %, Nat.dvd, Even, Odd, Nat.Prime, Nat.gcd",
    "Int":    ">, <, >=, <=, +, -, *, Int.natAbs",
    "Bool":   "decide, Decidable, true, false, &&, ||",
    "Option": "Option.isSome, Option.isNone, Option.get!, Option.map, Option.bind",
    "Prod":   "Prod.fst, Prod.snd",
    "String": "String.length, String.append, String.contains",
}

def auto_templates(lean_code):
    types_seen = []
    seen = set()

    def _add(t):
        if t not in seen:
            seen.add(t)
            types_seen.append(t)

    for t in ("List", "Array", "Option", "String", "Bool", "Int", "Nat"):
        if re.search(r'\b' + t + r'\b', lean_code):
            _add(t)
    if re.search(r'×|Prod\b', lean_code):
        _add("Prod")
    for m in re.finditer(r'\binductive\s+([A-Z]\w*)', lean_code):
        _add(m.group(1))

    return [f"{t}: {_TYPE_PREDS.get(t, 'membership, structure preservation')}" for t in types_seen]


def _normalize_stmt(stmt):
    s = re.sub(r'\s+', ' ', stmt.strip())
    s = re.sub(r'\b[a-z]\b', '_', s)
    return s


def _admit_with_proof(gwp, specs, lean_code, fn, lean_checker, project_dir, source, verbose=False):
    """add the statements the LLM proved itself to specs: each passes the same
    well-formedness gate as every other candidate (one theorem about the function,
    in the function's own vocabulary), then gate 3; its kernel-checked proof is kept."""
    wrong = _make_wrong(lean_code, fn) or _replace_body(lean_code)
    for s in gwp:
        with events.context(stage="validate", candidate_id=s["name"]):
            verdicts = _gate.check_candidate(lean_checker, f"theorem {s['name']} : {s['stmt']} := sorry",
                                             fn, lean_code, project_dir, source)
            if _gate.failing_check(verdicts) == "env":  # a setup error, as in validate: never a verdict
                raise RuntimeError("well-formedness gate environment unavailable: "
                                   + next((v["detail"] for v in verdicts if not v.get("ok")), ""))
            if not _gate.is_well_formed(verdicts, source):
                _verdict(s, status="rejected", method="", fail_gate="g1", check=_gate.failing_check(verdicts),
                            detail=next((v["detail"] for v in verdicts if not v.get("ok")), "")[:300])
                if verbose:
                    print(f"  [gwp] {s['name']}: wf gate FAIL: {_gate.failing_check(verdicts)}")
                continue
            if lean_checker.try_proof(wrong, s["stmt"]).proved:
                continue
            _verdict(s, status="proved", method=s["method"])
        existing = next((x for x in specs if x["stmt"] == s["stmt"]), None)
        if existing:  # the same statement, failed or unproved elsewhere: proved now, by this proof
            for k in ("fail_gate", "refuted_by", "bounded", "wf_fail_check"):
                existing.pop(k, None)
            existing.update({k: v for k, v in s.items() if k not in ("name", "status")})
            existing["status"] = "proved"
        else:
            specs.append(s)


def synthesize(lean_code, test_inputs, templates, llm, lean_checker,
               use_obligations=False, func_name=None, verbose=False, debug_dir=None, postcond_defs=None, project_dir=None, func_source=None, source=None):
    fn = func_name or _func_name(lean_code)
    with events.context(func=fn, stage="generate"):
        if not templates:
            templates = auto_templates(lean_code)
        if use_obligations:
            obligations = plan_obligations(lean_code, llm)
            specs = generate_from_plan(obligations, lean_code, llm)
            gwp = []
        else:
            complexity = _classify_complexity(func_source or lean_code, fn)
            if verbose:
                print(f"  [gen] function complexity: {complexity}")
            behavior_specs = []
            if complexity == "hard" and fn and test_inputs:
                io_pairs = []
                for inp in test_inputs[:8]:
                    out = lean_checker.eval_expr(f"{fn} {inp}", prelude=func_source or lean_code)
                    if out:
                        io_pairs.append(f"  {fn} {inp} = {out}")
                if io_pairs:
                    sig_str = _get_signature_string(func_source or lean_code, fn)
                    behavior_prompt = (
                        f"A Lean 4 function with this signature:\n"
                        f"  def {fn} {sig_str}\n\n"
                        f"Observed behavior:\n" + "\n".join(io_pairs) + "\n\n"
                        "Write 10 theorems about the pattern in this input-output behavior.\n"
                        "Do NOT reference internal implementation details.\n"
                        "Focus on: bounds, base cases, monotonicity, relationship between input size and output.\n"
                        "Format: theorem name : ∀ (args), statement := sorry\n"
                        "Return only a ```lean code block."
                    )
                    behavior_specs = llm.generate_specs_raw(behavior_prompt)
                    if behavior_specs and verbose:
                        print(f"  [gen] behavior-first produced {len(behavior_specs)} candidates (hard function)")
            if verbose:
                print("  [gen] running strategy: direct")
            specs = llm.generate_specs(lean_code, templates, func_name=func_name, postcond_defs=postcond_defs, func_source=func_source)
            if behavior_specs:
                specs.extend(behavior_specs)
            if verbose:
                print(f"  [gen] direct produced {len(specs)} candidates")
            gwp = []
            if func_name and test_inputs:
                if verbose:
                    print("  [gen] running strategy: examples")
                ex = generate_from_examples(func_source or lean_code, func_name, test_inputs, lean_checker, llm)
                if verbose:
                    print(f"  [gen] examples produced {len(ex)} candidates")
                if verbose:
                    print("  [gen] running strategy: negatives")
                neg = generate_from_negatives(func_source or lean_code, func_name, test_inputs, lean_checker, llm)
                if verbose:
                    print(f"  [gen] negatives produced {len(neg)} candidates")
                gwp = generate_with_proof(func_source or lean_code, func_name, llm, lean_checker, project_dir=project_dir)
                # strategy: program slicing (SLD-Spec methodology)
                if func_name:
                    from strategies import generate_from_slices
                    slice_specs = generate_from_slices(
                        lean_code, func_name, llm, lean_checker, verbose=verbose,
                        project_dir=project_dir, func_source=func_source)
                    if slice_specs:
                        if verbose:
                            print(f"  [gen] slicing produced {len(slice_specs)} candidates")
                        specs.extend(slice_specs)
                seen_stmts = set()
                deduped = []
                for s in specs:
                    k = s["stmt"].strip()
                    if k not in seen_stmts:
                        seen_stmts.add(k)
                        deduped.append(s)
                    elif verbose:
                        print(f"  [dedup] dropped exact duplicate: {s['name']}")
                specs = deduped
                seen_norm = {_normalize_stmt(s["stmt"]) for s in specs}
                for s in ex + neg:
                    norm = _normalize_stmt(s["stmt"])
                    if norm not in seen_norm:
                        seen_norm.add(norm)
                        specs.append(s)
                if verbose:
                    print(f"  [gen] total after merge+dedup: {len(specs)}")

            # strategy: failure-freedom (aeneas Result functions)
            # runs without test_inputs; final dedup handles duplicates with other strategies
            # TODO: complexity classification can gate this strategy by complexity level
            if func_name and "Result" in (func_source or lean_code):
                from strategies import generate_failure_freedom
                ff_specs = generate_failure_freedom(
                    lean_code, func_name, llm, lean_checker,
                    verbose=verbose, project_dir=project_dir, func_source=func_source)
                if ff_specs:
                    if verbose:
                        print(f"  [gen] failure-freedom produced {len(ff_specs)} candidates")
                    specs.extend(ff_specs)

        specs = validate(specs, lean_code, test_inputs, lean_checker,
                         llm=llm, func_name=func_name, verbose=verbose,
                         debug_dir=debug_dir, project_dir=project_dir, func_source=func_source, source=source)

        # round 2: SpecGen-style mutation-guided repair (not raw error messages)
        g1_fails = [s for s in specs if s.get("fail_gate") == "g1"]
        if g1_fails and len(g1_fails) <= 15:
            repaired = []

            for failed_spec in g1_fails[:5]:
                stmt = failed_spec["stmt"]
                mutations = []

                args_in_stmt = re.findall(r'\((\w+)\s*:\s*[^)]+\)', stmt)
                for arg in args_in_stmt:
                    mutated = re.sub(rf'\({arg}\s*:\s*[^)]+\)\s*', '', stmt)
                    mutations.append(("remove_arg_" + arg, mutated))

                for old_t, new_t in [("Int", "Nat"), ("Nat", "Int"), ("Array", "List"), ("List", "Array")]:
                    if old_t in stmt:
                        mutations.append(("swap_type_" + old_t, stmt.replace(old_t, new_t, 1)))

                if "_precond" not in stmt:
                    forall_match = re.match(r'∀\s*(\([^)]+\)(?:\s*\([^)]+\))*)', stmt)
                    if forall_match:
                        first_arg = re.search(r'\((\w+)\s*:', stmt)
                        if first_arg:
                            arg_name = first_arg.group(1)
                            precond_insert = f"(h_precond : {fn}_precond {arg_name})"
                            insert_pos = forall_match.end()
                            mutated = stmt[:insert_pos] + f" {precond_insert}" + stmt[insert_pos:]
                            mutations.append(("add_precond", mutated))

                mutations.append(("add_namespace", stmt.replace(fn, fn)))

                working_mutation = None
                for mut_name, mut_stmt in mutations:
                    code = lean_code.rstrip() + f"\ntheorem _test : {mut_stmt} := sorry"
                    ok, _ = lean_checker.typecheck(code, project_dir=project_dir)
                    if ok:
                        working_mutation = (mut_name, mut_stmt)
                        if verbose:
                            print(f"  [repair] {failed_spec['name']}: mutation '{mut_name}' fixes typecheck")
                        break

                if working_mutation:
                    mut_name, mut_stmt = working_mutation
                    repaired.append({
                        "name": failed_spec["name"] + "_repaired",
                        "stmt": mut_stmt,
                        "status": "pending",
                        "method": None,
                        "preamble": failed_spec.get("preamble", ""),
                    })
                else:
                    mutation_insights = []
                    for mut_name, mut_stmt in mutations[:3]:
                        code = lean_code.rstrip() + f"\ntheorem _test : {mut_stmt} := sorry"
                        ok, errs = lean_checker.typecheck(code, project_dir=project_dir)
                        if errs:
                            mutation_insights.append(f"  tried {mut_name}: {errs[0][:60]}")

                    guided_prompt = (
                        f"This theorem failed to typecheck:\n"
                        f"  theorem {failed_spec['name']} : {stmt} := sorry\n\n"
                        f"I tried these mutations:\n" + "\n".join(mutation_insights) + "\n\n"
                        f"Function signature:\n  {_get_signature_string(func_source or lean_code, fn)}\n\n"
                        f"Write a FIXED version that typechecks. Return ONLY the theorem line."
                    )
                    fix_resp = llm._ask(guided_prompt)
                    if fix_resp:
                        m = theorems(fix_resp)
                        if m:
                            repaired.append({
                                "name": m[0][0],
                                "stmt": m[0][1],
                                "status": "pending",
                                "method": None,
                                "preamble": "",
                            })

            if repaired:
                repaired_validated = validate(repaired, lean_code, test_inputs, lean_checker,
                    llm=llm, func_name=func_name,
                    verbose=verbose, debug_dir=debug_dir, project_dir=project_dir,
                    func_source=func_source, source=source)
                new_proved = [s for s in repaired_validated if s["status"] == "proved"]
                specs.extend(new_proved)
                if verbose:
                    print(f"  [repair] mutation-guided: {len(repaired)} repaired, {len(new_proved)} proved")

        # round 3: if still low, generate safe/simple specs
        proved_count = sum(1 for s in specs if s["status"] == "proved")
        if proved_count < 3:
            safe_prompt = (
                f"I need simple theorems about this function that will definitely typecheck:\n"
                f"{func_source if func_source else lean_code}\n\n"
                f"Write 5 simple theorems: base cases, type preservation, trivial properties.\n"
                f"Every theorem must use ∀ quantifiers and will typecheck.\n"
            )
            round3 = llm.generate_specs_raw(safe_prompt)
            if round3:
                if verbose:
                    print(f"  [gen] round 3 produced {len(round3)} safe specs")
                round3_validated = validate(round3, lean_code, test_inputs, lean_checker,
                                            llm=llm, func_name=func_name,
                                            verbose=verbose, debug_dir=debug_dir, project_dir=project_dir,
                                            source=source)
                new_proved = [s for s in round3_validated if s["status"] == "proved"]
                specs.extend(new_proved)
                if verbose:
                    print(f"  [gen] round 3: {len(new_proved)} proved")

        if gwp and fn:
            _admit_with_proof(gwp, specs, lean_code, fn, lean_checker, project_dir, source, verbose)

        # dedup all specs after gwp merge using normalized comparison
        seen_final = set()
        deduped_final = []
        for s in specs:
            norm = _normalize_stmt(s["stmt"])
            if norm not in seen_final:
                seen_final.add(norm)
                deduped_final.append(s)
            elif verbose:
                print(f"  [dedup] dropped post-gwp duplicate: {s['name']}: {s['stmt'][:60]}")
        specs = deduped_final

        # second pass: last-resort proof for unproved specs
        if llm and fn:
            for spec in [s for s in specs if s["status"] == "unproved"]:
                prompt = (
                    f"this theorem is true but i cannot prove it:\n"
                    f"{lean_code}\n"
                    f"theorem {spec['name']} : {spec['stmt']} := sorry\n\n"
                    f"write a complete proof. no sorry allowed. the function is {fn}.\n"
                    f"try: induction, cases, simp [{fn}], or prove a helper theorem first.\n"
                    "return the full theorem with proof in a ```lean block."
                )
                text = llm._ask(prompt)
                m = re.search(r'```\w*\s*([\s\S]*?)```', text)
                if not m:
                    if verbose:
                        print(f"  [2nd] {spec['name']}: FAIL")
                    continue
                block = m.group(1).strip()
                # the block's theorems are checked as given; `_lss_second` restates the
                # spec itself, so a block that proved some other statement does not count
                v, _ = check_proof(lean_code, block + f"\ntheorem _lss_second : {spec['stmt']} := by\n"
                                   f"  exact {spec['name']}", "_lss_second", project_dir=project_dir)
                if v["ok"]:
                    spec["status"] = "proved"
                    spec["method"] = "llm-second-pass"
                    spec["axioms"] = v["axioms"]
                if verbose:
                    print(f"  [2nd] {spec['name']}: {'PROVED' if spec['status'] == 'proved' else 'FAIL'}")

        return specs

