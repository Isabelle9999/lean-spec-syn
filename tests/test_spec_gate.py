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


# the full candidate shapes below (unit applied directly in ⦃ r => P r ⦄ form) are
# exactly what synth.py's prompt now asks the LLM to emit -- see run_static's own
# checks on that prompt text, and synth.py:218-244.
# what synth.validate (strategies.normalize_call) makes of a call on a struct literal
RAW_SWAP = '∀ (a b : Std.U32), records.swap { first := a, second := b } ⦃ r => r.first = b ⦄'
NORMAL_SWAP = ('∀ (a b : Std.U32), ∀ (lss_a0 : _), lss_a0 = { first := a, second := b } → '
               'records.swap lss_a0 ⦃ r => r.first = b ⦄')
RUST_CASES = [
    ("correct spec passes every check", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, "")]),

    ("second theorem in one candidate -> one_theorem", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄ := sorry\n'
     'theorem another : True := trivial',
     [("one_theorem", False, "expected exactly one top-level command, found 2")]),

    ("wrong attribute -> no_attribute", "records.swap",
     '@[simp] theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", False, "attribute(s) present: [simp]")]),

    ("wrong declaration keyword (lemma) -> is_theorem", "records.swap",
     'lemma swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", False, "expected a `theorem` declaration, got `lemma`")]),

    ("conclusion on a concrete argument -> conclusion_shape", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap { first := p.first, second := p.first } ⦃ r => True ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", False, "argument `{ first := p.first, second := p.first }` is not a bound variable")]),

    ("equation form (old idiom), not a Hoare triple -> conclusion_shape", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p = ok { first := p.second, second := p.first } := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", False, "conclusion must be `f args ⦃ r => P r ⦄`")]),

    ("parse error -> one_theorem", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = ⦄ := sorry',
     [("one_theorem", False, "candidate does not parse: ...")]),

    ("type error in the postcondition -> conclusion_shape", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = p.nonexistent ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", False, "statement does not elaborate: ...")]),

    ("unknown name is an error, not a new bound variable -> conclusion_shape", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => r.first = no_such_value ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", False, "statement does not elaborate: Unknown identifier `no_such_value`...")]),

    ("postcondition names another crate function -> vocabulary", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => ∃ s, records.order_pair p = ok s ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", False, "forbidden crate name(s) used outside the program position: [FeatureSuite.records.order_pair]")]),

    ("postcondition restates the call, r = f x -> vocabulary", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => records.swap p = ok r ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", False, "forbidden crate name(s) used outside the program position: [FeatureSuite.records.swap]")]),

    ("non-decidable postcondition passes: the rust track has no decidable check "
     "(the bounded check decides a statement at its instantiation, or leaves it to the provers)", "records.swap",
     'theorem swap_spec (p : records.Pair) : records.swap p ⦃ r => ∃ g : Std.U32 -> Std.U32, g r.first = r.second ⦄ := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, "")]),

    ("a call on a constructor in the normal form python gives it passes", "records.swap",
     'theorem swap_spec : ' + NORMAL_SWAP + ' := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, "")]),

    ("⦃⦄div spec on a loop unit passes", "search.linear_search",
     'theorem linear_search_spec (values : Array Std.U32 8#usize) (target : Std.U32) : '
     'search.linear_search values target ⦃ r => True ⦄div := sorry',
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, "")]),
]

# native track: the manifest is the unit plus its own auxiliaries (read from the
# environment by wf_gate.lean), the conclusion starts at the first binder that
# calls the unit, and identical calls are one program position -- `(f x).1 <
# (f x).2` calls `f` twice with the same argument.
_NATIVE_LEAN_CODE = (
    "def f_precond (x : Nat) : Prop := x > 0\n"
    "def f (x : Nat) : Nat × Nat := (x, x + 1)\n"
)
NATIVE_CASES = [
    ("same call repeated (f x twice) passes every check", "f", _NATIVE_LEAN_CODE,
     "theorem f_spec : ∀ x, f_precond x → (f x).1 < (f x).2 := sorry",
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, ""),
      ("decidable", True, "")]),

    ("two different calls (f x vs f (x+1)) -> conclusion_shape", "f", _NATIVE_LEAN_CODE,
     "theorem f_spec_bad : ∀ x, f_precond x → (f x).1 < (f (x+1)).2 := sorry",
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", False, "the conclusion calls `f` with different arguments: [f x, f (x + 1)]")]),

    ("quantifier over the output stays in the conclusion -> passes", "f", _NATIVE_LEAN_CODE,
     "theorem f_spec_all : ∀ x, f_precond x → ∀ i, i < (f x).1 → i < (f x).2 := sorry",
     [("one_theorem", True, ""),
      ("is_theorem", True, ""),
      ("no_attribute", True, ""),
      ("conclusion_shape", True, ""),
      ("vocabulary", True, ""),
      ("decidable", True, "")]),
]


def _same(got, expected):
    # an expected detail ending in "..." fixes only its start: the rest is Lean's
    # own error text, which is not part of the gate's contract
    if len(got) != len(expected):
        return False
    for (gc, gok, gd), (ec, eok, ed) in zip(got, expected):
        if gc != ec or gok != eok:
            return False
        if ed.endswith("...") and not (gd or "").startswith(ed[:-3]):
            return False
        if not ed.endswith("...") and gd != ed:
            return False
    return True


def run_static():
    print("=== static ===")
    import gate
    import synth

    check("gate.py has no _fix_aeneas_spec-style regex fixups left in synth.py",
          not hasattr(synth, "_fix_aeneas_spec"))

    import strategies
    norm = strategies.normalize_call
    check("a call on a struct literal gets the normal form the full test gates", norm(RAW_SWAP, "records.swap") == NORMAL_SWAP,
          norm(RAW_SWAP, "records.swap"))
    cases = [
        ("constructors and literals become variables a hypothesis defines",
         "∀ {T : Type} (x : T) (tl : C.List T), list_nth_mut (C.List.Cons x tl) 0#u32 ⦃ r => r.1 = x ⦄", "list_nth_mut",
         "∀ {T : Type} (x : T) (tl : C.List T), ∀ (lss_a0 : _) (lss_a1 : _), lss_a0 = (C.List.Cons x tl) → "
         "lss_a1 = (0#u32) → list_nth_mut lss_a0 lss_a1 ⦃ r => r.1 = x ⦄"),
        ("a constant (none) is not a bound variable",
         "∀ {T : Type} (O : C.Ord T) (v : T), TreeSet.insert_loop O v none ⦃ r => r.1 = true ⦄", "TreeSet.insert_loop",
         "∀ {T : Type} (O : C.Ord T) (v : T), ∀ (lss_a0 : _), lss_a0 = none → TreeSet.insert_loop O v lss_a0 ⦃ r => r.1 = true ⦄"),
        ("a variable passed twice is passed once",
         "∀ (x : Std.U32), f x x ⦃ r => True ⦄", "f", "∀ (x : Std.U32), ∀ (lss_a0 : _), lss_a0 = x → f x lss_a0 ⦃ r => True ⦄"),
        ("the new binders come after the hypotheses, before the call",
         "∀ (s : S), s.n > 0 → C.g s (s.n - 1) ⦃ r => True ⦄div", "g",
         "∀ (s : S), s.n > 0 → ∀ (lss_a0 : _), lss_a0 = (s.n - 1) → C.g s lss_a0 ⦃ r => True ⦄div"),
        ("a statement already in normal form is unchanged",
         "∀ (s : S) (i : Std.Usize), h.insert s i ⦃ r => True ⦄", "h.insert", "∀ (s : S) (i : Std.Usize), h.insert s i ⦃ r => True ⦄"),
        ("a call of another function is unchanged", "∀ x, g 0 ⦃ r => True ⦄", "f", "∀ x, g 0 ⦃ r => True ⦄"),
        ("a statement with no triple is unchanged", "∀ x, f x = 1", "f", "∀ x, f x = 1"),
        ("every replaced argument gets its own fresh name, past any the statement already uses",
         "∀ (x : U32) (lss_a0 : U32), lss_a0 = x → f (g x) (h x) ⦃ r => r = x ⦄", "f",
         "∀ (x : U32) (lss_a0 : U32), lss_a0 = x → ∀ (lss_a1 : _) (lss_a2 : _), lss_a1 = (g x) → lss_a2 = (h x) → "
         "f lss_a1 lss_a2 ⦃ r => r = x ⦄"),
        ("a named argument is left as written",
         "∀ (p : P), f p.1 (T := Std.U32) ⦃ r => True ⦄", "f",
         "∀ (p : P), ∀ (lss_a0 : _), lss_a0 = p.1 → f lss_a0 (T := Std.U32) ⦃ r => True ⦄"),
    ]
    for desc, stmt, unit, want in cases:
        got = norm(stmt, unit)
        check(f"normal form: {desc}", got == want, got)

    check("gate.CHECK_ORDER is the six named checks, in order",
          gate.CHECK_ORDER == ["one_theorem", "is_theorem", "no_attribute",
                                "conclusion_shape", "vocabulary", "decidable"],
          str(gate.CHECK_ORDER))
    check("the rust track has every check but decidable",
          gate.checks_for("rust-aeneas") == gate.CHECK_ORDER[:-1] and gate.checks_for("lean-native") == gate.CHECK_ORDER,
          str(gate.checks_for("rust-aeneas")))
    rust_ok = [{"gate": "wf", "check": c, "ok": True, "detail": ""} for c in gate.RUST_CHECK_ORDER]
    check("a rust candidate passing its five checks is well-formed", gate.is_well_formed(rust_ok, "rust-aeneas"))
    check("the same five verdicts are not a native pass (it stopped before decidable)",
          not gate.is_well_formed(rust_ok, "lean-native") and not gate.is_well_formed(rust_ok))

    # verdict schema: is_well_formed / failing_check against synthetic verdicts,
    # no Lean involved.
    schema_ok = [{"gate": "wf", "check": c, "ok": True, "detail": ""} for c in gate.CHECK_ORDER]
    check("is_well_formed true when all six checks ran and passed", gate.is_well_formed(schema_ok))
    check("failing_check none when every verdict ok", gate.failing_check(schema_ok) is None)
    check("is_well_formed false when the gate stopped early with every verdict ok",
          not gate.is_well_formed(schema_ok[:5]))

    schema_bad = [{"gate": "wf", "check": "one_theorem", "ok": True, "detail": ""},
                  {"gate": "wf", "check": "is_theorem", "ok": False, "detail": "nope"}]
    check("is_well_formed false on first failing verdict", not gate.is_well_formed(schema_bad))
    check("failing_check names the failing check", gate.failing_check(schema_bad) == "is_theorem",
          str(gate.failing_check(schema_bad)))
    check("is_well_formed false on empty verdict list (gate produced nothing)",
          not gate.is_well_formed([]))

    check("lean/wf_gate.lean exists", os.path.exists(gate._WF_GATE_PATH))
    check("lean/wf_gate_aeneas.lean exists", os.path.exists(gate._WF_GATE_AENEAS_PATH))

    # synth.py raises instead of asking the LLM for a repair when the gate
    # couldn't even get an environment (a setup error, not the candidate's
    # fault) -- that branch keys off exactly this pair.
    env_fail_verdicts = gate._env_fail("crate env unavailable: boom")
    check("_env_fail's verdict list is not well-formed", not gate.is_well_formed(env_fail_verdicts))
    check("_env_fail's failing check is \"env\"", gate.failing_check(env_fail_verdicts) == "env",
          str(gate.failing_check(env_fail_verdicts)))

    # the prompt text synth.py sends the LLM for rust units: new spec form in,
    # old ∃r/ok-equation idiom and its regex fixups out.
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "synth.py"),
               encoding="utf-8").read()
    check("prompt teaches the ⦃ r => P r ⦄ spec form", "⦃ r => P r ⦄" in src)
    check("prompt teaches ⦃ ⦄div for loop/recursive units", "⦃ ⦄div" in src)
    check("prompt no longer asks for the old `exists r, f x = ok r` idiom",
          "exists r, f x = ok r" not in src)
    check("prompt's WRONG examples flag the old ok-equation form as wrong",
          "records.swap p = ok {" in src and "WRONG (never write these)" in src)
    check("prompt's CORRECT EXAMPLES no longer teach a vacuous `True` postcond",
          "⦃ r => True ⦄" not in src)
    check("prompt's CORRECT EXAMPLES no longer apply a function to a concrete constant",
          "lists.head_or lists.List.Nil d" not in src)
    check("prompt's CORRECT EXAMPLES no longer teach a property that holds for every Usize",
          "r.val ≤ Std.Usize.max" not in src)
    check("prompt's CORRECT EXAMPLES include head_or_spec (unit applied only to bound variables)",
          "theorem head_or_spec (xs : lists.List) (d : Std.U32) : lists.head_or xs d "
          "⦃ r => r = match xs with | .Nil => d | .Cons x _ => x ⦄ := sorry" in src)
    check("prompt's CORRECT EXAMPLES include swap_ordered (a real, non-vacuous property)",
          "theorem swap_ordered (p : records.Pair) (h : p.first.val ≤ p.second.val) : records.swap p "
          "⦃ r => r.second.val ≤ r.first.val ⦄ := sorry" in src)

    # statements as the LLM writes them reach the gate whole
    import strategies
    got = strategies.theorems("```lean\n"
                              "theorem a (T : Type) {x : T} (h : (0#u32).val < 3) : f x ⦃ r => ∀ (t : T), r.2 t = g t ⦄ := sorry\n"
                              "theorem b : ∀ (n : Std.U32), f n ⦃ r => r = n ⦄ := by simp\n```")
    check("a reply's binders become a leading ∀, so the statement stands alone",
          [(n, s) for n, s, _ in got] == [
              ("a", "∀ (T : Type) {x : T} (h : (0#u32).val < 3), f x ⦃ r => ∀ (t : T), r.2 t = g t ⦄"),
              ("b", "∀ (n : Std.U32), f n ⦃ r => r = n ⦄")], str(got))
    got = strategies.theorems("Here is the fixed theorem: theorem c (l : CList T) :\n  f l\n"
                              "  ⦃ r => let y := r.1; y = 0#u32 ⦄div := sorry")
    check("a fixed theorem after prose, over several lines, with a `let`, is read whole",
          [(n, s) for n, s, _ in got] == [("c", "∀ (l : CList T), f l\n  ⦃ r => let y := r.1; y = 0#u32 ⦄div")],
          str(got))
    strat = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "strategies.py"),
                 encoding="utf-8").read()
    check("every LLM reply goes through the one reader: no theorem regex is left",
          "re.search(r':\\s*(.*?)\\s*:='" not in src and "theorem\\s+(\\w+)\\s*:" not in src + strat
          and "(?:\\([^)]*\\)\\s*)*" not in src + strat)
    args, ret = synth._parse_signature("def TreeSet.insert_loop {T : Type} (OrdInst : Ord T) (value : T)\n"
                                       "  (current_tree : Option (Node T)) :\n  Result (Bool × Option (Node T)) := do\n",
                                       "TreeSet.insert_loop")
    check("a signature argument with nested parentheses is one argument, and the return type is read",
          args == [("OrdInst", "Ord T"), ("value", "T"), ("current_tree", "Option (Node T)")]
          and ret == "Result (Bool × Option (Node T))", f"{args} {ret}")
    types = "structure Ord (Self : Type) where\n  cmp : Self → Self → Result Ordering\ninductive Node (T : Type) where\n"
    check("the crate's own types in the prompt's signature carry the crate name",
          synth._qualify_types("Ord T", "open Aeneas Aeneas.Std\nopen Bst\n", types) == "Bst.Ord T"
          and synth._qualify_types("Option (Node T)", "open Bst\n", types) == "Option (Bst.Node T)"
          and synth._qualify_types("Bst.Ord T", "open Bst\n", types) == "Bst.Ord T")
    check("the prompt writes Aeneas integers as 0#u32, never as (0 : Std.U32)",
          "Numeric literals may need type annotation" not in src and "0#u32, 5#i8" in src)
    check("the prompt states a case as a hypothesis, the function on bound variables only",
          "state a case as a hypothesis" in src)


def run_full():
    print("=== full ===")
    import lean
    import gate
    import lss_config

    rust_dir = os.path.expanduser("~/rust_benchmarks")
    code_dir = os.path.join(rust_dir, "FeatureSuite", "Code")
    if not os.path.isdir(code_dir):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, f"not a directory: {code_dir}")
        return

    checker = lean.LeanChecker()

    for desc, unit, candidate, expected in RUST_CASES:
        verdicts = gate.check_candidate(checker, candidate, unit, None, rust_dir, "rust-aeneas")
        got = [(v.get("check"), v.get("ok"), v.get("detail")) for v in verdicts]
        check(desc, _same(got, expected), f"expected {expected}, got {got}")

    native_dir = lss_config.project_dir("lean-native")
    if not os.path.isdir(native_dir):
        check(f"{native_dir} exists", False, f"not a directory: {native_dir}")
        return

    for desc, unit, lean_code, candidate, expected in NATIVE_CASES:
        verdicts = gate.check_candidate(checker, candidate, unit, lean_code, native_dir, None)
        got = [(v.get("check"), v.get("ok"), v.get("detail")) for v in verdicts]
        check(desc, _same(got, expected), f"expected {expected}, got {got}")


if static:
    run_static()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
