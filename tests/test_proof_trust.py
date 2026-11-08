import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

static = "--static" in sys.argv
fails = []

print(f"mode {'static' if static else 'full'}")

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


def _verdicts(text):
    out = {}
    for m in re.finditer(r"LSS_PROOF (\{[^\n]*\})", text or ""):
        try:
            v = json.loads(m.group(1))
        except json.JSONDecodeError:
            continue
        out[v.get("name")] = v
    return out


def _lean_defs(path):
    with open(path, encoding="utf-8") as f:
        return set(re.findall(r"^(?:partial )?def (\w+)", f.read(), re.MULTILINE))


class _FakeServer:
    """records every text sent (and its prelude); answers with `reply(code)`, by
    default an empty, error-free result -- a REPL that elaborated it cleanly."""

    def __init__(self, reply=None):
        self.sent = []
        self.preludes = []
        self.reply = reply or (lambda code: "")

    def check(self, code, timeout=None, env=None, prelude=""):
        import lean_server
        self.sent.append(code)
        self.preludes.append(prelude)
        return lean_server.CheckResult(stdout="", stderr=self.reply(code), rc=0, via="repl", new_env=1)

    def stats(self):
        return {"restarts": 0}


def _verdict_line(name, ok, stage="ok", axioms=()):
    return "LSS_PROOF " + json.dumps({"name": name, "ok": ok, "stage": stage, "detail": "",
                                      "axioms": list(axioms)}) + "\n"


def _with_fake(fake, fn):
    import lean_server
    orig = lean_server.get_server
    lean_server.get_server = lambda *a, **k: fake
    try:
        return fn()
    finally:
        lean_server.get_server = orig


# the axiom each native-evaluation tactic adds on the pinned toolchain, for a
# theorem elaborated through lss_check_proof (synchronously: Elab.async false).
# a top-level theorem elaborated asynchronously gets `..._1_1` instead, so the
# test also reads `#print axioms` for the same theorem, declared again after the
# check took it back out, elaborated the same way, and compares.
NATIVE_AXIOMS = {
    "planted_native": ["planted_native._native.native_decide.ax_1"],
    "planted_decide_native": ["planted_decide_native._native.decide.ax_1"],
}

# FeatureSuite's records.order_pair calls records.swap (see test_aeneas_layer.py)
ORDER_PAIR_GOAL = "forall (p : records.Pair), exists r, records.order_pair p = ok r ∧ r.first ≤ r.second"
SWAP_HOARE = "forall (p : records.Pair), records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄"
SWAP_HOARE_HALF1 = "forall (p : records.Pair), records.swap p ⦃ r => r.first = p.second ⦄"
CLOSERS = "step* <;> first | scalar_tac | simp_scalar | (simp_all <;> simp_lists [*]) | grind"
CALLER_TACTIC = "lss_spec_form\nunfold records.order_pair\n" + CLOSERS
# looks inside the callee: unfolds swap instead of using its spec
CALLER_THROUGH_CALLEE = "lss_spec_form\nunfold records.order_pair\nunfold records.swap\n" + CLOSERS

# a tactic that fails when either option the checker forces is not in force;
# defined outside the checked text (the checker only accepts theorems).
OPTION_PROBE = """
open Lean Elab Tactic in
elab "lss_test_forced_opts" : tactic => do
  let o ← getOptions
  if debug.skipKernelTC.get o then throwError "debug.skipKernelTC is on"
  if Elab.async.get o then throwError "Elab.async is on"
"""

CHECKER_CASES = [
    # (description, theorems, name, heartbeats, expected ok, expected stage, detail must contain)
    ("clean proof passes", "theorem planted_clean : 2 + 2 = 4 := by decide",
     "planted_clean", 0, True, "ok", ""),
    ("classical proof passes with the three standard axioms",
     "theorem planted_classical (p : Prop) : p ∨ ¬ p := Classical.em p",
     "planted_classical", 0, True, "ok", ""),
    ("native_decide is rejected by the axiom audit",
     "theorem planted_native : 2 + 2 = 4 := by native_decide",
     "planted_native", 0, False, "axioms", "(native)"),
    ("decide +native is rejected by the axiom audit",
     "theorem planted_decide_native : 2 + 2 = 4 := by decide +native",
     "planted_decide_native", 0, False, "axioms", "(native)"),
    ("sorry is rejected by the axiom audit",
     "theorem planted_sorry : 2 + 2 = 5 := sorry",
     "planted_sorry", 0, False, "axioms", "sorryAx (sorry)"),
    ("a failing tactic is reported with its own error text",
     "theorem planted_false : 2 + 2 = 5 := by decide",
     "planted_false", 0, False, "elab", "is false"),
    ("set_option before the theorem is rejected",
     "set_option debug.skipKernelTC true in\ntheorem planted_skip : 1 = 1 := rfl",
     "planted_skip", 0, False, "not_theorem", "Command.in"),
    ("an axiom declaration is rejected",
     "axiom planted_cheat : False\ntheorem planted_ax : 1 = 2 := planted_cheat.elim",
     "planted_ax", 0, False, "not_theorem", "Command.axiom"),
    ("#eval is rejected", "#eval 1", "planted_eval", 0, False, "not_theorem", "Command.eval"),
    ("helper theorems before the named one are allowed",
     "theorem planted_helper : 1 + 1 = 2 := rfl\ntheorem planted_main : 2 = 1 + 1 := planted_helper.symm",
     "planted_main", 0, True, "ok", ""),
    ("a missing theorem name is reported",
     "theorem planted_other : 1 = 1 := rfl", "planted_missing", 0, False, "missing", "planted_missing"),
    ("a parse error is reported", "theorem planted_parse : 1 = := rfl",
     "planted_parse", 0, False, "parse", "does not parse"),
    ("an unknown name is an error, not an implicit variable",
     "theorem planted_implicit : planted_unknown = planted_unknown := rfl",
     "planted_implicit", 0, False, "elab", "planted_unknown"),
    ("the heartbeat budget applies",
     "theorem planted_budget (xs ys : List Nat) : (xs ++ ys).reverse.length = ys.length + xs.length := by grind",
     "planted_budget", 1, False, "elab", "heartbeats"),
    ("the same proof passes without the tiny budget",
     "theorem planted_budget2 (xs ys : List Nat) : (xs ++ ys).reverse.length = ys.length + xs.length := by grind",
     "planted_budget2", 0, True, "ok", ""),
    ("a lemma added inside the proof without the kernel is caught by the replay, and taken back out",
     "theorem planted_forged : (1 : Nat) = 2 := by\n  run_tac do\n"
     "    let ty ← Lean.Meta.mkEq (Lean.mkNatLit 1) (Lean.mkNatLit 2)\n"
     "    let v ← Lean.Meta.mkEqRefl (Lean.mkNatLit 1)\n"
     "    Lean.withOptions (fun o => o.setBool `debug.skipKernelTC true) do\n"
     "      Lean.addDecl (.thmDecl (Lean.mkTheoremValEx `planted_forged_lemma [] ty v []))\n"
     "  exact planted_forged_lemma",
     "planted_forged", 0, False, "replay", "planted_forged_lemma"),
    ("a lemma added inside a proof that then fails stays out of the environment",
     "theorem planted_left : (1 : Nat) = 2 := by\n  run_tac do\n"
     "    let ty ← Lean.Meta.mkEq (Lean.mkNatLit 1) (Lean.mkNatLit 2)\n"
     "    let v ← Lean.Meta.mkEqRefl (Lean.mkNatLit 1)\n"
     "    Lean.withOptions (fun o => o.setBool `debug.skipKernelTC true) do\n"
     "      Lean.addDecl (.thmDecl (Lean.mkTheoremValEx `planted_left_lemma [] ty v []))\n"
     "  decide",
     "planted_left", 0, False, "elab", "is false"),
    ("so a later proof cannot use it",
     "theorem planted_reuse : (1 : Nat) = 2 := planted_left_lemma",
     "planted_reuse", 0, False, "elab", "planted_left_lemma"),
    ("a verdict the checked text logs itself, as a warning or an error, is not a verdict",
     "theorem planted_fake : True := by\n  run_tac do\n"
     '    let v := Lean.Json.compress (Lean.Json.mkObj [("name", "planted_ghost"), ("ok", true), ("stage", "ok"), '
     '("detail", ""), ("axioms", Lean.Json.arr #[])])\n'
     '    Lean.logWarning m!"LSS_PROOF {v}"\n    Lean.logError m!"LSS_PROOF {v}"\n  trivial',
     "planted_fake", 0, False, "elab", "LSS-PROOF"),
    ("a recursive theorem and its auxiliary declarations pass the replay",
     "theorem planted_rec : ∀ n : Nat, 0 + n = n\n  | 0 => rfl\n  | n + 1 => congrArg Nat.succ (planted_rec n)",
     "planted_rec", 0, True, "ok", ""),
    ("kernel checking and synchronous elaboration are forced even when set globally",
     "theorem planted_forced : True := by\n  lss_test_forced_opts\n  trivial",
     "planted_forced", 0, True, "ok", ""),
]


def _call(theorems, name, heartbeats):
    import lean
    return lean.proof_check_call(theorems, name, heartbeats)


def run_static():
    print("=== static ===")
    import lean
    import gate
    import lean_server

    pc_path = os.path.join(ROOT, "lean", "proof_check.lean")
    check("lean/proof_check.lean exists", os.path.exists(pc_path))
    pc_defs = _lean_defs(pc_path)
    gate_defs = _lean_defs(gate._WF_GATE_PATH)
    check("proof_check.lean defines the parsing helpers the gate uses",
          {"lssParseAll", "lssFirstError"} <= pc_defs, str(sorted(pc_defs)))
    check("wf_gate.lean defines nothing proof_check.lean defines (one env holds both)",
          not (pc_defs & gate_defs), str(sorted(pc_defs & gate_defs)))
    check("allowed axioms are exactly propext, Classical.choice, Quot.sound",
          "#[``propext, ``Classical.choice, ``Quot.sound]" in lean.proof_check_text())
    pc = lean.proof_check_text()
    cmds = pc[pc.index("def lssCheckCmds"):pc.index("def lssParseText")]
    check("lss_check_proof replays what the text added through the kernel after elaborating, before the axiom audit",
          "lssReplayOne news" in pc and "addDeclCore 0 decl" in pc and "Lean.Environment.replay" not in pc
          and "let env0 ← getEnv" in cmds
          and 0 <= cmds.find("elabCommand cmd") < cmds.find("lssReplaySince env0") < cmds.find("collectAxioms fullName"),
          cmds[:200])

    fail_at = [cmds.find(f'fail "{st}"') for st in ("elab", "missing", "replay", "axioms")]
    check("every stage a text fails at takes the text back out of the environment before its verdict",
          all(i > 0 for i in fail_at) and "setEnv env0\n    emit false stage" in cmds
          and cmds.count("emit false") == 2, str(fail_at))
    helpers = pc[pc.index('elab "lss_define_helpers '):]
    check("only a checked text's errors go back into the log, defused, in the proof check, the helpers and the gate "
          "(whose candidate elaborates synchronously, so no message comes after the filter)",
          "lssOwnErrors log" in cmds and "lssOwnErrors log" in helpers
          and "lssOwnErrors candLog" in open(gate._WF_GATE_PATH, encoding="utf-8").read()
          and "`autoImplicit false).setBool `Elab.async false" in open(gate._WF_GATE_PATH, encoding="utf-8").read()
          and "before ++ log" not in cmds, "")
    got = lean.parse_proof_verdicts(_verdict_line("a", True) + _verdict_line("a", False, "elab"))
    check("the first verdict for a name is its own: a later line with the same name does not replace it",
          got["a"]["ok"] is True, str(got))

    # native gate: proof_check.lean goes first, then wf_gate.lean, then the call
    fake = _FakeServer()
    orig_get = lean_server.get_server
    lean_server.get_server = lambda *a, **k: fake
    try:
        gate.check_candidate(None, "theorem t : ∀ n : Nat, n = n := sorry", "f",
                             "def f (n : Nat) : Nat := n", "/nonexistent", None)
    finally:
        lean_server.get_server = orig_get
    sent = fake.sent[-1] if fake.sent else ""
    i_pc, i_gate, i_call = (sent.find("def lssParseAll"), sent.find('elab "lss_wf_gate '),
                            sent.find("\nlss_wf_gate "))
    check("native gate sends proof_check.lean before wf_gate.lean, then the call",
          0 <= i_pc < i_gate < i_call, f"{i_pc} {i_gate} {i_call}")

    # rust crate env: proof_check.lean before aeneas_layer.lean
    import callgraph

    class _G:
        crate_text = "import Aeneas\n-- crate\n"
        crate = "Crate"

    fake = _FakeServer()
    orig_for = callgraph.for_project
    lean_server.get_server = lambda *a, **k: fake
    callgraph.for_project = lambda p: _G()
    try:
        lean.LeanChecker()._aeneas_build_env("/nonexistent")
    finally:
        lean_server.get_server = orig_get
        callgraph.for_project = orig_for
    sent = "\n".join(fake.sent)
    i_pc, i_layer = sent.find('elab "lss_check_proof '), sent.find("macro \"lss_spec_form\"")
    check("crate env holds proof_check.lean before aeneas_layer.lean", 0 <= i_pc < i_layer, f"{i_pc} {i_layer}")
    check("LSS's own commands are elaborated before the crate's namespace is entered, so no crate name can shadow "
          "theirs, and the crate's names are the crate's after it (no `open`, which left List ambiguous)",
          0 <= i_layer < sent.find("namespace Crate\n") and "open Crate" not in sent,
          f"{i_layer} {sent.find('namespace Crate')}")


class _FakeGraph:
    crate = "C"
    names = {"C.top", "C.swap", "C.rec", "C.leaf"}

    def callees_outside_scc(self, unit):
        return {"C.top": ["C.leaf", "C.swap"], "C.rec": ["C.swap"]}.get(unit, [])

    def recursive(self, unit):
        return unit == "C.rec"


def run_static_verdicts():
    print("=== static: every layer reads its verdict ===")
    import lean
    import synth

    got = lean.parse_proof_verdicts("noise\n" + _verdict_line("a", True) + "LSS_PROOF {broken\n" +
                                    _verdict_line("b", False, "axioms", ["sorryAx"]))
    check("parse_proof_verdicts reads every verdict and skips broken lines",
          set(got) == {"a", "b"} and got["a"]["ok"] is True and got["b"]["stage"] == "axioms", str(got))

    fake = _FakeServer()
    v, _ = _with_fake(fake, lambda: lean.check_proof("def f := 1", "theorem t : f = 1 := rfl", "t"))
    check("check_proof adds import Lean when the context has no import",
          fake.sent[-1].startswith("import Lean\n"), fake.sent[-1][:40])
    check("check_proof sends proof_check.lean as the server prelude", fake.preludes[-1] == lean.proof_check_text())
    check("no verdict in the output is not a proof", v["ok"] is False and v["stage"] == "no_verdict", str(v))

    # an error-free run with no verdicts proves nothing (the old rc == 0 shortcut)
    checker = lean.LeanChecker(project_dir="/nonexistent")
    setattr(checker, "_precheck_env", lambda project_dir, requires_hammer=False: (True, ""))
    fake = _FakeServer()
    pr = _with_fake(fake, lambda: checker.try_proof_batch("def f (n : Nat) : Nat := n", "∀ n, f n = n",
                                                          func_name="f", project_dir="/nonexistent"))
    check("tactic portfolio: a clean run with no verdict is not proved", pr.proved is False, str(pr))

    # the first accepted entry, in portfolio order, wins; rejected entries before it do not count
    def reply_batch(code):
        return (_verdict_line("_lss_p0", False, "axioms", ["sorryAx"]) + _verdict_line("_lss_p3", True) +
                _verdict_line("_lss_p5", True, "ok", ["propext"]))
    fake = _FakeServer(reply_batch)
    pr = _with_fake(fake, lambda: checker.try_proof_batch("def f (n : Nat) : Nat := n", "∀ n, f n = n",
                                                          func_name="f", project_dir="/nonexistent"))
    check("tactic portfolio: the first accepted entry wins", pr.proved and pr.method == "l1:decide", str(pr))
    check("tactic portfolio: every entry goes through lss_check_proof",
          fake.sent[-1].count("lss_check_proof ") == fake.sent[-1].count("theorem _lss_p") >= 20
          and "private theorem" not in fake.sent[-1], str(fake.sent[-1].count("lss_check_proof ")))
    check("tactic portfolio: the function-aware batch proved it, so the automation batch is never sent",
          len(fake.sent) == 1, str(len(fake.sent)))

    # gcd' recurses with no cases: one equation, its whole body, which simp would unfold forever
    gcd = ("def gcd' (a b : Nat) : Nat :=\n  if h : a = 0 then b else gcd' (b % a) a\n"
           "termination_by a\ndecreasing_by\n  apply Nat.mod_lt\n  omega")
    fake = _FakeServer()
    _with_fake(fake, lambda: checker.try_proof_batch(gcd, "∀ (a b : Nat), a = 0 → gcd' a b = b",
                                                     func_name="gcd'", project_dir="/nonexistent"))
    sent = "\n".join(fake.sent)
    check("tactic portfolio: when the first batch proves nothing, the automation batch is sent next",
          len(fake.sent) == 2 and "exact?" not in fake.sent[0] and "exact?" in fake.sent[1], str(len(fake.sent)))
    handed = re.findall(r"(?:simp|simp_all|grind) \[[^\]]*gcd'", sent)
    check("tactic portfolio: a recursive function without cases goes to simp only after one case split",
          len(handed) == 1 and "fun_cases gcd' <;> simp_all [gcd']" in sent, str(handed))
    check("tactic portfolio: a statement in normal form is substituted back before the call unfolds, "
          "and a recursive one is tried by its own induction principle",
          "intros; subst_vars; unfold gcd'; split <;> simp_all" in sent and "intros; fun_induction gcd' <;> simp_all" in sent)
    cl = lean.classify_function
    check("a recursion by `|` cases or one top-level match has an equation per case; one whose body is an "
          "`if`, even with a match inside, has a single equation",
          cl("def p : List Nat → Nat\n  | [] => 0\n  | x :: xs =>\n    let y := p xs\n    y + x", "p")["by_cases"]
          and cl("def q (l : List Nat) : Nat :=\n  match l with\n  | [] => 0\n  | _ :: t => q t", "q")["by_cases"]
          and not cl("def g (n : Nat) : Nat :=\n  if n = 0 then 0 else match n with\n  | k+1 => g k", "g")["by_cases"]
          and cl("def g (n : Nat) : Nat :=\n  if n = 0 then 0 else match n with\n  | k+1 => g k", "g")["recursive"])
    import lss_config
    hb = lss_config.proof_cfg()["tactic_heartbeats"]
    calls = re.findall(r"lss_check_proof .*? heartbeats:(\d+)", sent)
    check("tactic portfolio: every attempt runs under its own heartbeat budget",
          calls and all(int(h) == hb for h in calls), str(set(calls)))

    # hammer: an accepted verdict proves, an axiom rejection does not
    import lss_config
    orig_hp = lss_config.hammer_project_dir
    lss_config.hammer_project_dir = lambda: "/nonexistent"
    try:
        fake = _FakeServer(lambda code: _verdict_line("_hammer_proof", True, "ok", ["propext"]))
        pr = _with_fake(fake, lambda: checker.try_hammer("", "∀ n : Nat, n = n"))
        check("hammer: an accepted verdict proves", pr.proved and pr.axioms == ["propext"], str(pr))
        fake = _FakeServer(lambda code: _verdict_line("_hammer_proof", False, "axioms", ["x._native.native_decide.ax_1"]))
        pr = _with_fake(fake, lambda: checker.try_hammer("", "∀ n : Nat, n = n"))
        check("hammer: an axiom rejection does not prove", pr.proved is False, str(pr))
    finally:
        lss_config.hammer_project_dir = orig_hp

    # the aeneas layer: an attempt counts only with an accepted verdict, and only then is it admitted
    import callgraph
    state = {"ok": True, "env": 3, "admitted": [], "active": {}, "restarts": 0}
    setattr(checker, "_aeneas_env_for", lambda project_dir: state)
    orig_for = callgraph.for_project
    callgraph.for_project = lambda p: _FakeGraph()  # C.f: no external callee, so no modularity call
    fake = _FakeServer(lambda code: _verdict_line("_aeneas_a", False, "axioms", ["sorryAx"]))
    pr = _with_fake(fake, lambda: checker.try_aeneas("stmt", "f", "/nonexistent"))
    check("aeneas layer: a rejected attempt and a missing verdict prove nothing",
          not pr.proved and not state["admitted"], str(pr)[:200])

    def reply_aeneas(code):
        out = _verdict_line("_aeneas_a", False, "elab") + _verdict_line("_aeneas_b", True, "ok", ["propext"])
        return out + (_verdict_line("lss_admitted_0", True) if "name:lss_admitted_0 " in code else "")
    fake = _FakeServer(reply_aeneas)
    pr = _with_fake(fake, lambda: checker.try_aeneas("stmt", "f", "/nonexistent"))
    callgraph.for_project = orig_for
    check("aeneas layer: an accepted attempt proves and is admitted through its own verdict",
          pr.proved and pr.method == "aeneas:b" and pr.axioms == ["propext"] and len(state["admitted"]) == 1
          and state["env"] == 1, f"{pr} {state}"[:300])

    # synth's LLM proof check: the verdict decides, the output carries the errors
    fake = _FakeServer(lambda code: "error: unsolved goals\n" + _verdict_line("_t", False, "elab"))
    ok, raw = _with_fake(fake, lambda: synth._try_lean_proof("", "1 = 1", "simp"))
    check("synth proof check: a rejected verdict is not proved and keeps the error text",
          ok is False and "unsolved goals" in raw, raw[:100])
    fake = _FakeServer(lambda code: _verdict_line("_t", True))
    ok, _ = _with_fake(fake, lambda: synth._try_lean_proof("", "1 = 1", "rfl"))
    check("synth proof check: an accepted verdict proves", ok is True)


# every function that may set status "proved", and how many times; each one takes
# it from an LSS_PROOF verdict (a ProofResult from lean.py, synth._try_lean_proof
# or lean.check_proof). a new site must be checked the same way before it is added.
PROVED_SITES = {"validate": 4, "_llm_repair": 3, "_try_proof_sketch": 2, "synthesize": 1,
                "generate_with_proof": 1, "_admit_with_proof": 1}


def _proved_sites():
    import ast
    import collections
    found = collections.Counter()

    def visit(node, fn):
        for ch in ast.iter_child_nodes(node):
            f = ch.name if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef)) else fn
            hit = False
            if isinstance(ch, ast.Assign) and isinstance(ch.value, ast.Constant) and ch.value.value == "proved":
                hit = any(isinstance(t, ast.Subscript) and isinstance(t.slice, ast.Constant)
                          and t.slice.value == "status" for t in ch.targets)
            if isinstance(ch, ast.Dict):
                hit = any(isinstance(k, ast.Constant) and k.value == "status" and isinstance(v, ast.Constant)
                          and v.value == "proved" for k, v in zip(ch.keys, ch.values))
            if hit and f is not None:  # module-level demo data under __main__ is not a pipeline path
                found[f] += 1
            visit(ch, f)

    for name in sorted(os.listdir(ROOT)):
        if name.endswith(".py"):
            with open(os.path.join(ROOT, name), encoding="utf-8") as fh:
                visit(ast.parse(fh.read()), None)
    return dict(found)


def run_static_no_unverdicted():
    print("=== static: nothing marks proved without a verdict ===")
    import lean
    import synth

    sites = _proved_sites()
    check("the only places that set status proved are the verdict-backed ones",
          sites == PROVED_SITES, f"found {sites}")
    check("SpecMutator is gone", not hasattr(lean, "SpecMutator"))
    check("no strengthening swap is left (LLMClient.strengthen_spec is gone)",
          not hasattr(synth.LLMClient, "strengthen_spec"))
    with open(os.path.join(ROOT, "synth.py"), encoding="utf-8") as fh:
        src = fh.read()
    check("the batched strengthening checks (_sq, _psq) are gone",
          "_sq{" not in src and "_psq{" not in src, "found a _sq/_psq absence check")


def run_static_modularity():
    print("=== static: modularity and blame orchestration ===")
    import lean

    checker = lean.LeanChecker()
    state = {"env": 7, "active": {"C.swap": "lss_admitted_0.step"}}
    g = _FakeGraph()

    def modular_reply(passing):
        def reply(code):
            tag = re.search(r"lss_modular (\S+)", code)
            name = (tag.group(1) if tag else "?") + ".proof"
            return _verdict_line(name, passing(code), "ok" if passing(code) else "elab")
        return reply

    tactic = "lss_spec_form\n  unfold C.top\n  step*"
    fake = _FakeServer(modular_reply(lambda code: True))
    got = _with_fake(fake, lambda: checker._modularity(g, state, "C.top", "stmt", tactic))
    check("modular: a proof that passes the abstraction is modular, in one check",
          got == (True, []) and len(fake.sent) == 1, f"{got} after {len(fake.sent)} checks")
    sent = fake.sent[0] if fake.sent else ""
    check("modular: every external callee is abstracted, with its active spec lemma or _",
          "abstract:[C.leaf _, C.swap lss_admitted_0.step] inline:[]" in sent, sent[-200:])
    check("modular: the tactic is sent with one indentation",
          'tactic:"lss_spec_form\\nunfold C.top\\nstep*"' in sent, sent[:300])

    # abstraction fails; keeping swap concrete passes: the proof needs swap's body
    fake = _FakeServer(modular_reply(lambda code: "abstract:[C.leaf _]" in code))
    got = _with_fake(fake, lambda: checker._modularity(g, state, "C.top", "stmt", tactic))
    check("modular: the callee whose concrete body rescues the proof is named",
          got == (False, ["C.swap"]), str(got))

    fake = _FakeServer(modular_reply(lambda code: True))
    got = _with_fake(fake, lambda: checker._modularity(g, state, "C.rec", "stmt", tactic))
    check("modular: recursive units are not checked", got == (None, []) and not fake.sent, str(got))
    got = _with_fake(fake, lambda: checker._modularity(g, state, "C.leaf", "stmt", tactic))
    check("modular: a unit without external callees is modular without a check",
          got == (True, []) and not fake.sent, str(got))

    # blame: inlining swap rescues the failed proof, inlining leaf does not
    fake = _FakeServer(modular_reply(lambda code: "inline:[C.swap]" in code))
    got = _with_fake(fake, lambda: checker._blame(g, state, "C.top", "stmt", tactic))
    check("blame: the callee whose inlined body rescues the proof is blamed by name",
          got == ["C.swap"] and len(fake.sent) == 2, f"{got} after {len(fake.sent)} checks")
    check("blame: other callees keep their step lemmas (nothing abstracted)",
          all("abstract:[]" in c for c in fake.sent), str([c[-120:] for c in fake.sent]))

    # admit records the unit's active step lemma from LSS_STEP
    st = {"env": 0, "admitted": [], "active": {}}
    fake = _FakeServer(lambda code: _verdict_line("lss_admitted_3", True) + 'LSS_STEP {"call":"lss_admitted_3",'
                       '"action":"combined","active":"lss_admitted_3.comb","replaced":"lss_admitted_1.step"}\n')
    _with_fake(fake, lambda: checker._aeneas_admit("/p", st, "lss_admitted_3", "stmt", "step*", "C.swap"))
    check("admit records the unit's active step lemma",
          st["active"] == {"C.swap": "lss_admitted_3.comb"} and st["env"] == 1 and len(st["admitted"]) == 1, str(st))
    fake = _FakeServer(lambda code: _verdict_line("lss_admitted_4", True))
    _with_fake(fake, lambda: checker._aeneas_admit("/p", st, "lss_admitted_4", "stmt", "step*", "C.swap"))
    sent = fake.sent[0] if fake.sent else ""
    order = [sent.find(x) for x in ["attribute [-step] lss_admitted_3.comb\n", "lss_check_proof",
                                    "attribute [step] lss_admitted_3.comb", "lss_register_step lss_admitted_4"]]
    check("a later spec of the same unit is proved with the unit's own step lemma taken off, put back before "
          "it is registered", sent.startswith("attribute [-step] lss_admitted_3.comb\n") and -1 not in order
          and order == sorted(order), sent[:300])
    fake = _FakeServer(modular_reply(lambda code: True))
    _with_fake(fake, lambda: checker._modularity(g, {"env": 7, "active": {"C.top": "lss_admitted_5.step",
                                                                           "C.swap": "lss_admitted_0.step"}},
                                                 "C.top", "stmt", tactic))
    sent = fake.sent[0] if fake.sent else ""
    check("modular: the unit's own step lemma is taken off for the check, the callee's kept",
          sent.startswith("attribute [-step] lss_admitted_5.step\n") and "C.swap lss_admitted_0.step" in sent,
          sent[:200])


def run_full():
    print("=== full ===")
    import lean
    import lean_server
    import lss_config

    proj = lss_config.project_dir("aeneas")
    if not os.path.isdir(proj):
        check(f"{proj} exists", False, "not a directory")
        return
    server = lean_server.get_server(proj, lss_config.server_cfg())
    check("server started", server._worker is not None)

    text = "import Lean\n" + lean.proof_check_text() + OPTION_PROBE
    text += "set_option debug.skipKernelTC true\nset_option Elab.async true\n"
    for _, theorems, name, hb, _, _, _ in CHECKER_CASES:
        text += _call(theorems, name, hb) + "\n"
    text += "#check @planted_forged_lemma\n"
    text += "namespace LssPlantedNs\n" + _call("theorem planted_ns : 1 = 1 := rfl", "planted_ns", 0) + "\nend LssPlantedNs\n"
    text += "set_option debug.skipKernelTC false\n"
    text += "".join(f"set_option Elab.async false in\n{th}\n#print axioms {name}\n"
                    for _, th, name, *_ in CHECKER_CASES if name in NATIVE_AXIOMS)
    # control: the probe does fire outside the checker
    text += ("set_option debug.skipKernelTC true in\n"
             "theorem planted_unforced : True := by\n  lss_test_forced_opts\n  trivial\n")
    r = server.check(text, timeout=300)
    out = (r.stdout or "") + "\n" + (r.stderr or "")
    got = _verdicts(out)
    for desc, _, name, _, ok, stage, needle in CHECKER_CASES:
        v = got.get(name)
        check(desc, v is not None and v.get("ok") is ok and v.get("stage") == stage
              and needle in v.get("detail", "") + name, str(v)[:300])
    check("inside a namespace the verdict carries the theorem's name as written, and checks the qualified one",
          got.get("planted_ns", {}).get("ok") is True, str(got.get("planted_ns")))
    check("no verdict comes from a line the checked text logged", "planted_ghost" not in got, str(got.get("planted_ghost")))
    check("the lemma the replay rejected is no longer in the environment",
          any("planted_forged_lemma" in m["text"] and "unknown" in m["text"].lower() for m in r.messages),
          out[-300:])
    check("classical proof lists exactly the three standard axioms",
          sorted(got.get("planted_classical", {}).get("axioms", [])) == ["Classical.choice", "Quot.sound", "propext"],
          str(got.get("planted_classical")))
    for name, axioms in NATIVE_AXIOMS.items():
        check(f"{name}: the verdict lists the fixture's exact axiom names",
              got.get(name, {}).get("axioms") == axioms, str(got.get(name)))
        printed = next((m["text"] for m in r.messages if m["text"].startswith(f"'{name}' depends on axioms")), "")
        check(f"{name}: #print axioms shows the same names", printed == f"'{name}' depends on axioms: [{', '.join(axioms)}]",
              printed)
        check(f"{name}: the axiom audit took it back out of the environment, so it can be declared again",
              not any(f"`{name}` has already been declared" in m["text"] for m in r.messages), printed)
    check("control: the option probe fails outside the checker",
          "debug.skipKernelTC is on" in out, out[-300:])

    # the LLM proof path end to end: native_decide is refused, decide is accepted
    import synth
    ok_native, out_native = synth._try_lean_proof("", "2 + 2 = 4", "native_decide")
    ok_decide, _ = synth._try_lean_proof("", "2 + 2 = 4", "decide")
    check("synth proof check refuses native_decide end to end", ok_native is False, out_native[-200:])
    check("synth proof check accepts decide end to end", ok_decide is True)

    # native track: the same file elaborates after import Mathlib
    native = lss_config.project_dir("lean-native")
    if not os.path.isdir(native):
        check(f"{native} exists", False, "not a directory")
    else:
        ns = lean_server.get_server(native, lss_config.server_cfg())
        r = ns.check("import Mathlib\n" + lean.proof_check_text() + "\n" +
                     _call("theorem planted_mathlib (x : ℝ) : x + 0 = x := by simp", "planted_mathlib", 0),
                     timeout=300)
        v = _verdicts((r.stdout or "") + (r.stderr or "")).get("planted_mathlib")
        check("native track: a Mathlib proof passes after import Mathlib", v is not None and v.get("ok") is True, str(v))
        pr = lean.LeanChecker().try_proof_batch("", "∀ n : Nat, n + 0 = n", project_dir=native)
        check("native track: the tactic portfolio proves through verdicts", pr.proved, pr.error[:200])
        import benchmarks
        gcd = next(b for b in benchmarks.BENCHMARKS if b["name"] == "gcd")
        for stmt in ["∀ (a b : Nat), a = 0 → gcd' a b = b", "∀ (a b : Nat), b = 0 → gcd' a b = a",
                     "∀ (a b : Nat), b = a → gcd' a b = a"]:
            pr = lean.LeanChecker().try_proof_batch(gcd["lean_code"], stmt, func_name="gcd'", project_dir=native)
            check(f"native track: the portfolio proves {stmt} about a well-founded recursion", pr.proved, pr.error[:200])

    run_full_modularity()
    lean_server.shutdown_all()


def _mod(tag, tactic, abstract, inline):
    import lean
    return (f'lss_modular {tag} unit:records.order_pair stmt:"{lean._escape_lean_str(ORDER_PAIR_GOAL)}" '
            f'tactic:"{lean._escape_lean_str(tactic)}" abstract:[{abstract}] inline:[{inline}] heartbeats:0\n')


def _theorem(name, stmt, tactic):
    import lean
    body = "\n".join("  " + line for line in tactic.split("\n"))
    return lean.proof_check_call(f"theorem {name} : {stmt} := by\n{body}", name, 0) + "\n"


def run_full_modularity():
    print("=== full: ∀-abstraction and blame on FeatureSuite ===")
    import lean
    import lean_server
    import lss_config
    import callgraph

    rust_dir = os.path.expanduser("~/rust_benchmarks")
    if not os.path.isdir(os.path.join(rust_dir, "FeatureSuite", "Code")):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, "not a directory")
        return
    server = lean_server.get_server(lss_config.project_dir("aeneas"), lss_config.server_cfg())
    g = callgraph.for_project(rust_dir)
    base = (g.crate_text + "\nset_option maxRecDepth 2048\n"
            f"open Aeneas Aeneas.Std Result ControlFlow Error\nopen {g.crate}\n" +
            lean.proof_check_text() + "\n" + lean._aeneas_layer_text() + "\n")
    r0 = server.check(base, timeout=600)
    check("crate env built", r0.rc == 0 and r0.new_env is not None, (r0.stderr or "")[:300])
    if r0.new_env is None:
        return
    env0 = r0.new_env

    # the planted proof that looks inside swap passes plain checking ...
    r = server.check(_theorem("planted_through", ORDER_PAIR_GOAL, CALLER_THROUGH_CALLEE), env=env0, timeout=120)
    v = lean.parse_proof_verdicts(r.stderr).get("planted_through")
    check("planted proof through the callee passes plain checking", v is not None and v["ok"], str(v))
    # ... and fails the abstraction theorem, even with swap's full spec available
    r = server.check(_theorem("swap_full", SWAP_HOARE, "lss_spec_form\nunfold records.swap\nstep*") +
                     "lss_register_step swap_full\n" +
                     _mod("planted_through_mod", CALLER_THROUGH_CALLEE, "records.swap swap_full.step", "") +
                     _mod("planted_clean_mod", CALLER_TACTIC, "records.swap swap_full.step", "") +
                     _mod("planted_unconstrained_mod", CALLER_TACTIC, "records.swap _", ""),
                     env=env0, timeout=300)
    got = lean.parse_proof_verdicts(r.stderr)
    check("callee spec admitted", got.get("swap_full", {}).get("ok") is True, str(got.get("swap_full")))
    v = got.get("planted_through_mod.proof")
    check("planted proof through the callee fails the abstraction theorem",
          v is not None and v["ok"] is False and v["stage"] == "elab", str(v))
    v = got.get("planted_clean_mod.proof")
    check("planted clean proof passes the abstraction theorem (audit included)",
          v is not None and v["ok"] is True, str(v))
    v = got.get("planted_unconstrained_mod.proof")
    check("with the callee unconstrained the clean proof fails", v is not None and v["ok"] is False, str(v))

    # a weak callee spec: the caller fails; inlining the callee's body rescues it
    r = server.check(_theorem("swap_weak", SWAP_HOARE_HALF1, "lss_spec_form\nunfold records.swap\nstep*") +
                     "lss_register_step swap_weak\n" +
                     _theorem("caller_weak", ORDER_PAIR_GOAL, CALLER_TACTIC) +
                     _mod("weak_inline_mod", CALLER_TACTIC, "", "records.swap"),
                     env=env0, timeout=300)
    got = lean.parse_proof_verdicts(r.stderr)
    check("weak callee spec: the caller's proof fails", got.get("caller_weak", {}).get("ok") is False,
          str(got.get("caller_weak")))
    check("weak callee spec: inlining the callee's body rescues it",
          got.get("weak_inline_mod.proof", {}).get("ok") is True, str(got.get("weak_inline_mod.proof")))

    # the same through the pipeline: modular flag on success, blame by name on failure
    swap_q = f"{g.crate}.records.swap"
    checker = lean.LeanChecker()
    pr = checker.try_aeneas(SWAP_HOARE, "records.swap", rust_dir, candidate_id="mod_swap")
    check("pipeline: swap proved and modular (no external callee)", pr.proved and pr.modular is True, str(pr)[:300])
    pr = checker.try_aeneas(ORDER_PAIR_GOAL, "records.order_pair", rust_dir, candidate_id="mod_order_pair")
    check("pipeline: order_pair proved and modular through swap's spec",
          pr.proved and pr.modular is True and pr.needs_callee_body == [], str(pr)[:300])
    weak = lean.LeanChecker()
    pr = weak.try_aeneas(SWAP_HOARE_HALF1, "records.swap", rust_dir, candidate_id="mod_swap_weak")
    check("pipeline: weak swap spec proved", pr.proved, str(pr)[:300])
    pr = weak.try_aeneas(ORDER_PAIR_GOAL, "records.order_pair", rust_dir, candidate_id="mod_order_pair_weak")
    check("pipeline: order_pair fails and blames swap's spec by name",
          not pr.proved and pr.blamed_callees == [swap_q], str(pr)[:300])


if static:
    run_static()
    run_static_verdicts()
    run_static_no_unverdicted()
    run_static_modularity()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
