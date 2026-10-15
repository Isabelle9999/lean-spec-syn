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
# test also reads `#print axioms` for the same declaration and compares.
NATIVE_AXIOMS = {
    "planted_native": ["planted_native._native.native_decide.ax_1"],
    "planted_decide_native": ["planted_decide_native._native.decide.ax_1"],
}

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
    sent = fake.sent[-1] if fake.sent else ""
    i_pc, i_layer = sent.find('elab "lss_check_proof '), sent.find("macro \"lss_spec_form\"")
    check("crate env holds proof_check.lean before aeneas_layer.lean", 0 <= i_pc < i_layer, f"{i_pc} {i_layer}")


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
          fake.sent[-1].count("lss_check_proof ") >= 30 and "private theorem" not in fake.sent[-1],
          str(fake.sent[-1].count("lss_check_proof ")))

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
    state = {"ok": True, "env": 3, "admitted": [], "restarts": 0}
    setattr(checker, "_aeneas_env_for", lambda project_dir: state)
    fake = _FakeServer(lambda code: _verdict_line("_aeneas_a", False, "axioms", ["sorryAx"]))
    pr = _with_fake(fake, lambda: checker.try_aeneas("stmt", "f", "/nonexistent"))
    check("aeneas layer: a rejected attempt and a missing verdict prove nothing",
          not pr.proved and not state["admitted"], str(pr)[:200])

    def reply_aeneas(code):
        out = _verdict_line("_aeneas_a", False, "elab") + _verdict_line("_aeneas_b", True, "ok", ["propext"])
        return out + (_verdict_line("lss_admitted_0", True) if "name:lss_admitted_0 " in code else "")
    fake = _FakeServer(reply_aeneas)
    pr = _with_fake(fake, lambda: checker.try_aeneas("stmt", "f", "/nonexistent"))
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
    text += "set_option debug.skipKernelTC false\n"
    text += "".join(f"#print axioms {n}\n" for n in NATIVE_AXIOMS)
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
    check("classical proof lists exactly the three standard axioms",
          sorted(got.get("planted_classical", {}).get("axioms", [])) == ["Classical.choice", "Quot.sound", "propext"],
          str(got.get("planted_classical")))
    for name, axioms in NATIVE_AXIOMS.items():
        check(f"{name}: the verdict lists the fixture's exact axiom names",
              got.get(name, {}).get("axioms") == axioms, str(got.get(name)))
        printed = next((m["text"] for m in r.messages if m["text"].startswith(f"'{name}' depends on axioms")), "")
        check(f"{name}: #print axioms shows the same names", printed == f"'{name}' depends on axioms: [{', '.join(axioms)}]",
              printed)
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

    lean_server.shutdown_all()


if static:
    run_static()
    run_static_verdicts()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
