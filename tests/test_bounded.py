import json
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

import bounded  # noqa: E402
import translation_check as tc  # noqa: E402  (bounded puts tools/ on the path)

static = "--static" in sys.argv
fails = []

U32 = ("int", "Std.U32")
I8 = ("int", "Std.I8")
VEC = ("vec", U32)
PAIR = ("struct", "records.Pair", [("first", U32), ("second", U32)])


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


def _key(v):
    return json.dumps(v, sort_keys=True)


def run_static_values():
    print("=== static: inputs, perturbations, shrinking ===")
    rows = bounded.sample_rows([U32, VEC], seed=1)
    check("sampling is deterministic for a seed", rows == bounded.sample_rows([U32, VEC], seed=1))
    check("sampling stays within the row budget, without duplicates",
          len(rows) == bounded.ROWS and len({_key(r) for r in rows}) == len(rows), str(len(rows)))
    check("edge values come first: 0, 1, max, max-1 for U32",
          [r[0] for r in rows[:4]] == [0, 1, 4294967295, 4294967294], str([r[0] for r in rows[:4]]))
    check("signed edges include min and -1", {-128, -1, 127} <= set(bounded.edge_values(I8)))
    check("every sampled value renders as a Lean literal",
          all(tc.lean_literal(t, v) for r in rows for t, v in zip([U32, VEC], r)))
    for T, v in [(U32, 5), (U32, "7"), (VEC, [1, 2]), (VEC, []), (PAIR, {"first": 1, "second": 2}),
                 (("bool",), True), (("option", U32), None), (("tuple", [U32, ("bool",)]), [3, False])]:
        ps = bounded.perturb(T, v)
        check(f"perturbations of a {T[0]} exist and differ from it",
              bool(ps) and all(_key(p) != _key(v) for p in ps), str(ps))
    check("int perturbations stay in range", all(0 <= p <= 4294967295 for p in bounded.perturb(U32, 4294967295)))
    sh = bounded.shrink(U32, 100)
    check("shrinking an int offers 0, the powers of two and steps toward it, all smaller",
          sh[0] == 0 and {1, 2, 64, 50, 75, 99} <= set(sh) and max(sh) < 100, str(sh))
    check("shrinking a list drops elements first", bounded.shrink(VEC, [3, 4])[:2] == [[4], [3]])


NODE = ("enum", "C.Node", [("mk", [U32, ("option", ("self",)), ("option", ("self",))])], "C.Node Aeneas.Std.U32")
LIST = ("list_enum", "C.List", "Nil", "Cons", U32, "C.List Aeneas.Std.U32")


def run_static_recursive():
    print("=== static: generic and recursive types ===")
    got = bounded.type_ir(["enum", "C.List", [["Cons", [["int", "Std.U32"], ["self"]]], ["Nil", []]],
                           "C.List Aeneas.Std.U32"])
    check("Lean's Nil/Cons(T, Self) inductive reads as a list_enum, with its type text",
          got == ("list_enum", "C.List", "Nil", "Cons", U32, "C.List Aeneas.Std.U32"), str(got))
    got = bounded.type_ir(["enum", "C.Node", [["mk", [["int", "Std.U32"], ["option", ["self"]], ["option", ["self"]]]]],
                           "C.Node Aeneas.Std.U32"])
    check("a tree reads as an enum that refers to itself", got == NODE, str(got))
    check("an array's length is read from its literal",
          bounded.type_ir(["array", ["bool"], "8#usize"]) == ("array", ("bool",), 8))
    for j in [{"unsupported": "function"}, ["array", ["bool"], "n"], ["int", "Std.Foo"]]:
        try:
            bounded.type_ir(j)
            ok = False
        except tc.Unsupported:
            ok = True
        check(f"what Lean could not read is unsupported: {j}", ok)
    rows = bounded.sample_rows([NODE, LIST], seed=3)
    check("trees and lists are sampled, every one a finite value that renders",
          len(rows) > 10 and all(tc.lean_literal(NODE, r[0]) and tc.lean_literal(LIST, r[1]) for r in rows))

    def depth(v):
        return 1 + max([depth(c) for c in v["args"][1:] if c is not None], default=0)
    check("a sampled tree is at most a few levels deep", max(depth(r[0]) for r in rows) <= 5,
          str(max(depth(r[0]) for r in rows)))
    v = {"tag": "mk", "args": [3, None, {"tag": "mk", "args": [4, None, None]}]}
    check("a tree literal names its constructor in full",
          tc.lean_literal(NODE, v) == "(C.Node.mk 3#u32 none (some (C.Node.mk 4#u32 none none)))",
          tc.lean_literal(NODE, v))
    check("a tree shrinks to its subtrees", bounded.shrink(NODE, v) == [v["args"][2]], str(bounded.shrink(NODE, v)))
    ps = bounded.perturb(NODE, v)
    check("perturbing a tree changes its value", bool(ps) and all(_key(p) != _key(v) for p in ps), str(ps))
    defs = []
    enc = tc.lean_encode_expr(("option", NODE), "v", defs)
    check("a tree's encoder is a partial def sent before the command",
          len(defs) == 1 and defs[0].startswith("partial def lss_enc_0 (x : (C.Node Aeneas.Std.U32)) : String")
          and "lss_enc_0 x" in defs[0] and "lss_enc_0 x" in enc, f"{defs} {enc}")
    import re
    chain = ("struct", "C.Chain", [("items", LIST), ("next", ("option", ("self",)))], "C.Chain")
    defs = []
    tc.lean_encode_expr(chain, "v", defs)
    names = [re.match(r"partial def (\w+)", d).group(1) for d in defs]
    called = [set(re.findall(r"lss_enc_\d+", d.split(":=", 1)[1])) for d in defs]
    check("every encoder def comes after the defs it calls (a recursive struct holding a crate list)",
          len(defs) == 2 and all(c <= set(names[:k + 1]) for k, c in enumerate(called)), str(defs))
    check("a generic type's ascription is its type text",
          tc.lean_type_str(("vec", NODE)) == "(alloc.vec.Vec (C.Node Aeneas.Std.U32))", tc.lean_type_str(("vec", NODE)))
    check("a monomorphic struct still ascribes by name", tc.lean_type_str(PAIR) == "records.Pair")


def run_static_commands():
    print("=== static: lean command text ===")
    stmt = '∀ (x : Std.U32), f x ⦃ r => r.val = x.val + 1 ⦄'
    check("the plan command names the tag and the crate", bounded.plan_command("t0", "C", stmt).startswith(
        'lss_eval_plan t0 crate:C stmt:"∀ (x : Std.U32), f x ⦃'), bounded.plan_command("t0", "C", stmt))
    cmd = bounded.eval_command("t1", "C", stmt, [U32], U32, [[0], [5]])
    check("eval command names the tag and crate and quotes the statement",
          cmd.startswith('lss_eval_spec t1 crate:C stmt:"∀ (x : Std.U32), f x ⦃'), cmd[:80])
    check("eval command has one row per input", cmd.endswith('rows:[["0#u32"], ["5#u32"]]'), cmd[-60:])
    check("the encoder's quotes are escaped", 'enc:"fun v => (\\"\\\\\\"\\" ++ toString' in cmd, cmd[90:200])
    cmd = bounded.eval_command("t1", "C", stmt, [U32], ("option", NODE), [[0]])
    check("a recursive result type's encoder def comes first",
          cmd.startswith("partial def lss_enc_0") and "\nlss_eval_spec t1" in cmd, cmd[:120])
    cmd = bounded.eval_command("t1", "C", stmt, [U32], None, [[0]])
    check("a result type with no encoder evaluates outcomes only", 'enc:"fun _ => \\"\\""' in cmd, cmd[60:160])
    post = bounded.post_command("t2", "C", stmt, [U32], U32, [5], [6, 7])
    check("post command carries the row and the wrong outputs",
          post.startswith("lss_eval_post t2 crate:C ") and post.endswith('row:["5#u32"] outs:["6#u32", "7#u32"]'),
          post[-60:])
    text = ('x.lean:1:0: warning: LSS_EVAL {"tag":"a","ok":true,"kind":"spec","rows":[]}\n'
            'LSS_EVAL {broken\nLSS_EVAL {"tag":"b","ok":false,"detail":"no"}')
    got = bounded.parse_evals(text)
    check("parse_evals reads every message and skips broken lines", set(got) == {"a", "b"}, str(got))
    binders = [{"k": "type", "v": "Aeneas.Std.I32", "name": "T"}, {"k": "inst", "v": "C.I32.Insts.Ord", "name": "O"},
               {"k": "class"}, {"k": "law"}, {"k": "arg", "i": 1}, {"k": "arg", "i": 0}, {"k": "det"}, {"k": "hyp"}]
    ref = bounded.refutation_text("rf", "S", binders, ["C.I32.Insts.Ord"], [U32, ("bool",)], U32,
                                  [5, True], "violates", '"6"')
    check("refutation applies every binder explicitly, in order: the type, the instance, the class "
          "instance, the law by lss_law_tac, the witness, a defined binder by unification, a hypothesis by decide",
          "(@h (Aeneas.Std.I32) (C.I32.Insts.Ord) (inferInstance) (by lss_law_tac [C.I32.Insts.Ord]) (true) (5#u32) _ "
          "(by first | rfl | decide | simp_all | omega))" in ref, ref)
    check("refutation computes the call's value without restating it",
          "have hv : (Aeneas.Std.Result.ok y : Aeneas.Std.Result _) = Aeneas.Std.Result.ok (6#u32) := "
          "hy.symm.trans (by first | rfl | decide)" in ref, ref)
    check("refutation of a violated postcondition decides it", ref.endswith("first | decide | simp | omega"))
    ref = bounded.refutation_text("rf", "S", [{"k": "arg", "i": 0}], [], [U32], U32, [0], "fail",
                                  "Aeneas.Std.Error.integerOverflow")
    check("refutation of a failing call needs only the constructor clash",
          ref.endswith("cases hv") and "Result.fail Aeneas.Std.Error.integerOverflow" in ref, ref)


def _plan(free=None, ret=None, binders=None, insts=None):
    free = free if free is not None else [{"name": "x", "type": "Aeneas.Std.U32", "ir": ["int", "Std.U32"]}]
    return {"ok": True, "kind": "spec", "free": free, "ret": ret or ["int", "Std.U32"],
            "binders": binders or [{"k": "arg", "i": 0}], "insts": insts or []}


class FakeLean:
    """bounded._Lean with scripted answers: `row_outcome(row)` gives one row's
    result, `post_outcome(row, out)` one perturbed output's, `plan` the plan."""
    calls = []

    def __init__(self, row_outcome, post_outcome=None, kernel=True, timeout=False, plan=None):
        self.row_outcome, self.post_outcome, self.kernel, self.timeout = row_outcome, post_outcome, kernel, timeout
        self.plan_ = plan or _plan()
        self.n = 0
        self.sent = []

    def __call__(self, checker, project_dir):
        return self

    def plan(self, stmt):
        return (None, "timeout") if self.timeout == "plan" else (self.plan_, "")

    def eval(self, stmt, args, ret, rows):
        if self.timeout:
            return None, "timeout"
        return {"kind": "dspec" if "div" in stmt else "spec", "rows": [self.row_outcome(r) for r in rows]}, ""

    def post(self, stmt, args, ret, row, outs):
        return [self.post_outcome(row, o) for o in outs] if self.post_outcome else None

    def run(self, text):
        self.sent.append(text)
        name = text.split(" name:")[1].split()[0]
        return f'LSS_PROOF {{"name":"{name}","ok":{"true" if self.kernel else "false"},"stage":"ok","detail":"","axioms":[]}}', ""


def _check(fake, stmt="S"):
    old_lean = bounded._Lean
    bounded._Lean = fake  # type: ignore[assignment]
    try:
        return bounded.check_spec(None, stmt, "f", "/p")
    finally:
        bounded._Lean = old_lean


def _ok(v):
    return {"outcome": "holds", "value": json.dumps(str(v))}


def run_static_check():
    print("=== static: the verdict ===")
    # f x = x, spec "r.val < 5": false from 5 on; the witness shrinks to 5
    fake = FakeLean(lambda r: _ok(r[0]) if int(r[0]) < 5 else {"outcome": "violates", "value": json.dumps(str(r[0]))})
    v = _check(fake)
    check("a false spec is refuted", v["status"] == "refuted", str(v))
    check("the witness shrinks to the smallest failing input", v.get("witness") == [5], str(v.get("witness")))
    check("the refutation is kernel-checked when lss_check_proof accepts it",
          v.get("kernel") is True and "5#u32" in fake.sent[-1], fake.sent[-1][-200:] if fake.sent else "")
    check("the feedback names the input by its binder and the output as a literal",
          "(x := 5#u32)" in v.get("feedback", "") and "returned 5#u32" in v.get("feedback", ""), v.get("feedback"))
    gen = _plan(binders=[{"k": "type", "v": "Aeneas.Std.U32", "name": "T"}, {"k": "arg", "i": 0}])
    v = _check(FakeLean(lambda r: {"outcome": "violates", "value": '"1"'}, plan=gen))
    check("a generic spec's refutation says at which instantiation",
          v["status"] == "refuted" and "at T := Aeneas.Std.U32" in v["feedback"]
          and v["instantiation"] == "T := Aeneas.Std.U32", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "violates", "value": '"1"'}, kernel=False))
    check("a refutation the kernel does not check is evaluation-only", v["status"] == "refuted" and v["kernel"] is False)
    v = _check(FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"}))
    check("a spec whose call fails is refuted", v["status"] == "refuted" and v["outcome"] == "fail", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "div", "value": ""}))
    check("divergence refutes a ⦃ ⦄ spec", v["status"] == "refuted", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "div", "value": ""}), stmt="div S")
    check("divergence is allowed by a ⦃ ⦄div spec", v["status"] == "pass", str(v))

    def same(r):
        return _ok(r[0])
    v = _check(FakeLean(same, lambda row, o: "holds"))
    check("a spec that accepts every wrong output, and claims no success, is vacuous",
          v["status"] == "vacuous" and "says nothing" in v.get("feedback", ""), str(v))
    v = _check(FakeLean(same, lambda row, o: "violates" if int(o) != int(row[0]) else "holds"))
    check("an exact spec passes: it rejects the wrong outputs", v["status"] == "pass" and v["warning"] is None, str(v))
    v = _check(FakeLean(lambda r: _ok(r[0]) if int(r[0]) < 2 else {"outcome": "discard"}, lambda row, o: "holds"))
    check("a no-fail statement (hypotheses filter, any output accepted) is kept",
          v["status"] == "pass", str(v))
    check("rare hypotheses give the narrow warning, not a rejection", v["warning"] == "narrow", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "discard"}))
    check("no input meeting the hypotheses gives the no_witness warning",
          v["status"] == "pass" and v["warning"] == "no_witness", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "error", "detail": "boom"}))
    check("a spec none of whose rows evaluates is skipped, with the error",
          v == {"status": "skipped", "detail": "boom"}, str(v))
    v = _check(FakeLean(same, timeout=True))
    check("a diverging evaluation is a timeout, not a refutation", v["status"] == "timeout", str(v))
    v = _check(FakeLean(same, timeout="plan"))
    check("a plan that times out is a timeout", v["status"] == "timeout", str(v))
    for detail in ["not evaluated: the crate has no instance of C.Hash",
                   "not evaluated: postcondition: not Decidable: ∀ t, r.2 t = t",
                   "not evaluated: the crate's instance does not meet the hypothesis `h`"]:
        f = FakeLean(same, plan={"ok": False, "detail": detail})
        v = _check(f)
        check(f"a statement the plan cannot evaluate goes on unevaluated: {detail[15:50]}",
              v == {"status": "not_evaluated", "detail": detail[len("not evaluated:"):].strip()}, str(v))
    v = _check(FakeLean(same, plan={"ok": False, "detail": "does not parse"}))
    check("any other plan error is skipped", v == {"status": "skipped", "detail": "does not parse"}, str(v))
    v = _check(FakeLean(same, plan=_plan(free=[{"name": "f", "type": "U32 → U32", "ir": {"unsupported": "fun"}}])))
    check("a binder whose type has no sampler is not evaluated", v["status"] == "not_evaluated" and "fun" in v["detail"],
          str(v))
    noret = _plan(ret={"unsupported": "a function"})
    f = FakeLean(lambda r: {"outcome": "violates", "value": ""}, plan=noret)
    v = _check(f)
    check("with a result type that has no encoder, a violation is refuted by evaluation only",
          v["status"] == "refuted" and v["kernel"] is False and not f.sent and "returned a value" in v["feedback"],
          str(v))
    v = _check(FakeLean(same, lambda row, o: "holds", plan=noret))
    check("and no perturbation is tried, so it is not called vacuous", v["status"] == "pass", str(v))


def _lean_names(path):
    """every name a Lean file declares at top level (defs, theorems, instances, inductives, syntax)."""
    import re
    with open(path, encoding="utf-8") as f:
        text = f.read()
    return set(re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:partial |unsafe |noncomputable )*"
                          r"(?:def|theorem|opaque|inductive|structure|instance|abbrev|syntax|macro) (\w+)",
                          text, re.MULTILINE))


def run_static_run():
    print("=== static: what each command is sent with ===")
    here = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lean")
    mine = _lean_names(os.path.join(here, "bounded.lean"))
    others = set().union(*(_lean_names(os.path.join(here, f)) for f in
                           ("proof_check.lean", "aeneas_layer.lean", "wf_gate.lean", "wf_gate_aeneas.lean")))
    check("bounded.lean declares the evaluation commands, and nothing the files in the same env declare",
          {"lssMono", "lssShapeOf", "lssTypeIR", "lssProveLaw", "lssOutcome"} <= mine and not (mine & others),
          str(sorted(mine & others)))

    class Server:
        sent = []

        def check(self, code, timeout=None, env=None):
            self.sent.append((code, env))

            class R:
                timed_out = False
                stdout, stderr = 'LSS_EVAL {"tag":"derive","ok":true,"derived":["C.T"],"via_beq":[],"none":[]}', ""
                new_env = 77
            return R()

    class Checker:
        lean_calls = 0
        state = {"ok": True, "env": 42, "env0": 41, "crate": "C"}

        def _aeneas_env_for(self, project_dir):
            return self.state

    server = Server()
    old = bounded._lean_server.get_server
    bounded._lean_server.get_server = lambda *a, **k: server  # type: ignore[assignment]
    try:
        ck = Checker()
        lean_ = bounded._Lean(ck, "/p")
        lean_.run("lss_eval_spec x")
        lean_.run("lss_eval_spec y")
        bounded._Lean(ck, "/p").run("lss_eval_spec z")
        ck.state = {"ok": True, "env": 52, "env0": 51, "crate": "C"}  # the crate env was rebuilt
        bounded._Lean(ck, "/p").run("lss_eval_spec w")
    finally:
        bounded._lean_server.get_server = old
    code, env = server.sent[0]
    check("the check's env is built on the crate env as built before the crate is opened", env == 41, str(env))
    check("it holds the gate's Decidable instances, then bounded.lean, then DecidableEq for the crate's types",
          code.index("lssSubtypeDecEq") < code.index("deriving instance DecidableEq for Aeneas.Std.Result")
          < code.index("elab \"lss_eval_plan ") < code.index("lss_derive_deceq crate:C"), code[-200:])
    check("it is built once per crate env, every command then runs in it, after opening the crate",
          [e for _, e in server.sent[1:4]] == [77, 77, 77] and server.sent[1][0] == "open C\nlss_eval_spec x",
          str([(c[:30], e) for c, e in server.sent]))
    check("a rebuilt crate env gets a new check env", server.sent[4][1] == 51 and server.sent[5][1] == 77,
          str([(c[:30], e) for c, e in server.sent[4:]]))
    check("what was derived is kept with the crate env", ck.state.get("check_derive", {}).get("derived") == ["C.T"],
          str(ck.state.get("check_derive")))

    class Broken(Server):
        def check(self, code, timeout=None, env=None):
            class R:
                timed_out = False
                stdout, stderr = ":778:30: error: unexpected token ':='; expected '}'", ""
                new_env = 78
            return R()
    bounded._lean_server.get_server = lambda *a, **k: Broken()  # type: ignore[assignment]
    try:
        fresh = Checker()
        fresh.state = {"ok": True, "env": 62, "env0": 61, "crate": "C"}
        bounded.check_spec(fresh, "S", "f", "/p")
        raised = ""
    except RuntimeError as e:
        raised = str(e)
    finally:
        bounded._lean_server.get_server = old
    check("bounded.lean failing to build stops the run with Lean's error, never a skipped verdict",
          "does not build" in raised and "778:30" in raised, raised)

    class Lost(Server):
        def check(self, code, timeout=None, env=None):
            class R:
                timed_out, mem_killed = False, True
                stdout, stderr = "", ""
                new_env = None
            return R()
    bounded._lean_server.get_server = lambda *a, **k: Lost()  # type: ignore[assignment]
    try:
        fresh = Checker()
        fresh.state = {"ok": True, "env": 72, "env0": 71, "crate": "C"}
        v = bounded.check_spec(fresh, "S", "f", "/p")
    except Exception as e:  # anything raised stops the run
        v = {"status": "raised", "detail": repr(e)}
    finally:
        bounded._lean_server.get_server = old
    check("a check env the server lost (a memory kill) skips the candidate, it does not stop the run",
          v.get("status") == "skipped" and "check env lost" in v.get("detail", ""), str(v))


def run_static_synth():
    print("=== static: wiring into validate ===")
    import synth
    import gate
    import lean

    class Checker:
        def __init__(self):
            self.aeneas = []

        def try_aeneas(self, stmt, func, project_dir, candidate_id=None):
            self.aeneas.append(stmt)
            return lean.ProofResult(proved=True, method="aeneas:a", error="")

    class LLM:
        prompts = []

        def _ask(self, prompt):
            self.prompts.append(prompt)
            return "theorem s_fixed : FIXED := sorry" if "theorem s :" in prompt else ""

    verdicts = {"S": {"status": "refuted", "kernel": True, "witness": [5], "outcome": "violates", "value": '"5"',
                      "feedback": "On input (5#u32) the function returned \"5\", and the statement is false there"},
                "FIXED": {"status": "timeout", "detail": "timeout"},
                "V": {"status": "vacuous", "feedback": "says nothing"}}
    old_gate, old_b = synth._gate.check_candidate, synth._bounded.check_spec
    synth._gate.check_candidate = lambda *a, **k: [{"check": c, "ok": True, "detail": ""} for c in gate.checks_for("rust-aeneas")]
    synth._bounded.check_spec = lambda checker, stmt, unit, project_dir: dict(verdicts[stmt])
    try:
        checker, llm = Checker(), LLM()
        specs = [{"name": "s", "stmt": "S"}, {"name": "v", "stmt": "V"}]
        synth.validate(specs, "def f (x : U32) : Result U32 := ok x", [], checker, llm=llm, func_name="f",
                       project_dir="/p", source="rust-aeneas")
    finally:
        synth._gate.check_candidate, synth._bounded.check_spec = old_gate, old_b
    s = specs[0]
    check("a refuted spec gets status refuted, by kernel", s["status"] == "refuted" and s["refuted_by"] == "kernel", str(s))
    check("a vacuous spec is rejected", specs[1]["status"] == "rejected" and specs[1]["fail_gate"] == "vacuous",
          str(specs[1]))
    check("the repair prompt carries the counterexample", any("On input (5#u32)" in p for p in llm.prompts))
    check("a vacuous spec gets a repair prompt too", any("says nothing" in p for p in llm.prompts))
    rep = [x for x in specs if x["name"] == "s_r"]
    check("the repaired statement is checked again and, after a timeout, goes to the provers",
          len(rep) == 1 and rep[0]["stmt"] == "FIXED" and rep[0]["status"] == "proved" and checker.aeneas == ["FIXED"],
          str(rep))
    check("a repaired spec is not repaired again", sum(1 for x in specs if x["name"].endswith("_r_r")) == 0)

    # a gate rejection: the repair reply is read whole, and the event says why
    emitted, gated = [], []
    old_gate, old_emit = synth._gate.check_candidate, synth.events.emit
    synth._gate.check_candidate = lambda checker, text, *a, **k: gated.append(text) or [
        {"check": "one_theorem", "ok": True, "detail": ""},
        {"check": "conclusion_shape", "ok": False, "detail": "argument `none` is not a bound variable"}]
    synth.events.emit = lambda kind, **f: emitted.append((kind, f))

    class FixLLM:
        def _ask(self, prompt):
            return "Here is the fix: theorem g (o : Option U32) : f o ⦃ r => r = o ⦄ := sorry"
    try:
        g = [{"name": "g", "stmt": "f none ⦃ r => True ⦄"}]
        synth.validate(g, "def f (x : U32) : Result U32 := ok x", [], Checker(), llm=FixLLM(), func_name="f",
                       project_dir="/p", source="rust-aeneas")
    finally:
        synth._gate.check_candidate, synth.events.emit = old_gate, old_emit
    check("the gate sees the call in normal form: its argument `none` defined by a hypothesis",
          gated and gated[0] == "theorem g : ∀ (lss_a0 : _), lss_a0 = none → f lss_a0 ⦃ r => True ⦄ := sorry", str(gated))
    rej = [f for k, f in emitted if k == "verdict" and f.get("status") == "rejected"]
    check("a gate rejection's event names the failing check, its detail and the statement as repaired",
          len(rej) == 1 and rej[0].get("check") == "conclusion_shape" and "not a bound variable" in rej[0].get("detail", "")
          and rej[0].get("stmt") == "∀ (o : Option U32), f o ⦃ r => r = o ⦄", str(rej))


def run_full():
    print("=== full: bounded checking on FeatureSuite ===")
    import lean
    import lean_server
    import lss_config

    rust_dir = os.path.expanduser("~/rust_benchmarks")
    if not os.path.isdir(os.path.join(rust_dir, "FeatureSuite", "Code")):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, "not a directory")
        return
    checker = lean.LeanChecker()
    v = bounded.check_spec(checker, "∀ (value : Std.U32), identity value ⦃ r => r.val = value.val + 1 ⦄",
                           "identity", rust_dir)
    check("planted false spec is refuted", v["status"] == "refuted", str(v))
    check("its witness shrinks to 0", v.get("witness") == [0], str(v.get("witness")))
    check("its refutation is kernel-checked", v.get("kernel") is True, str(v))
    v = bounded.check_spec(checker, "∀ (value : Std.U32), identity value ⦃ _ => True ⦄", "identity", rust_dir)
    check("⦃ _ => True ⦄ on a function that never fails is vacuous", v["status"] == "vacuous", str(v))
    v = bounded.check_spec(checker, "∀ (value : Std.U32), identity value ⦃ r => r = value ⦄", "identity", rust_dir)
    check("an exact spec passes", v["status"] == "pass" and v["warning"] is None, str(v))
    lean_ = bounded._Lean(checker, rust_dir)
    got = lean_.post("∀ (value : Std.U32), identity value ⦃ r => r = value ⦄", [U32], U32, [5],
                     bounded.perturb(U32, 5))
    check("an exact spec rejects every perturbed output", got is not None and set(got) == {"violates"}, str(got))
    v = bounded.check_spec(checker, "∀ (value : Std.U32), value.val = 12345 → identity value ⦃ r => r = value ⦄",
                           "identity", rust_dir)
    check("precondition value = 12345 only warns", v["status"] == "pass" and v["warning"] in ("narrow", "no_witness"),
          str(v))
    v = bounded.check_spec(checker, "∀ (p : records.Pair), records.swap p ⦃ r => r.first = p.first ⦄",
                           "records.swap", rust_dir)
    check("a false spec on a struct is refuted", v["status"] == "refuted", str(v))
    arr = "∀ (values : Array Std.U32 8#usize) (target : Std.U32), search.count_occurrences values target"
    v = bounded.check_spec(checker, arr + " ⦃ r => r.val ≤ 8 ⦄", "search.count_occurrences", rust_dir)
    check("a true spec on a loop over an array passes", v["status"] == "pass", str(v))
    v = bounded.check_spec(checker, arr + " ⦃ r => r.val = 0 ⦄", "search.count_occurrences", rust_dir)
    check("a false spec on a loop over an array is refuted", v["status"] == "refuted", str(v))
    v = bounded.check_spec(checker, "∀ (values : alloc.vec.Vec Std.U32), vectors.reverse values ⦃ r => r.val = values.val ⦄",
                           "vectors.reverse", rust_dir)
    check("a false spec on a vector is refuted, with a short witness",
          v["status"] == "refuted" and len(v.get("witness", [[]])[0]) == 2, str(v))

    run_planted(checker)

    # a diverging evaluation: the server times out, restarts, and the next check works
    state = checker._aeneas_env_for(rust_dir)
    server = lean_server.get_server(lss_config.project_dir("aeneas"))
    r = server.check("partial def lss_spin (x : Std.U32) : Result Std.U32 := lss_spin x", env=state["env0"], timeout=60)
    check("diverging helper added", r.rc == 0 and r.new_env is not None, (r.stderr or "")[:200])
    if r.new_env is not None:
        state["env0"] = r.new_env
        old = bounded.EVAL_TIMEOUT
        bounded.EVAL_TIMEOUT = 20
        try:
            ev, why = bounded._Lean(checker, rust_dir).eval("∀ (x : Std.U32), lss_spin x ⦃ _ => True ⦄",
                                                            [U32], U32, [[0]])
        finally:
            bounded.EVAL_TIMEOUT = old
        check("a diverging evaluation is reported as a timeout", ev is None and why == "timeout", f"{ev} {why}")
        v = bounded.check_spec(checker, "∀ (value : Std.U32), identity value ⦃ r => r = value ⦄", "identity", rust_dir)
        check("after the timeout the crate env is rebuilt and checks still run", v["status"] == "pass", str(v))
    lean_server.shutdown_all()


PLANTED_TYPES = """-- hand-written in the shape Aeneas generates, for LSS's tests
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace LssPlanted

/-- [lss_planted::List] -/
inductive List (T : Type) where
| Cons : T → List T → List T
| Nil : List T

/-- [lss_planted::Ordering] -/
inductive Ordering where
| Less : Ordering
| Equal : Ordering
| Greater : Ordering

/-- Trait declaration: [lss_planted::Ord]
    Source: 'src/lib.rs', lines 1:0-3:1 -/
structure Ord (Self : Type) where
  cmp : Self → Self → Result Ordering

/-- Trait declaration: [lss_planted::Hash]
    Source: 'src/lib.rs', lines 4:0-6:1 -/
structure Hash (Self : Type) where
  hash : Self → Result Std.U32

/-- [lss_planted::Node] -/
inductive Node (T : Type) where
| mk : T → Option (Node T) → Option (Node T) → Node T

end LssPlanted
"""

PLANTED_FUNS = """-- hand-written in the shape Aeneas generates, for LSS's tests
import Aeneas
import LssPlanted.Code.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace LssPlanted

/-- [lss_planted::head] -/
def head {T : Type} (l : List T) : Result T :=
  match l with
  | List.Cons x _ => ok x
  | List.Nil => fail panic

/-- [lss_planted::{lss_planted::Ord for i32}::cmp] -/
def OrdI32.cmp (x : Std.I32) (y : Std.I32) : Result Ordering :=
  if x < y then ok Ordering.Less else if x = y then ok Ordering.Equal else ok Ordering.Greater

/-- Trait implementation: [lss_planted::{lss_planted::Ord for i32}] -/
@[reducible]
def I32.Insts.LssPlantedOrd : Ord Std.I32 := {
  cmp := OrdI32.cmp
}

/-- [lss_planted::max_of] -/
def max_of {T : Type} (OrdInst : Ord T) (a : T) (b : T) : Result T := do
  let o ← OrdInst.cmp a b
  match o with
  | Ordering.Less => ok b
  | _ => ok a

/-- [lss_planted::hash_of] -/
def hash_of {T : Type} (HashInst : Hash T) (x : T) : Result Std.U32 :=
  HashInst.hash x

/-- [lss_planted::singleton] -/
def singleton {T : Type} (v : T) : Result (Option (Node T)) :=
  ok (some (Node.mk v none none))

/-- [lss_planted::nth_back] -/
def nth_back {T : Type} (l : List T) (i : Std.U32) : Result (T × (T → List T)) :=
  match l with
  | List.Cons x tl =>
    if i = 0#u32 then ok (x, fun t => List.Cons t tl) else fail panic
  | List.Nil => fail panic

end LssPlanted
"""

PLANTED_UNITS = ["head", "OrdI32.cmp", "max_of", "hash_of", "singleton", "nth_back"]

ORD_LAW = ("∀ {T : Type} (OrdInst : LssPlanted.Ord T) [LinearOrder T] (hcmp : ∀ a b, OrdInst.cmp a b = "
           "ok (if a < b then LssPlanted.Ordering.Less else if a = b then LssPlanted.Ordering.Equal "
           "else LssPlanted.Ordering.Greater)) (a b : T), ")


def planted_crate():
    """a crate written in Aeneas's shape: generic functions, a trait with an instance and
    one without, a tree, a backward function. returns its directory."""
    import tempfile
    tmp = tempfile.mkdtemp()
    code = os.path.join(tmp, "LssPlanted", "Code")
    os.makedirs(code)
    with open(os.path.join(code, "Types.lean"), "w", encoding="utf-8") as f:
        f.write(PLANTED_TYPES)
    with open(os.path.join(code, "Funs.lean"), "w", encoding="utf-8") as f:
        f.write(PLANTED_FUNS)
    decls = [{"kind": "function", "is_local": True, "lean_name": f"LssPlanted.{u}", "rust_name": f"lss_planted::{u}",
              "loop_id": None, "loop_is_body": None, "parent_lean_name": None, "is_recursive": False,
              "can_fail": True, "can_diverge": False, "is_opaque": False, "lean_file": "LssPlanted/Code/Funs.lean"}
             for u in PLANTED_UNITS]
    with open(os.path.join(tmp, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
        json.dump({"import": "LssPlanted", "declarations": decls}, f)
    return tmp


def run_planted(checker):
    print("=== full: generic statements, checked at one instantiation ===")
    import shutil
    import strategies
    d = planted_crate()
    try:
        def b(stmt, unit):
            return bounded.check_spec(checker, strategies.normalize_call(stmt, unit), unit, d)
        st = checker._aeneas_env_for(d)
        check("the planted crate builds", st["ok"], st["error"][:300])
        import gate
        for desc, stmt, unit in [
                ("a generic call on a constructor, in normal form",
                 "∀ {T : Type} (x : T) (tl : LssPlanted.List T), head (LssPlanted.List.Cons x tl) ⦃ r => r = x ⦄", "head"),
                ("a law on a trait argument", ORD_LAW + "max_of OrdInst a b ⦃ r => r = a ∨ r = b ⦄", "max_of"),
                ("a postcondition about a backward function's every input",
                 "∀ {T : Type} (l : LssPlanted.List T) (i : Std.U32), nth_back l i ⦃ r => ∀ t, ∃ tl, "
                 "r.2 t = LssPlanted.List.Cons t tl ⦄", "nth_back")]:
            vs = gate.check_candidate(checker, f"theorem t : {strategies.normalize_call(stmt, unit)} := sorry",
                                      unit, None, d, "rust-aeneas")
            check(f"the gate accepts {desc}", gate.is_well_formed(vs, "rust-aeneas"), str(vs)[:300])
        v = b("∀ {T : Type} (x : T) (tl : LssPlanted.List T), head (LssPlanted.List.Cons x tl) ⦃ r => r ≠ x ⦄", "head")
        check("a false generic spec is refuted at T := U32, through its normal form",
              v["status"] == "refuted" and v.get("instantiation") == "T := Aeneas.Std.U32", str(v))
        check("its refutation is kernel-checked", v.get("kernel") is True, str(v))
        derive = st.get("check_derive") or {}
        check("the crate's list gets a derived DecidableEq and its tree one decided by BEq",
              "LssPlanted.List" in derive.get("derived", []) and "LssPlanted.Node" in derive.get("via_beq", []),
              str(derive))
        v = b("∀ {T : Type} (x : T) (tl : LssPlanted.List T), head (LssPlanted.List.Cons x tl) ⦃ r => r = x ⦄", "head")
        check("the true generic spec passes, rejecting wrong outputs", v["status"] == "pass" and v["warning"] is None,
              str(v))
        pr = checker.try_aeneas(strategies.normalize_call(
            "∀ {T : Type} (x : T) (tl : LssPlanted.List T), head (LssPlanted.List.Cons x tl) ⦃ r => r = x ⦄", "head"),
            "head", d, candidate_id="planted_head")
        check("the normal form is proved: its defining hypothesis substituted back, the call unfolds",
              pr.proved, pr.error[:300])
        v = b("∀ {T : Type} (l : LssPlanted.List T), head l ⦃ _ => True ⦄", "head")
        check("a generic spec claiming success on every list is refuted by the empty one",
              v["status"] == "refuted" and v.get("outcome") == "fail", str(v))
        v = b(ORD_LAW + "max_of OrdInst a b ⦃ r => r = a ⦄", "max_of")
        check("a false spec over a trait is refuted at the crate's instance, once the kernel proved its law",
              v["status"] == "refuted"
              and v.get("instantiation") == "T := Aeneas.Std.I32, OrdInst := LssPlanted.I32.Insts.LssPlantedOrd", str(v))
        check("that refutation is kernel-checked, the law proved again inside it", v.get("kernel") is True, str(v))
        v = b(ORD_LAW + "max_of OrdInst a b ⦃ r => (r = a ∨ r = b) ⦄", "max_of")
        check("the true spec over the trait passes", v["status"] == "pass", str(v))
        v = b("∀ {T : Type} (OrdInst : LssPlanted.Ord T) (hcmp : ∀ a b, OrdInst.cmp a b = ok LssPlanted.Ordering.Less) "
              "(a b : T), max_of OrdInst a b ⦃ r => r = a ⦄", "max_of")
        check("an instance that does not meet the statement's law is never used: not evaluated",
              v["status"] == "not_evaluated" and "does not meet" in v.get("detail", ""), str(v))
        v = b("∀ {T : Type} (HashInst : LssPlanted.Hash T) (x : T), hash_of HashInst x ⦃ r => r.val < 7 ⦄", "hash_of")
        check("a trait the crate has no instance of: not evaluated, no instance made up",
              v["status"] == "not_evaluated" and "no instance of LssPlanted.Hash" in v.get("detail", ""), str(v))
        v = b("∀ {T : Type} (l : LssPlanted.List T) (i : Std.U32), nth_back l i ⦃ r => ∀ t, ∃ tl, r.2 t = LssPlanted.List.Cons t tl ⦄",
              "nth_back")
        check("a statement about a backward function's every input is not evaluated: it goes to the provers",
              v["status"] == "not_evaluated" and "Decidable" in v.get("detail", ""), str(v))
        v = b("∀ {T : Type} (v : T), singleton v ⦃ r => r = some (LssPlanted.Node.mk v none none) ⦄", "singleton")
        check("equality on a tree is decided: the true spec passes", v["status"] == "pass", str(v))
        v = b("∀ {T : Type} (v : T), singleton v ⦃ r => r = none ⦄", "singleton")
        check("and a false one is refuted", v["status"] == "refuted", str(v))
    finally:
        shutil.rmtree(d, ignore_errors=True)


run_static_values()
run_static_recursive()
run_static_commands()
run_static_check()
run_static_run()
run_static_synth()
if not static:
    run_full()
print()
print("all pass" if not fails else f"FAILED: {fails}")
sys.exit(1 if fails else 0)
