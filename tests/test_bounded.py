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


def run_static_commands():
    print("=== static: lean command text ===")
    stmt = '∀ (x : Std.U32), f x ⦃ r => r.val = x.val + 1 ⦄'
    cmd = bounded.eval_command("t1", stmt, [U32], U32, [[0], [5]])
    check("eval command names the tag and quotes the statement",
          cmd.startswith('lss_eval_spec t1 stmt:"∀ (x : Std.U32), f x ⦃'), cmd[:80])
    check("eval command has one row per input", cmd.endswith('rows:[["0#u32"], ["5#u32"]]'), cmd[-60:])
    check("the encoder's quotes are escaped", 'enc:"fun v => (\\"\\\\\\"\\" ++ toString' in cmd, cmd[90:200])
    post = bounded.post_command("t2", stmt, [U32], U32, [5], [6, 7])
    check("post command carries the row and the wrong outputs", post.endswith('row:["5#u32"] outs:["6#u32", "7#u32"]'),
          post[-60:])
    text = ('x.lean:1:0: warning: LSS_EVAL {"tag":"a","ok":true,"kind":"spec","rows":[]}\n'
            'LSS_EVAL {broken\nLSS_EVAL {"tag":"b","ok":false,"detail":"no"}')
    got = bounded.parse_evals(text)
    check("parse_evals reads every message and skips broken lines", set(got) == {"a", "b"}, str(got))
    ref = bounded.refutation_text("rf", "S", "C.f", ["a1", "a0", "h"], [U32, ("bool",)], U32,
                                  [5, True], "violates", '"6"')
    check("refutation applies the statement in binder order, hypotheses by decide",
          "(h (true) (5#u32) (by first | decide | simp_all | omega))" in ref, ref)
    check("refutation computes the call in parameter order", "have hv : C.f (5#u32) (true) = Aeneas.Std.Result.ok (6#u32)" in ref, ref)
    check("refutation of a violated postcondition decides it", ref.endswith("first | decide | simp | omega"))
    ref = bounded.refutation_text("rf", "S", "C.f", ["a0"], [U32], U32, [0], "fail", "Aeneas.Std.Error.integerOverflow")
    check("refutation of a failing call needs only the constructor clash",
          ref.endswith("cases hy") and "Result.fail Aeneas.Std.Error.integerOverflow" in ref, ref)


class FakeLean:
    """bounded._Lean with scripted answers: `row_outcome(row)` gives one row's
    result, `post_outcome(row, out)` one perturbed output's."""
    calls = []

    def __init__(self, row_outcome, post_outcome=None, kernel=True, timeout=False):
        self.row_outcome, self.post_outcome, self.kernel, self.timeout = row_outcome, post_outcome, kernel, timeout
        self.n = 0
        self.sent = []

    def __call__(self, checker, project_dir):
        return self

    def eval(self, stmt, args, ret, rows):
        if self.timeout:
            return None, "timeout"
        return {"kind": "dspec" if "div" in stmt else "spec", "binders": ["a0"],
                "rows": [self.row_outcome(r) for r in rows]}, ""

    def post(self, stmt, args, ret, row, outs):
        return [self.post_outcome(row, o) for o in outs] if self.post_outcome else None

    def run(self, text):
        self.sent.append(text)
        name = text.split(" name:")[1].split()[0]
        return f'LSS_PROOF {{"name":"{name}","ok":{"true" if self.kernel else "false"},"stage":"ok","detail":"","axioms":[]}}', ""


def _check(fake, stmt="S", sig=("C.f", [U32], U32)):
    old_lean, old_sig = bounded._Lean, bounded.signature
    bounded._Lean = fake  # type: ignore[assignment]
    bounded.signature = lambda project_dir, unit: sig  # type: ignore[assignment]
    try:
        return bounded.check_spec(None, stmt, "f", "/p")
    finally:
        bounded._Lean, bounded.signature = old_lean, old_sig


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
    check("the feedback names the input and the observed output", "(5#u32)" in v.get("feedback", ""), v.get("feedback"))
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
    v = _check(FakeLean(lambda r: {"outcome": "error", "detail": "not Decidable: x"}))
    check("a spec none of whose rows evaluates is skipped, with the error",
          v == {"status": "skipped", "detail": "not Decidable: x"}, str(v))
    v = _check(FakeLean(same, timeout=True))
    check("a diverging evaluation is a timeout, not a refutation", v["status"] == "timeout", str(v))

    def unsupported(project_dir, unit):
        raise tc.Unsupported("generic")
    old = bounded.signature
    bounded.signature = unsupported  # type: ignore[assignment]
    try:
        v = bounded.check_spec(None, "S", "f", "/p")
    finally:
        bounded.signature = old
    check("a unit whose types are not covered is skipped", v == {"status": "skipped", "detail": "generic"}, str(v))


def run_static_run():
    print("=== static: what each command is sent with ===")

    class Server:
        sent = []

        def check(self, code, timeout=None, env=None):
            self.sent.append((code, env))

            class R:
                timed_out = False
                stdout, stderr = "", ""
            return R()

    class Checker:
        lean_calls = 0

        def _aeneas_env_for(self, project_dir):
            return {"ok": True, "env": 42}

    server = Server()
    old = bounded._lean_server.get_server
    bounded._lean_server.get_server = lambda *a, **k: server  # type: ignore[assignment]
    try:
        bounded._Lean(Checker(), "/p").run("lss_eval_spec x")
    finally:
        bounded._lean_server.get_server = old
    code, env = server.sent[0]
    check("each command runs against the crate env", env == 42, str(env))
    check("each command carries the gate's Decidable instances first",
          "lssSubtypeDecEq" in code and "deriving instance DecidableEq for Aeneas.Std.Result" in code
          and code.endswith("lss_eval_spec x"), code[-200:])


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
    synth._gate.check_candidate = lambda *a, **k: [{"check": c, "ok": True, "detail": ""} for c in gate.CHECK_ORDER]
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

    # a diverging evaluation: the server times out, restarts, and the next check works
    state = checker._aeneas_env_for(rust_dir)
    server = lean_server.get_server(lss_config.project_dir("aeneas"))
    r = server.check("partial def lss_spin (x : Std.U32) : Result Std.U32 := lss_spin x", env=state["env"], timeout=60)
    check("diverging helper added", r.rc == 0 and r.new_env is not None, (r.stderr or "")[:200])
    if r.new_env is not None:
        state["env"] = r.new_env
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


run_static_values()
run_static_commands()
run_static_check()
run_static_run()
run_static_synth()
if not static:
    run_full()
print()
print("all pass" if not fails else f"FAILED: {fails}")
sys.exit(1 if fails else 0)
