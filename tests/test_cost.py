"""speed and cost: where each rust proof attempt runs, the time budgets, the
mutant sample, the prompt context and the cost report. --static needs no Lean;
the full run uses ~/lss_lean/aeneas and ~/rust_benchmarks (FeatureSuite)."""
import json
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


def _verdict_line(name, ok, stage="ok", axioms=()):
    return "LSS_PROOF " + json.dumps({"name": name, "ok": ok, "stage": stage, "detail": "",
                                      "axioms": list(axioms)}) + "\n"


class FakeServer:
    """records each text sent with its env, timeout and prelude; answers with
    `reply(code)`, by default an empty, error-free result."""

    def __init__(self, reply=None):
        self.sent = []
        self.reply = reply or (lambda code: "")

    def check(self, code, timeout=None, env=None, prelude=""):
        import lean_server
        self.sent.append({"code": code, "env": env, "timeout": timeout, "prelude": prelude})
        return lean_server.CheckResult(stdout="", stderr=self.reply(code), rc=0, via="repl", new_env=99)

    def stats(self):
        return {"restarts": 0}


class Patch:
    """set attributes for the length of a `with` block."""

    def __init__(self, *triples):
        self.triples = triples
        self.saved = []

    def __enter__(self):
        for obj, name, value in self.triples:
            self.saved.append((obj, name, getattr(obj, name)))
            setattr(obj, name, value)
        return self

    def __exit__(self, *_):
        for obj, name, value in reversed(self.saved):
            setattr(obj, name, value)


def _proof_cfg(**over):
    import lss_config
    base = lss_config.proof_cfg()
    return lambda: {**base, **over}


CRATE_CTX = "import Aeneas\nimport Crate.Code.Funs\nimport Crate.Code.Types\nopen Crate\n"


class _Graph:
    crate = "Crate"
    crate_text = "import Aeneas\n-- the crate\n"


def _routed_checker(fake):
    """a checker that keeps Crate's env (env 7), registered the way a real build does."""
    import lean
    import lean_server
    import callgraph
    checker = lean.LeanChecker(project_dir="/aeneas")
    with Patch((lean_server, "get_server", lambda *a, **k: fake), (callgraph, "for_project", lambda p: _Graph())):
        checker._aeneas_build_env("/crate")
    state = {"ok": True, "env": 7, "admitted": [], "active": {}, "restarts": 0}
    setattr(checker, "_aeneas_env_for", lambda project_dir: state)
    return checker, state


def run_static_routing():
    print("=== static: every rust attempt runs in the crate env ===")
    import lean
    import lean_server
    import lss_config
    import callgraph

    # the crate env imports Hammer (and sets its premise selector) only with rust_hammer
    for on in (True, False):
        fake = FakeServer()
        with Patch((lean_server, "get_server", lambda *a, **k: fake), (callgraph, "for_project", lambda p: _Graph()),
                   (lss_config, "proof_cfg", _proof_cfg(rust_hammer=on))):
            lean.LeanChecker()._aeneas_build_env("/crate")
        text = fake.sent[-1]["code"]
        has = text.startswith("import Aeneas\nimport Hammer\n") and "set_library_suggestions" in text
        check(f"crate env with rust_hammer={on}: Hammer imported and its selector set" if on else
              "crate env with rust_hammer=False: no Hammer", has == on, text[:80])

    fake = FakeServer(lambda code: _verdict_line("t", True))
    checker, state = _routed_checker(fake)
    with Patch((lean_server, "get_server", lambda *a, **k: fake)):
        lean.run_in_project(CRATE_CTX + "#check 1")
        sent = fake.sent[-1]
        check("a text that imports a crate runs in the crate env, without its import lines",
              sent["env"] == 7 and "import" not in sent["code"] and "#check 1" in sent["code"], str(sent)[:200])

        v, _ = lean.check_proof(CRATE_CTX, "theorem t : 1 = 1 := rfl", "t", project_dir="/crate", timeout=11)
        sent = fake.sent[-1]
        check("a proof check on a rust unit runs in the crate env, with no prelude and its own timeout",
              v["ok"] and sent["env"] == 7 and sent["prelude"] == "" and sent["timeout"] == 11
              and "lss_check_proof" in sent["code"] and "import" not in sent["code"], str(sent)[:200])

        lean.check_proof("import Mathlib\n", "theorem t : 1 = 1 := rfl", "t", project_dir="/native")
        sent = fake.sent[-1]
        check("a text with no crate import keeps its own imports and the proof-check prelude",
              sent["env"] is None and sent["code"].startswith("import Mathlib") and sent["prelude"] == lean.proof_check_text(),
              str(sent)[:200])

        lean.run_in_project("import Aeneas\nimport Other.Code.Funs\n#check 1")
        check("a crate no checker keeps is not routed", fake.sent[-1]["env"] is None, str(fake.sent[-1])[:200])

        state["ok"] = False
        lean.run_in_project(CRATE_CTX + "#check 1")
        check("a crate whose env is down is not routed", fake.sent[-1]["env"] is None, str(fake.sent[-1])[:200])
        state["ok"] = True

        # nothing is imported to check that a crate can load Mathlib or Hammer
        n = len(fake.sent)
        check("the crate dir needs no import precheck", checker._precheck_env("/crate") == (True, "") and
              len(fake.sent) == n, str(fake.sent[n:])[:200])
        with Patch((lss_config, "proof_cfg", _proof_cfg(rust_hammer=False))):
            ok, _ = checker._precheck_env("/crate", requires_hammer=True)
        check("the crate dir has no hammer when rust_hammer is off", ok is False)

        # cached results of a rust text are keyed by the crate text, so old entries never match
        cache = {}

        class _Cache:
            def get(self, k):
                return cache.get(k)

            def put(self, k, v):
                cache[k] = v
        checker._cache = _Cache()
        checker.typecheck(CRATE_CTX + "def g := 1")
        check("a rust typecheck is cached under the crate text's hash",
              len(cache) == 1 and next(iter(cache)).startswith("crate:"), str(list(cache))[:120])
        checker._cache = None

        # layer 1 on a rust unit: no Mathlib precheck, the batch runs in the crate env
        n = len(fake.sent)
        checker.try_proof(CRATE_CTX, "∀ (x : Std.U32), x = x", func_name="f", project_dir="/crate")
        sent = fake.sent[n:]
        check("layer 1 on a rust unit is one call, in the crate env",
              len(sent) == 1 and sent[0]["env"] == 7 and sent[0]["code"].count("lss_check_proof") >= 20, str(sent)[:200])

        # hammer on a rust unit: in the crate env, or skipped when rust_hammer is off
        fake.reply = lambda code: _verdict_line("_hammer_proof", True, "ok", ["propext"])
        n = len(fake.sent)
        with Patch((lss_config, "proof_cfg", _proof_cfg(rust_hammer=True))):
            pr = checker.try_hammer(CRATE_CTX, "∀ (a b : Nat), a + b = b + a")
        sent = fake.sent[n:]
        check("hammer on a rust unit runs in the crate env and proves through its verdict",
              pr.proved and len(sent) == 1 and sent[0]["env"] == 7 and "by hammer" in sent[0]["code"], str(sent)[:200])
        n = len(fake.sent)
        with Patch((lss_config, "proof_cfg", _proof_cfg(rust_hammer=False))):
            pr = checker.try_hammer(CRATE_CTX, "∀ (a b : Nat), a + b = b + a")
        check("hammer on a rust unit is skipped when rust_hammer is off",
              not pr.proved and len(fake.sent) == n and "skipped" in pr.method, str(pr))
    lean._CRATE_ENVS.clear()


class _UnitGraph:
    crate = "C"
    names = {"C.f"}

    def callees_outside_scc(self, unit):
        return []

    def recursive(self, unit):
        return False


def run_static_hammer_closer():
    print("=== static: hammer closes what step* leaves ===")
    import lean
    import lean_server
    import lss_config
    import callgraph

    def run(reply, **cfg):
        checker = lean.LeanChecker()
        state = {"ok": True, "env": 3, "admitted": [], "active": {}, "restarts": 0}
        setattr(checker, "_aeneas_env_for", lambda project_dir: state)
        fake = FakeServer(reply)
        with Patch((lean_server, "get_server", lambda *a, **k: fake), (callgraph, "for_project", lambda p: _UnitGraph()),
                   (lss_config, "proof_cfg", _proof_cfg(**cfg))):
            pr = checker.try_aeneas("stmt", "f", "/crate")
        return pr, fake.sent, state

    def h_wins(code):
        out = _verdict_line("_aeneas_a", False, "elab") + _verdict_line("_aeneas_b", False, "elab")
        if "name:_aeneas_h " in code:
            out = _verdict_line("_aeneas_h", True, "ok", ["propext"])
        if "name:lss_admitted_0 " in code:
            out = _verdict_line("lss_admitted_0", True)
        return out
    pr, sent, state = run(h_wins, rust_hammer=True, hammer_heartbeats=777)
    h = next((x for x in sent if "name:_aeneas_h " in x["code"]), None)
    check("when a and b fail, the closers plus hammer run as their own call",
          h is not None and lean.HAMMER in h["code"] and "grind | hammer" in h["code"] and h["env"] == 3, str(sent)[:300])
    check("the hammer closer gets hammer's heartbeats and time",
          h is not None and "heartbeats:777" in h["code"] and h["timeout"] == max(90, lss_config.server_cfg()["hammer_timeout"]),
          str(h)[:200])
    check("a proof the hammer closer finds is proved as aeneas:h and admitted with the same budget",
          pr.proved and pr.method == "aeneas:h" and len(state["admitted"]) == 1 and lean.HAMMER in state["admitted"][0][2]
          and any("name:lss_admitted_0 " in x["code"] and "heartbeats:777" in x["code"] for x in sent), str(pr)[:200])

    def a_wins(code):
        if "name:lss_admitted_0 " in code:
            return _verdict_line("lss_admitted_0", True)
        return _verdict_line("_aeneas_a", True)
    pr, sent, _ = run(a_wins, rust_hammer=True)
    check("when a or b closes the goal, hammer never runs",
          pr.method == "aeneas:a" and not any(lean.HAMMER in x["code"] for x in sent), str(sent)[:200])

    pr, sent, _ = run(lambda code: _verdict_line("_aeneas_a", False, "elab"), rust_hammer=False)
    check("with rust_hammer off there is no hammer closer",
          not pr.proved and not any(lean.HAMMER in x["code"] for x in sent), str(sent)[:200])


class Clock:
    def __init__(self):
        self.t = 0.0

    def __call__(self):
        return self.t


class _BudgetChecker:
    """layer 1 fails after 10 s (or its timeout), hammer uses its whole timeout and
    proves (when `hammer_proves`); every call's timeout is recorded."""

    def __init__(self, clock, hammer_proves=True):
        self.clock, self.hammer_proves = clock, hammer_proves
        self.l1, self.hammer = [], []

    def _precheck_env(self, project_dir, requires_hammer=False):
        return True, ""

    def typecheck(self, code, project_dir=None):
        return True, []

    def try_proof(self, lean_env, stmt, func_name=None, project_dir=None, timeout=None, **_):
        import lean
        self.l1.append(timeout)
        self.clock.t += min(10, timeout or 30)
        return lean.ProofResult(proved=False, method="", error="")

    def try_hammer(self, lean_env, stmt, func_name=None, project_dir=None, timeout=None):
        import lean
        import lss_config
        t = timeout or lss_config.server_cfg()["hammer_timeout"]
        self.hammer.append(t)
        self.clock.t += t
        return lean.ProofResult(proved=self.hammer_proves, method="l2:hammer (1.0s)" if self.hammer_proves else "", error="")


class _SketchLLM:
    def _ask(self, prompt):
        return "by\n" + "".join(f"  have h{i} : {i} = {i} := sorry\n" for i in range(4)) + "  simp_all"


def run_static_budgets():
    print("=== static: one time budget per split, one hammer budget per unit's mutants ===")
    import time
    import lean
    import lss_config
    import synth

    def split(seconds):
        clock = Clock()
        checker = _BudgetChecker(clock)
        sub = []

        def fake_check(context, theorems, name, project_dir=None, timeout=None, heartbeats=0):
            sub.append((name, timeout, clock.t))
            clock.t += 1
            return {"ok": name == "_decomp_final", "stage": "ok", "axioms": []}, ""
        with Patch((time, "monotonic", clock), (synth, "check_proof", fake_check),
                   (lss_config, "proof_cfg", _proof_cfg(split_seconds=seconds))):
            r = synth.decompose_and_prove("ctx", "stmt", checker, _SketchLLM(), project_dir="/p")
        return r, checker, sub

    r, checker, sub = split(100)
    final_t = next((t for n, _, t in sub if n == "_decomp_final"), None)
    check("every sub-lemma is tried, layer 1 then hammer", len(checker.l1) == 4 and len(checker.hammer) == 4,
          f"{checker.l1} {checker.hammer}")
    check("the sub-lemmas together stay within the candidate's budget",
          final_t is not None and final_t - 1 <= 100, f"sub-lemmas ended at {final_t}")
    check("each sub-lemma's hammer gets only its share of what is left",
          all(t <= 25 + 1e-9 for t in checker.hammer), str(checker.hammer))
    check("layer 1 keeps its normal cap inside a share", all(lean.MIN_TRY <= t <= 30 for t in checker.l1), str(checker.l1))
    check("the split still proves when every sub-lemma closes", r.proved and r.method == "l3:decompose", str(r))

    r, checker, _ = split(0)
    check("with no time left a sub-lemma still gets layer 1, and no hammer",
          checker.l1 == [lean.MIN_TRY] and checker.hammer == [] and not r.proved, f"{checker.l1} {checker.hammer}")

    clock = Clock()
    checker = _BudgetChecker(clock, hammer_proves=False)
    with Patch((time, "monotonic", clock), (lss_config, "proof_cfg", _proof_cfg(mutant_hammer_seconds=120))):
        engine = lean.MutationEngine(checker)
        for i in range(5):
            engine.certify_proof("def f := 1", {"code": "def f := 1\ndef f_mut := 2", "mutant_func_name": f"f_mut{i}"},
                                 "f", [], project_dir="/p")
    expected, left = [], 120.0
    while left >= lean.MIN_TRY and len(expected) < 5:
        expected.append(min(lss_config.server_cfg()["hammer_timeout"], left))
        left -= expected[-1]
    check("the unit's mutants share one hammer budget, then stop calling hammer",
          checker.hammer == expected and sum(checker.hammer) <= 120, f"{checker.hammer} vs {expected}")
    check("every mutant still gets its tactic proof attempt", len(checker.l1) == 5, str(checker.l1))


CLAMP = """def clampTo (lo hi x : Nat) : Nat :=
  if x < lo then lo
  else if x > hi then hi
  else x + 0"""


def run_static_mutants():
    print("=== static: at most one mutant per line, judged only by proof ===")
    import lean

    ms = ([{"operator": "arith_+_-", "line": 1, "k": i} for i in range(5)] +
          [{"operator": "arith_-_+", "line": 2}, {"operator": "boundary_<_≤", "line": 2}, {"operator": "+", "line": 3}])
    got, stats = lean._sample_per_line(ms, 30)
    check("one mutant per line", [m["line"] for m in got] == [1, 2, 3], str(got))
    check("on each line the least-used operator class wins", got[1]["operator"] == "boundary_<_≤", str(got[1]))
    check("the sampling stats count lines and mutants", stats == {"generated": 8, "lines": 3, "sampled": 3, "capped": False},
          str(stats))
    got, stats = lean._sample_per_line([{"operator": "x", "line": i} for i in range(50)], 30)
    check("more lines than the cap are sampled evenly, first to last",
          len(got) == 30 and got[0]["line"] == 0 and got[-1]["line"] >= 45 and stats["capped"], str([m["line"] for m in got]))

    class _Typechecks:
        def typecheck(self, code, project_dir=None):
            return True, []
    engine = lean.MutationEngine(_Typechecks())
    muts = engine.generate_mutants(CLAMP, "clampTo")
    lines = [m["line"] for m in muts]
    check("generated mutants sit on distinct lines of the definition",
          bool(muts) and len(set(lines)) == len(lines) and all(0 <= x <= 3 for x in lines), str(lines))
    check("no line goes unmutated when it has a mutant", set(lines) == {1, 2, 3}, str(lines))

    check("the LLM equivalence judge is gone", not hasattr(lean.MutationEngine, "detect_equivalent_llm"))
    try:
        engine.filter_compilable([], llm=object())  # type: ignore[call-arg]
        takes_llm = True
    except TypeError:
        takes_llm = False
    check("filter_compilable takes no LLM", not takes_llm)


CRATE_TEXT = """import Aeneas
namespace C

structure m.Inner where
  v : Std.U32

structure m.Pair where
  first : m.Inner
  second : Std.U32

inductive m.Other where
  | A
  | B

def m.leaf (x : Std.U32) : Result Std.U32 := ok x

def m.callee (p : m.Pair) : Result Std.U32 := m.leaf p.second

def m.even (n : Std.U32) : Result Bool := m.odd n

def m.odd (n : Std.U32) : Result Bool := m.even n

def m.top (p : m.Pair) : Result Std.U32 := do
  let a ← m.callee p
  m.even a

def m.unrelated (o : m.Other) : Result Bool := ok true

end C
"""


class _CtxGraph:
    crate = "C"
    crate_text = CRATE_TEXT
    names = {"C.m.leaf", "C.m.callee", "C.m.even", "C.m.odd", "C.m.top", "C.m.unrelated"}
    _sccs = [frozenset({"C.m.even", "C.m.odd"}), frozenset({"C.m.top"}), frozenset({"C.m.callee"}),
             frozenset({"C.m.leaf"}), frozenset({"C.m.unrelated"})]
    _callees = {"C.m.top": ["C.m.callee", "C.m.even"], "C.m.even": ["C.m.odd"], "C.m.odd": ["C.m.even"],
                "C.m.callee": ["C.m.leaf"]}

    @property
    def sccs(self):
        return self._sccs

    def scc_of(self, name):
        return next((i for i, c in enumerate(self._sccs) if name in c), None)

    def callees_outside_scc(self, name):
        i = self.scc_of(name)
        return sorted(c for c in self._callees.get(name, []) if self.scc_of(c) != i)

    def def_text(self, name):
        short = name[len("C."):]
        start = CRATE_TEXT.find(f"def {short} ")
        end = CRATE_TEXT.find("\n\n", start)
        return CRATE_TEXT[start:end] if start >= 0 else None


def run_static_context():
    print("=== static: prompts get the unit, its types and its callees' specs ===")
    import lean
    import callgraph
    import synth

    checker = lean.LeanChecker()
    with Patch((callgraph, "for_project", lambda p: _CtxGraph())):
        text = checker.unit_context("/crate", "m.top")
        check("the context holds the unit's own definition", "def m.top (p : m.Pair)" in text, text)
        check("a callee with no proved spec appears as its definition", "def m.callee (p : m.Pair)" in text, text)
        check("a callee in a recursion group comes alone, without the rest of its group",
              "def m.even " in text and "def m.odd " not in text, text)
        check("the types the definitions name come along, and the types those name",
              "structure m.Pair where" in text and "structure m.Inner where" in text, text)
        check("nothing the unit does not reach is included",
              "m.unrelated" not in text and "inductive m.Other" not in text and "def m.leaf" not in text, text)
        check("the context is a fraction of the whole crate", len(text) < len(CRATE_TEXT), f"{len(text)} vs {len(CRATE_TEXT)}")
        checker._aeneas_env["/crate"] = {"admitted": [("lss_admitted_0", "∀ p, m.callee p ⦃ r => r = p.second ⦄", "step*",
                                                       "C.m.callee")]}
        text = checker.unit_context("/crate", "m.top")
        check("a callee with a proved spec appears as that spec instead of its body",
              "proved specs of C.m.callee" in text and "m.callee p ⦃ r => r = p.second ⦄" in text
              and "def m.callee" not in text, text)
        text = checker.unit_context("/crate", "m.even")
        check("a recursive unit gets the rest of its recursion group", "def m.odd " in text and "def m.even " in text, text)

    llm = object.__new__(synth.LLMClient)
    sent = []
    setattr(llm, "_ask", lambda prompt: sent.append(prompt) or "```lean\ntheorem t : ∀ x, f x ⦃ r => r = x ⦄ := sorry\n```")
    setattr(llm, "_retrieve_mathlib_examples", lambda *a: [])
    setattr(llm, "_retrieve_similar_proved_specs", lambda *a: [])
    llm.generate_specs("import Aeneas\nimport C.Code.Funs\n", [], func_name="f", func_source="def f (x : Std.U32) : Result Std.U32 := ok x")
    check("the spec prompt shows the unit's context, not just the import lines",
          bool(sent) and "def f (x : Std.U32)" in sent[0], (sent or [""])[0][:200])


def run_static_report():
    print("=== static: the cost report ===")
    import contextlib
    import io
    import tempfile
    import events
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
    import cost_report

    # an enclosing layer wins: a sub-lemma's attempts count toward the split
    fh = io.StringIO()
    saved, saved_stats = dict(events._state), dict(events._stats)
    events._state.clear()
    events._state.update({"run_id": "t", "config_hash": "h", "fh": fh})
    events._stats.update({"lean_calls": 0, "lean_s": 0.0})

    @events.layer("tactics")
    def inner():
        events.emit("lean", elapsed=1.0)

    @events.layer("decompose")
    def outer():
        inner()
    outer()
    inner()
    rows = [json.loads(x) for x in fh.getvalue().splitlines()]
    events._state.clear()
    events._state.update(saved)
    events._stats.clear()
    events._stats.update(saved_stats)
    check("Lean time inside a layer counts toward the outermost one",
          [r.get("layer") for r in rows] == ["decompose", "tactics"], str(rows))

    rows = ([{"kind": "llm", "func": "f1", "input_tokens": n, "output_tokens": 10, "usd": 0.01} for n in (1000, 3000)] +
            [{"kind": "prompt_context", "func": "f1", "chars": 900, "chars_whole": 40000}] +
            [{"kind": "lean", "layer": lay, "elapsed": sec, "func": "f1"} for lay, sec in
             [("aeneas", 3.0), ("decompose", 10.0), ("mutation", 5.0), ("tactics", 1.0), ("hammer", 2.0),
              ("bounded", 1.5), ("gate", 0.5)]] +
            [{"kind": "verdict", "func": "f1", "status": "proved", "method": m, "source": src} for m, src in
             [("aeneas:h", "rust-aeneas"), ("l2:hammer (12.0s)", "rust-aeneas"), ("l2:hammer (3.0s)", "lean-native"),
              ("l3:decompose", "rust-aeneas"), ("aeneas:a", "rust-aeneas")]])
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False, encoding="utf-8") as f:
        f.write("\n".join(json.dumps(r) for r in rows) + "\n")
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        cost_report.report(f.name)
    os.unlink(f.name)
    text = out.getvalue()
    lines = {ln.split()[0]: ln for ln in text.splitlines() if ln.startswith("  ") and ln.split()}
    check("every layer gets its Lean seconds, the split and the bounded check included",
          all(k in lines for k in ("aeneas", "decompose", "mutation", "tactics", "hammer", "bounded", "gate"))
          and "s=10.0" in lines.get("decompose", ""), text)
    check("proofs are credited to the aeneas layer and the split",
          "proofs=2" in lines.get("aeneas", "") and "proofs=1" in lines.get("decompose", ""), text)
    check("hammer closes are counted per track, on the whole goal and after step*",
          "whole goal=1 after step*=1" in lines.get("rust-aeneas", "") and
          "whole goal=1 after step*=0" in lines.get("lean-native", ""), text)
    check("each function shows its prompt tokens and its context size against the whole crate",
          "in_tokens=4000 (2000/call)" in lines.get("f1", "") and "context=900 chars (whole crate 40000)" in lines.get("f1", ""),
          text)


def _feature_suite():
    rust_dir = os.path.expanduser("~/rust_benchmarks")
    if not os.path.isdir(os.path.join(rust_dir, "FeatureSuite", "Code")):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, "not a directory")
        return None, None
    import loader
    benches = {b["func_name"]: b for b in loader.load_rust_project(rust_dir)}
    return rust_dir, benches


def run_full_routing(rust_dir, benches, checker):
    print("=== full: routing on FeatureSuite ===")
    import lean_server
    import lss_config

    bm = benches["identity"]
    ctx = bm["lean_code"] + bm["lean_preamble"]
    state = checker._aeneas_env_for(rust_dir)
    check("crate env built", state["ok"], state.get("error", "")[:300])
    if not state["ok"]:
        return
    ok, errs = checker.typecheck(ctx + "\ndef identity_mut0 (value : Std.U32) : Result Std.U32 := ok value",
                                 project_dir=rust_dir)
    check("a mutant of a crate function typechecks in the crate env", ok, str(errs)[:300])
    ok, _ = checker.typecheck(ctx + "\ndef identity_bad (value : Std.U32) : Result Std.U32 := ok true",
                              project_dir=rust_dir)
    check("an ill-typed mutant is still rejected", not ok)
    pr = checker.try_proof(ctx, "∀ (value : Std.U32), identity value = ok value", func_name="identity",
                           project_dir=rust_dir)
    check("layer 1 proves a statement about a crate function, in the crate env", pr.proved, pr.error[:300])
    pr = checker.try_hammer(ctx, "∀ (a b : Nat), a + b = b + a", project_dir=rust_dir)
    check("hammer is off on rust units by default and runs nothing", not pr.proved and "skipped" in pr.method, str(pr))
    started = [os.path.abspath(p) for p in lean_server.all_stats()]
    check("no Lean server was started in the rust project itself",
          os.path.abspath(rust_dir) not in started and os.path.abspath(lss_config.project_dir("aeneas")) in started,
          str(started))


SWAP_HOARE = "forall (p : records.Pair), records.swap p ⦃ r => r.first = p.second ∧ r.second = p.first ⦄"


def run_full_hammer_closer(rust_dir, checker):
    print("=== full: the hammer closer on FeatureSuite ===")
    state = checker._aeneas_env_for(rust_dir)
    before = len(state["admitted"])
    pr = checker.try_aeneas("∀ (value : Std.U32), identity value ⦃ r => r.val = value.val + 1 ⦄", "identity", rust_dir)
    check("a false spec goes through a and b (and the hammer closer when it is on) and is not proved",
          not pr.proved, str(pr)[:300])
    check("nothing is admitted for it", len(checker._aeneas_env_for(rust_dir)["admitted"]) == before)
    pr = checker.try_aeneas(SWAP_HOARE, "records.swap", rust_dir)
    check("the crate env still proves afterwards", pr.proved and pr.method == "aeneas:a", str(pr)[:300])


def run_full_context(rust_dir, benches, checker):
    print("=== full: the prompt context on FeatureSuite ===")
    bm = benches["records.order_pair"]
    text = checker.unit_context(rust_dir, bm["lean_name"])
    whole = len(bm["func_source"])
    check("order_pair's context holds its definition and the Pair type",
          "def records.order_pair" in text and "structure records.Pair" in text, text[:400])
    check("swap, proved earlier in this run, appears as its spec and not its body",
          "records.swap p ⦃" in text and "def records.swap" not in text, text[:600])
    check("the context leaves out functions order_pair never calls", "count_occurrences" not in text, text[:400])
    check("the context is under a fifth of Types.lean + Funs.lean", len(text) * 5 < whole, f"{len(text)} vs {whole}")


if static:
    run_static_routing()
    run_static_hammer_closer()
    run_static_budgets()
    run_static_mutants()
    run_static_context()
    run_static_report()
else:
    import lean
    import lean_server
    rust_dir, benches = _feature_suite()
    if rust_dir and benches is not None:
        import lss_config
        checker = lean.LeanChecker(project_dir=lss_config.project_dir("aeneas"))
        run_full_routing(rust_dir, benches, checker)
        run_full_hammer_closer(rust_dir, checker)
        run_full_context(rust_dir, benches, checker)
    lean_server.shutdown_all()

print()
if fails:
    print(f"FAILED: {fails}")
    sys.exit(1)
print("all pass")
