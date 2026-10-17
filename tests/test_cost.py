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


if static:
    run_static_routing()
else:
    import lean
    import lean_server
    rust_dir, benches = _feature_suite()
    if rust_dir and benches is not None:
        import lss_config
        checker = lean.LeanChecker(project_dir=lss_config.project_dir("aeneas"))
        run_full_routing(rust_dir, benches, checker)
    lean_server.shutdown_all()

print()
if fails:
    print(f"FAILED: {fails}")
    sys.exit(1)
print("all pass")
