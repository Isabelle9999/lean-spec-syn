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


class _StubChecker:
    """records which proof layer ran, proves instantly, no lean process."""

    def __init__(self):
        self.calls = []

    def typecheck(self, code, project_dir=None):
        return True, []

    def try_aeneas(self, stmt, func, project_dir, candidate_id=None):
        self.calls.append("aeneas")
        import lean
        return lean.ProofResult(proved=True, method="aeneas:a", error="")

    def try_proof(self, lean_env, stmt, func_name=None, project_dir=None):
        self.calls.append("proof")
        import lean
        return lean.ProofResult(proved=True, method="l1:rfl", error="")

    def try_hammer(self, lean_env, stmt, func_name=None, project_dir=None):
        self.calls.append("hammer")
        import lean
        return lean.ProofResult(proved=False, method="", error="")


def _spec(func):
    # mentions func twice so validate()'s vacuity check (gate 3) skips as relational
    return {"name": "t1", "stmt": f"forall n, {func} n = {func} n", "status": "pending", "method": ""}


def run_static():
    print("=== static ===")
    import synth
    import lss_config
    import gate

    # the well-formedness gate needs a real Lean server, and only the order of
    # the proof layers is under test here, so every candidate passes the gate
    gate.check_candidate = lambda *a, **k: [
        {"gate": "wf", "check": c, "ok": True, "detail": ""} for c in gate.CHECK_ORDER]

    check("aeneas_layer defaults to true in lss.toml",
          lss_config.proof_cfg()["aeneas_layer"] is True)
    check("aeneas_heartbeats has a default",
          lss_config.proof_cfg()["aeneas_heartbeats"] > 0)

    import lean
    check("premise_selector defaults to local in lss.toml",
          lss_config.proof_cfg()["premise_selector"] == "local")
    hammer_code14, _ = lean._hammer_code('', '∀ (n : Nat), n + 0 = n')
    check("hammer_code emits the local selector line when premise_selector is local",
          "sineQuaNonSelector" in hammer_code14, hammer_code14[:200])

    orig = lss_config.proof_cfg

    # toggle off: aeneas never called, falls to try_proof
    lss_config.proof_cfg = lambda: {"aeneas_layer": False, "aeneas_heartbeats": 200000}
    checker = _StubChecker()
    synth.validate([_spec("f")], "def f (n : Nat) : Nat := n", [], checker,
                   func_name="f", project_dir="/tmp", source="rust-aeneas")
    check("toggle off: aeneas skipped", checker.calls == ["proof"], str(checker.calls))

    # toggle on, not a rust unit: aeneas never called
    lss_config.proof_cfg = orig
    checker = _StubChecker()
    synth.validate([_spec("f")], "def f (n : Nat) : Nat := n", [], checker,
                   func_name="f", project_dir="/tmp", source=None)
    check("non-rust unit: aeneas skipped", checker.calls == ["proof"], str(checker.calls))

    # toggle on, rust unit: aeneas called first, short-circuits the rest
    checker = _StubChecker()
    synth.validate([_spec("f")], "def f (n : Nat) : Nat := n", [], checker,
                   func_name="f", project_dir="/tmp", source="rust-aeneas")
    check("rust unit: aeneas runs before try_proof", checker.calls == ["aeneas"], str(checker.calls))

    lss_config.proof_cfg = orig


# the fixture is a slice of a real aeneas-translated crate (records.swap /
# records.order_pair from FeatureSuite): a synthetic def mimicking aeneas's own
# output (dotted names, namespace, do-notation call chains) did not reproduce the
# @[step] pickup reliably — see the project notes for why this test uses the real
# crate instead.
SWAP_EQ = "forall (p : records.Pair), records.swap p = ok { first := p.second, second := p.first }"
SWAP_EX = "forall (p : records.Pair), exists r, records.swap p = ok r ∧ r.first = p.second ∧ r.second = p.first"
SWAP_EX_TRUE = "forall (p : records.Pair), exists r, records.swap p = ok r"
SWAP_FORALL = ("forall (p r : records.Pair), records.swap p = ok r -> "
               "r.first = p.second ∧ r.second = p.first")
SWAP_HALF1 = "forall (p : records.Pair), exists r, records.swap p = ok r ∧ r.first = p.second"
SWAP_HALF2 = "forall (p : records.Pair), exists r, records.swap p = ok r ∧ r.second = p.first"
SWAP_DIFF_BINDER = ("forall (p : records.Pair) (h : p.first = p.first), "
                     "exists r, records.swap p = ok r ∧ r.first = p.second ∧ r.second = p.first")
ORDER_PAIR_GOAL = "forall (p : records.Pair), exists r, records.order_pair p = ok r ∧ r.first ≤ r.second"


def _parse_steps(text):
    import json
    import re
    out = []
    for m in re.finditer(r"LSS_STEP (\{[^\n]*\})", text or ""):
        try:
            out.append(json.loads(m.group(1)))
        except json.JSONDecodeError:
            continue
    return out


def run_full():
    print("=== full ===")
    import lean
    import lean_server
    import lss_config
    import callgraph

    proj = lss_config.project_dir("aeneas")
    if not os.path.isdir(proj):
        check("~/lss_lean/aeneas exists", False, f"not a directory: {proj}")
        return
    rust_dir = os.path.expanduser("~/rust_benchmarks")
    code_dir = os.path.join(rust_dir, "FeatureSuite", "Code")
    if not os.path.isdir(code_dir):
        check("~/rust_benchmarks/FeatureSuite/Code exists", False, f"not a directory: {code_dir}")
        return
    server = lean_server.get_server(proj, lss_config.server_cfg())
    check("server started", server._worker is not None)

    g = callgraph.for_project(rust_dir)
    layer = lean._aeneas_layer_text()
    base = g.crate_text + f"\nopen {g.crate}\n" + lean.proof_check_text() + "\n" + layer + "\n"

    def run(label, extra, timeout=90):
        r = server.check(base + extra, timeout=timeout)
        return r

    for label, stmt in (("equation", SWAP_EQ), ("exists", SWAP_EX), ("exists-true", SWAP_EX_TRUE),
                        ("forall-arrow", SWAP_FORALL)):
        r = run(label, f"theorem t_{label.replace('-', '_')} : {stmt} := by\n"
                       "  lss_spec_form\n  unfold records.swap\n  step*\n")
        check(f"{label} shape proved through lss_spec_form", r.rc == 0, (r.stderr or "")[:300])

    r = run("caller without registration", f"""
theorem caller_unregistered : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("caller unproved without callee's spec registered",
          r.rc != 0 and "unsolved goals" in (r.stderr or ""), (r.stderr or "")[:300])

    r = run("caller with registration", f"""
theorem swap_spec : {SWAP_EX} := by
  lss_spec_form
  unfold records.swap
  step*

lss_register_step swap_spec

theorem caller_registered : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("caller proved once callee's spec is registered, callee not unfolded", r.rc == 0, (r.stderr or "")[:300])

    # the AND combinator (point 1) fixes the former known gap: step tries @[step]
    # lemmas for the same call newest-first and uses the first that applies
    # (Aeneas Tactic/Step/Step.lean:1123-1134), so registering a weak spec after a
    # strong one used to starve a caller that needed the strong one. now the two
    # combine into one lemma (strong ∧ weak), so the caller still proves.
    r = run("multiple specs, strong then weak", f"""
theorem swap_strong_t3 : {SWAP_EX} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_strong_t3

theorem swap_weak_t3 : {SWAP_EX_TRUE} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_weak_t3

theorem order_pair_strong_then_weak : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("strong then weak: combined, caller still proves", r.rc == 0, (r.stderr or "")[:300])
    steps = _parse_steps(r.stderr)
    check("strong then weak: LSS_STEP reports combined",
          any(s.get("action") == "combined" for s in steps), str(steps))

    # swap's two halves admitted separately: neither half alone determines both
    # fields of r, so order_pair only proves once the AND lemma combines them.
    r = run("swap halves: first half alone is not enough", f"""
theorem swap_half1_a : {SWAP_HALF1} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_half1_a

theorem order_pair_half1_only : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("swap halves: half1 alone is not enough",
          r.rc != 0 and "unsolved goals" in (r.stderr or ""), (r.stderr or "")[:300])

    r = run("swap halves: both halves combine", f"""
theorem swap_half1_b : {SWAP_HALF1} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_half1_b

theorem swap_half2_b : {SWAP_HALF2} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_half2_b

theorem order_pair_both_halves : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("swap halves: combined via AND, caller proves", r.rc == 0, (r.stderr or "")[:300])
    steps = _parse_steps(r.stderr)
    check("swap halves: LSS_STEP reports combined",
          any(s.get("action") == "combined" for s in steps), str(steps))

    # different binders, both orders: the spec with fewer binders stays the active
    # @[step] lemma either way (ties keep the old one), and LSS_STEP says so.
    r = run("different binders: fewer first, then more", f"""
theorem swap_fewer_a : {SWAP_EX} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_fewer_a

theorem swap_more_a : {SWAP_DIFF_BINDER} := by
  intro p h
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_more_a

theorem order_pair_fewer_then_more : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("different binders (fewer, more): caller still proves", r.rc == 0, (r.stderr or "")[:300])
    steps = _parse_steps(r.stderr)
    check("different binders (fewer, more): LSS_STEP keeps the fewer-binder lemma active",
          any(s.get("action") == "kept_old" and s.get("active") == "swap_fewer_a.step" for s in steps),
          str(steps))

    r = run("different binders: more first, then fewer", f"""
theorem swap_more_b : {SWAP_DIFF_BINDER} := by
  intro p h
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_more_b

theorem swap_fewer_b : {SWAP_EX} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_fewer_b

theorem order_pair_more_then_fewer : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("different binders (more, fewer): caller still proves", r.rc == 0, (r.stderr or "")[:300])
    steps = _parse_steps(r.stderr)
    check("different binders (more, fewer): LSS_STEP activates the fewer-binder lemma",
          any(s.get("action") == "kept_new" and s.get("active") == "swap_fewer_b.step" for s in steps),
          str(steps))

    r = run("multiple specs, weak then strong", f"""
theorem swap_weak_t3b : {SWAP_EX_TRUE} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_weak_t3b

theorem swap_strong_t3b : {SWAP_EX} := by
  lss_spec_form
  unfold records.swap
  step*
lss_register_step swap_strong_t3b

theorem order_pair_weak_then_strong : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
""")
    check("registration order weak-then-strong: caller proves (strong registered last)",
          r.rc == 0, (r.stderr or "")[:300])

    restarts_before = server._worker.restarts
    trips = (f"theorem trips : {ORDER_PAIR_GOAL} := by\n  lss_spec_form\n"
             "  unfold records.order_pair\n  grind")
    after = "theorem after_trip : forall (p : records.Pair), p = p := by\n  intro p\n  rfl"
    r = run("heartbeat trip", lean.proof_check_call(trips, "trips", 1) + "\n" +
            lean.proof_check_call(after, "after_trip", 0) + "\n")
    verdicts = lean.parse_proof_verdicts(r.stderr)
    check("heartbeat trip: trips ok=false", verdicts.get("trips", {}).get("ok") is False,
          str(verdicts.get("trips")))
    check("heartbeat trip: after_trip still proves, ok=true", verdicts.get("after_trip", {}).get("ok") is True,
          str(verdicts.get("after_trip")))
    check("heartbeat trip: server did not restart", server._worker.restarts == restarts_before,
          f"before={restarts_before} after={server._worker.restarts}")

    r = run("open goals logged", f"""
theorem open_goal_demo : {ORDER_PAIR_GOAL} := by
  lss_spec_form
  unfold records.order_pair
  step*
  lss_log_goals
  all_goals sorry
""")
    check("open goal logged with a head symbol", "LSS_GOALS " in (r.stderr or "") and '"head"' in (r.stderr or ""),
          (r.stderr or "")[:300])

    # three-deep call chain through the growing env: chainB (middle) needs swap's
    # (leaf) @[step] lemma to get its own spec admitted; chainC (top) is then proved
    # against that admitted env without ever unfolding chainB or records.swap.
    r0 = server.check(base, timeout=90)
    check("depth3: base env built", r0.rc == 0 and r0.new_env is not None, f"rc={r0.rc}")
    env = r0.new_env

    r1 = server.check(f"theorem leaf_spec : {SWAP_EX} := by\n"
                      "  lss_spec_form\n  unfold records.swap\n  step*\n"
                      "lss_register_step leaf_spec", env=env, timeout=90)
    check("depth3: leaf admitted", r1.rc == 0 and r1.new_env is not None, (r1.stderr or "")[:300])
    env = r1.new_env or env

    # mid_spec and top_proved are stated in the same ∃-shape real candidates use
    # (never the bare ⦃⦄ notation — see synth.py:230-244), so lss_register_step
    # converts them like any admitted spec, rather than skipping an already-spec-
    # shaped theorem it was not designed to handle.
    r2 = server.check("""
def chainB (p : records.Pair) : Result records.Pair := do
  let r <- records.swap p
  records.swap r

theorem mid_spec : forall (p : records.Pair),
    exists r, chainB p = ok r ∧ r.first = p.first ∧ r.second = p.second := by
  lss_spec_form
  unfold chainB
  step* <;> simp_all

lss_register_step mid_spec
""", env=env, timeout=90)
    check("depth3: middle admitted using leaf's step (not re-derived)",
          r2.rc == 0 and "LSS_SKIP_STEP mid_spec" not in (r2.stderr or ""), (r2.stderr or "")[:300])
    env = r2.new_env or env

    r3 = server.check("""
def chainC (p : records.Pair) : Result records.Pair := do
  let r <- chainB p
  records.swap r

theorem top_proved : forall (p : records.Pair),
    exists r, chainC p = ok r ∧ r.first = p.second ∧ r.second = p.first := by
  lss_spec_form
  unfold chainC
  step* <;> simp_all
""", env=env, timeout=90)
    check("depth3: top proved via the growing env, chainB never unfolded", r3.rc == 0, (r3.stderr or "")[:300])

    r = run("no top-level open leak", "example : MetaM Unit := pure ()\n")
    check("unqualified MetaM does not resolve after the layer text", r.rc != 0 and "MetaM" in (r.stderr or ""),
          (r.stderr or "")[:300])

    # the two-halves chain survives a real server restart: both halves are admitted
    # through the real try_aeneas path (so the python-side admitted list carries two
    # entries), then a restart forces _aeneas_env_for to rebuild the crate env and
    # replay both admits in order, which recombines them identically.
    checker = lean.LeanChecker()
    prh1 = checker.try_aeneas(SWAP_HALF1, "records.swap", rust_dir, candidate_id="restart_half1")
    check("halves restart: half1 proved and admitted", prh1.proved, prh1.error[:300])
    prh2 = checker.try_aeneas(SWAP_HALF2, "records.swap", rust_dir, candidate_id="restart_half2")
    check("halves restart: half2 proved and combined", prh2.proved, prh2.error[:300])
    server._worker._restart()
    prh3 = checker.try_aeneas(ORDER_PAIR_GOAL, "records.order_pair", rust_dir, candidate_id="restart_order_pair")
    check("halves restart: caller still proves after restart replays both halves",
          prh3.proved, prh3.error[:300])

    lean_server.shutdown_all()
    check("no lean process left after shutdown", server._worker is None)


if static:
    run_static()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
