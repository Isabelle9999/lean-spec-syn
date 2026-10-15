import os
import re
import json
import lean_server as _lean_server
import lss_config as _lss_config
import callgraph as _callgraph
import lean as _lean

CHECK_ORDER = ["one_theorem", "is_theorem", "no_attribute", "conclusion_shape", "vocabulary", "decidable"]

_GATE_DIR = os.path.dirname(os.path.abspath(__file__))
_WF_GATE_PATH = os.path.join(_GATE_DIR, "lean", "wf_gate.lean")
_WF_GATE_AENEAS_PATH = os.path.join(_GATE_DIR, "lean", "wf_gate_aeneas.lean")
_wf_gate_cache = None
_wf_gate_aeneas_cache = None


def _wf_gate_text():
    global _wf_gate_cache
    if _wf_gate_cache is None:
        with open(_WF_GATE_PATH, encoding="utf-8") as f:
            _wf_gate_cache = f.read()
    return _wf_gate_cache


def _wf_gate_aeneas_text():
    global _wf_gate_aeneas_cache
    if _wf_gate_aeneas_cache is None:
        with open(_WF_GATE_AENEAS_PATH, encoding="utf-8") as f:
            _wf_gate_aeneas_cache = f.read()
    return _wf_gate_aeneas_cache


def _escape_lean_str(s):
    return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def _env_fail(detail):
    # "env" is not one of CHECK_ORDER's six named checks: this is a meta-level
    # failure (crate/base environment never came up), not a verdict on the
    # candidate itself.
    return [{"gate": "wf", "check": "env", "ok": False, "detail": detail}]


def _parse_verdicts(text):
    verdicts = []
    for m in re.finditer(r"LSS_WF (\{[^\n]*\})", text or ""):
        try:
            verdicts.append(json.loads(m.group(1)))
        except json.JSONDecodeError:
            continue
    return verdicts


def check_candidate(lean_checker, candidate_text, func_name, lean_code, project_dir, source):
    """run the well-formedness gate on `candidate_text` (a full, self-contained
    `theorem <name> (binders) (hyps) : <stmt> := sorry` declaration -- not just a
    statement string). returns a list of {gate, check, ok, detail} verdicts, in
    CHECK_ORDER, stopping at the first ok=false (same short-circuit the Lean side
    itself applies). a candidate is well-formed iff all six checks ran and passed.
    """
    is_rust = source == "rust-aeneas" and _lss_config.proof_cfg()["aeneas_layer"]
    esc = _escape_lean_str(candidate_text)

    if is_rust:
        state = lean_checker._aeneas_env_for(project_dir)
        if not state["ok"]:
            return _env_fail(f"crate env unavailable: {state['error'][:200]}")
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        env = state["env"]
        g = _callgraph.for_project(project_dir)
        manifest_names = sorted(g.names)
        # callgraph keys everything by the crate-qualified name (e.g.
        # "FeatureSuite.search.linear_search"), but callers pass func_name the
        # same unqualified way Lean source itself writes it under `open <crate>`
        # (e.g. "search.linear_search", matching unit: below) -- qualify before
        # asking the graph about it.
        qualified_func = func_name if func_name in g.names else f"{g.crate}.{func_name}"
        allow_div = g.can_diverge(qualified_func) or g.recursive(qualified_func)
        gate_src = _wf_gate_text() + "\n" + _wf_gate_aeneas_text()
        track_tok = "rust"
    else:
        native_dir = _lss_config.project_dir("lean-native")
        target_dir = project_dir or native_dir
        server = _lean_server.get_server(target_dir)
        base = "import Mathlib\n" + lean_code.rstrip() + "\n"
        r0 = server.check(base, timeout=180)
        if r0.rc != 0 or r0.new_env is None:
            return _env_fail(f"base environment failed: {((r0.stderr or '') + (r0.stdout or ''))[:200]}")
        env = r0.new_env
        # the unit only: wf_gate.lean adds the unit's own auxiliaries from the
        # environment, so a `_precond` def stays usable in a hypothesis.
        manifest_names = [func_name]
        allow_div = False
        # proof_check.lean holds the parsing helpers the gate uses; on the rust
        # track it is already part of the crate env (lean._aeneas_build_env)
        gate_src = _lean.proof_check_text() + "\n" + _wf_gate_text()
        track_tok = "native"

    div_tok = "allow_div" if allow_div else "no_div"
    manifest_literal = ", ".join(manifest_names)
    call = f'lss_wf_gate "{esc}" unit:{func_name} manifest:[{manifest_literal}] {div_tok} {track_tok}\n'
    r = server.check(gate_src + "\n" + call, env=env, timeout=90)
    combined = (r.stdout or "") + "\n" + (r.stderr or "")
    verdicts = _parse_verdicts(combined)
    if not verdicts and not (r.timed_out or r.mem_killed):
        return _env_fail(f"gate produced no verdicts: {combined.strip()[:300]}")
    if is_well_formed(verdicts) or not all(v.get("ok") for v in verdicts):
        return verdicts
    # every check so far passed but the gate stopped early (timeout, memory cap or
    # an error inside a check): reject at the first check that never ran, so the
    # candidate neither passes nor stops the run.
    errors = [ln for ln in combined.splitlines() if ": error" in ln] or ["no error reported"]
    reason = "timed out" if r.timed_out else "hit the memory cap" if r.mem_killed else errors[0][:300]
    ran = {v.get("check") for v in verdicts}
    missing = next((c for c in CHECK_ORDER if c not in ran), CHECK_ORDER[-1])
    verdicts.append({"gate": "wf", "check": missing, "ok": False,
                     "detail": f"gate stopped before this check: {reason}"})
    return verdicts


def is_well_formed(verdicts):
    # all six checks ran, in order, and passed: a list that stops early is not a pass
    return [v.get("check") for v in verdicts] == CHECK_ORDER and all(v.get("ok") for v in verdicts)


def failing_check(verdicts):
    for v in verdicts:
        if not v.get("ok"):
            return v.get("check")
    return None
