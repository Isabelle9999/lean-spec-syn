"""bounded checking: run a candidate spec on concrete inputs before any prover.

for a rust unit, sampled inputs (edge values, then seeded random ones) go
through lean/aeneas_layer.lean's `lss_eval_spec`, which evaluates the call and
decides the spec's hypotheses and postcondition on each. in order:
  false     the postcondition fails on the function's real output, or the call
            fails (or diverges, under a spec that forbids it). the input is
            shrunk, then refuted with a kernel proof of `¬ stmt` through
            lss_check_proof when the witness allows one; otherwise the
            refutation is "evaluation only".
  narrow    the hypotheses let through no sampled input, or fewer than one in
            MAX_DISCARD_RATIO + 1 (QuickCheck's maxDiscardRatio): a warning, not
            a rejection, since a real precondition (a sorted list) can be rare
            in samples.
  vacuous   the postcondition also accepts every perturbed (wrong) output, and
            the statement claims no success either (no hypothesis filtered an
            input, the call never failed): it says nothing about the function.
types come from tools/translation_check.py's type IR, read from the unit's own
signature; a unit whose types it does not cover is skipped, and so is a spec
none of whose rows evaluates. every command is sent with the gate's own
Decidable instances (wf_gate.lean, wf_gate_aeneas.lean), never persisted, as
gate.py does: whatever the gate accepted as decidable is decided here the same way.
"""
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools"))
import translation_check as tc  # noqa: E402
import callgraph as _callgraph  # noqa: E402
import lean_server as _lean_server  # noqa: E402
import lss_config as _lss_config  # noqa: E402
import events  # noqa: E402
import lean as _lean  # noqa: E402
import gate as _gate  # noqa: E402

ROWS = 48
MAX_DISCARD_RATIO = 10
PERTURB_ROWS = 3
SHRINK_ROUNDS = 6
EVAL_TIMEOUT = 120


# ====================== values (the shape lean_literal and lean_encode_expr share) ======================

def _int_range(T):
    _, bits, signed = tc.INT_TYPES[T[1]]
    return (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)


def edge_values(T):
    """the values a bug most often hides behind, for one type."""
    kind = T[0]
    if kind == "bool":
        return [False, True]
    if kind == "int":
        lo, hi = _int_range(T)
        return list(dict.fromkeys([0, 1, hi, hi - 1, lo, lo + 1, -1 if lo < 0 else 2]))
    if kind == "tuple":
        return [[edge_values(e)[i % len(edge_values(e))] for e in T[1]] for i in range(2)]
    if kind == "array":
        return [[edge_values(T[1])[0]] * T[2], [edge_values(T[1])[-1]] * T[2]]
    if kind in ("slice", "vec"):
        e = edge_values(T[1])
        return [[], [e[0]], [e[1 % len(e)], e[0]], [e[0], e[1 % len(e)], e[2 % len(e)]]]
    if kind == "option":
        return [None, edge_values(T[1])[0]]
    return [random_value(T, random.Random(i)) for i in range(2)]


def random_value(T, rnd, depth=0):
    kind = T[0]
    if kind == "bool":
        return rnd.random() < 0.5
    if kind == "int":
        lo, hi = _int_range(T)
        # small values half the time: preconditions and loop bounds live there
        return rnd.randint(max(lo, -16), min(hi, 16)) if rnd.random() < 0.5 else rnd.randint(lo, hi)
    if kind == "tuple":
        return [random_value(e, rnd, depth) for e in T[1]]
    if kind == "array":
        return [random_value(T[1], rnd, depth + 1) for _ in range(T[2])]
    if kind in ("slice", "vec"):
        xs = [random_value(T[1], rnd, depth + 1) for _ in range(rnd.randint(0, 4 if depth == 0 else 2))]
        if T[1][0] == "int" and rnd.random() < 0.3:
            xs.sort()  # sorted inputs are rare at random but a common precondition
        return xs
    if kind == "struct":
        return {fn: random_value(ft, rnd, depth + 1) for fn, ft in T[2]}
    if kind == "enum":
        vname, arg_types = rnd.choice(T[2]) if depth < 3 else min(T[2], key=lambda v: len(v[1]))
        return {"tag": vname, "args": [random_value(a, rnd, depth + 1) for a in arg_types]}
    if kind == "list_enum":
        _, _, nil_v, cons_v, elem_T = T
        out = {"tag": nil_v, "args": []}
        for _ in range(rnd.randint(0, 3 if depth < 2 else 0)):
            out = {"tag": cons_v, "args": [random_value(elem_T, rnd, depth + 1), out]}
        return out
    if kind == "option":
        return None if rnd.random() < 0.3 else random_value(T[1], rnd, depth + 1)
    raise tc.Unsupported(f"no generator for {T!r}")


def sample_rows(arg_types, n=ROWS, seed=0):
    """edge-value rows first (each argument cycling through its own edge
    values), then seeded random rows, without duplicates."""
    rnd = random.Random(seed)
    edges = [edge_values(t) for t in arg_types]
    rows, seen = [], set()

    def add(row):
        key = json.dumps(row, sort_keys=True)
        if key not in seen:
            seen.add(key)
            rows.append(row)
    for i in range(max((len(e) for e in edges), default=1)):
        add([e[i % len(e)] for e in edges])
    tries = 0
    while len(rows) < n and tries < 20 * n:
        tries += 1
        add([random_value(t, rnd) for t in arg_types])
    return rows[:n]


def perturb(T, v):
    """wrong values of type T near v (never v itself)."""
    kind = T[0]
    out = []
    if kind == "bool":
        out = [not v]
    elif kind == "int":
        lo, hi = _int_range(T)
        n = int(v)
        out = [x for x in dict.fromkeys((n + 1, n - 1, 0, hi, lo)) if lo <= x <= hi and x != n]
    elif kind == "tuple":
        for i, e in enumerate(T[1]):
            for p in perturb(e, v[i])[:2]:
                out.append(v[:i] + [p] + v[i + 1:])
    elif kind == "array":
        if v:
            out = [[p] + v[1:] for p in perturb(T[1], v[0])[:2]]
    elif kind in ("slice", "vec"):
        e = edge_values(T[1])[0]
        out = ([v[:-1]] if v else []) + [v + [e]] + ([[p] + v[1:] for p in perturb(T[1], v[0])[:1]] if v else [])
    elif kind == "struct":
        for fn, ft in T[2]:
            for p in perturb(ft, v[fn])[:1]:
                out.append({**v, fn: p})
    elif kind == "enum":
        args = dict(T[2])[v["tag"]]
        out = [{"tag": n, "args": [edge_values(a)[0] for a in a_t]} for n, a_t in T[2] if n != v["tag"]][:2]
        for i, a in enumerate(args):
            for p in perturb(a, v["args"][i])[:1]:
                out.append({"tag": v["tag"], "args": v["args"][:i] + [p] + v["args"][i + 1:]})
    elif kind == "list_enum":
        _, _, nil_v, cons_v, elem_T = T
        out = [v["args"][1]] if v["tag"] == cons_v else []
        out.append({"tag": cons_v, "args": [edge_values(elem_T)[0], v]})
    elif kind == "option":
        out = [None] if v is not None else [edge_values(T[1])[0]]
        if v is not None:
            out += [p for p in perturb(T[1], v)[:1]]
    out = [x for x in out if json.dumps(x, sort_keys=True) != json.dumps(v, sort_keys=True)]
    return out[:6]


def shrink(T, v):
    """simpler values than v. for an int: 0, 1, the powers of two below it, and
    the steps n - n/2^k toward it (QuickCheck's shrinkIntegral), so the
    smallest failing candidate is found in a few rounds, not one halving each."""
    kind = T[0]
    if kind == "int":
        n = int(v)
        a = abs(n)
        cands = [0, 1] + [1 << k for k in range(a.bit_length())] + [a - (a >> k) for k in range(1, a.bit_length())]
        sign = -1 if n < 0 else 1
        return sorted({sign * c for c in cands if c < a}, key=abs)
    if kind == "bool":
        return [False] if v else []
    if kind in ("slice", "vec"):
        out = [v[:i] + v[i + 1:] for i in range(len(v))]
        for i, x in enumerate(v):
            out += [v[:i] + [s] + v[i + 1:] for s in shrink(T[1], x)[:1]]
        return out
    if kind in ("tuple", "array"):
        ts = T[1] if kind == "tuple" else [T[1]] * len(v)
        return [v[:i] + [s] + v[i + 1:] for i, t in enumerate(ts) for s in shrink(t, v[i])[:1]]
    if kind == "option":
        return [None] if v is not None else []
    if kind == "list_enum":
        return [v["args"][1]] if v["tag"] == T[3] else []
    return []


def size(T, v):
    """how complex a value is, for picking the simplest failing input."""
    kind = T[0]
    if kind == "int":
        return abs(int(v))
    if kind == "bool":
        return int(bool(v))
    if kind in ("slice", "vec", "array"):
        return (1 << 40) * len(v) + sum(size(T[1], x) for x in v)
    if kind == "tuple":
        return sum(size(t, x) for t, x in zip(T[1], v))
    if kind == "option":
        return 0 if v is None else 1 + size(T[1], v)
    return len(json.dumps(v))


# ====================== lean commands ======================

def _q(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def _lits(arg_types, row):
    return "[" + ", ".join(_q(tc.lean_literal(t, v)) for t, v in zip(arg_types, row)) + "]"


def eval_command(tag, stmt, arg_types, ret_type, rows):
    enc = "fun v => " + tc.lean_encode_expr(ret_type, "v")
    return (f"lss_eval_spec {tag} stmt:{_q(stmt)} enc:{_q(enc)} rows:["
            + ", ".join(_lits(arg_types, r) for r in rows) + "]")


def post_command(tag, stmt, arg_types, ret_type, row, outs):
    return (f"lss_eval_post {tag} stmt:{_q(stmt)} row:{_lits(arg_types, row)} outs:["
            + ", ".join(_q(tc.lean_literal(ret_type, o)) for o in outs) + "]")


def parse_evals(text):
    """every LSS_EVAL message in `text`, keyed by tag."""
    out = {}
    for m in re.finditer(r"LSS_EVAL (\{[^\n]*\})", text or ""):
        try:
            v = json.loads(m.group(1))
        except json.JSONDecodeError:
            continue
        out[v.get("tag")] = v
    return out


def refutation_text(name, stmt, unit, binders, arg_types, ret_type, row, outcome, value):
    """`theorem <name> : ¬ (<stmt>)` proved from the shrunk witness: instantiate
    the statement at the witness (hypotheses by decide), compute the call, and
    show the postcondition is false on its value (or that the call does not
    succeed). `spec` statements only: `dspec` refutations stay evaluation-only."""
    lits = [tc.lean_literal(t, v) for t, v in zip(arg_types, row)]
    app = " ".join(f"({lits[int(b[1:])]})" if b != "h" else "(by first | decide | simp_all | omega)"
                   for b in binders)
    call = f"{unit} " + " ".join(f"({x})" for x in lits)
    if outcome == "violates":
        got = f"Aeneas.Std.Result.ok ({tc.lean_literal(ret_type, json.loads(value))})"
    elif outcome == "fail":
        got = f"Aeneas.Std.Result.fail {value}"
    else:
        got = "Aeneas.Std.Result.div"
    lines = [f"theorem {name} : ¬ ({stmt}) := by",
             "  intro h",
             f"  obtain ⟨y, hy, hp⟩ := Aeneas.Std.WP.spec_imp_exists (h {app})",
             f"  have hv : {call} = {got} := by first | rfl | decide",
             "  rw [hv] at hy",
             "  cases hy"]
    if outcome == "violates":
        lines += ["  revert hp", "  first | decide | simp | omega"]
    return "\n".join(lines)


# ====================== the check ======================

def signature(project_dir, unit):
    """(lean name, argument types, return type) of a rust unit, in the type IR."""
    g = _callgraph.for_project(project_dir)
    crate = g.crate
    name = unit if unit in g.names else f"{crate}.{unit}"
    types_path = os.path.join(project_dir, crate, "Code", "Types.lean")
    types_text = open(types_path, encoding="utf-8").read() if os.path.exists(types_path) else ""
    custom, skipped = tc.resolve_custom_types(tc.parse_custom_types(types_text, crate), crate)
    def_text = g.def_text(name)
    if def_text is None:
        raise tc.Unsupported("no definition text")
    short = name[len(crate) + 1:] if name.startswith(crate + ".") else name
    args, ret = tc.parse_signature(def_text, short, custom)
    for t in [a for _, a in args] + [ret]:
        if t[0] in ("struct", "enum", "list_enum") and t[1] in skipped:
            raise tc.Unsupported(f"type {t[1]}: {skipped[t[1]]}")
    return name, [a for _, a in args], ret


class _Lean:
    """the crate environment the aeneas layer already keeps (one per crate)."""

    def __init__(self, checker, project_dir):
        self.checker, self.project_dir, self.n = checker, project_dir, 0
        self.prefix = _gate._wf_gate_text() + "\n" + _gate._wf_gate_aeneas_text() + "\n"  # then `open <crate>`

    def run(self, text):
        state = self.checker._aeneas_env_for(self.project_dir)
        if not state["ok"]:
            return None, "env"
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        # LSS's commands before `open <crate>`, as in the crate env (lean._aeneas_build_env)
        r = server.check(self.prefix + f"open {state['crate']}\n" + text, timeout=EVAL_TIMEOUT, env=state["env0"])
        self.checker.lean_calls += 1
        if r.timed_out:
            return None, "timeout"
        return (r.stdout or "") + (r.stderr or ""), ""

    def eval(self, stmt, args, ret, rows):
        results = []
        for i in range(0, len(rows), tc.MAX_BATCH):
            self.n += 1
            tag = f"lss_eval_{self.n}"
            out, why = self.run(eval_command(tag, stmt, args, ret, rows[i:i + tc.MAX_BATCH]))
            if out is None:
                return None, why
            v = parse_evals(out).get(tag)
            if v is None or not v.get("ok"):
                return None, (v or {}).get("detail", out.strip()[:300])
            results.append(v)
        return {"kind": results[0]["kind"], "binders": results[0]["binders"],
                "rows": [r for v in results for r in v["rows"]]}, ""

    def post(self, stmt, args, ret, row, outs):
        self.n += 1
        tag = f"lss_eval_{self.n}"
        out, _ = self.run(post_command(tag, stmt, args, ret, row, outs))
        v = parse_evals(out).get(tag) if out else None
        return v["outs"] if v and v.get("ok") else None


def _bad(kind, row):
    o = row["outcome"]
    return o in ("violates", "fail") or (o == "div" and kind == "spec")


@events.layer("bounded")
def check_spec(checker, stmt, unit, project_dir, seed=0):
    """the bounded verdict for one candidate (see the module docstring).
    status: pass, refuted, vacuous, timeout or skipped; warning: None, narrow or
    no_witness; a refutation carries the shrunk witness, whether the kernel
    checked it, and the feedback text a repair prompt uses."""
    try:
        name, args, ret = signature(project_dir, unit)
    except tc.Unsupported as e:
        return {"status": "skipped", "detail": e.reason}
    except OSError as e:  # no translated crate at project_dir: nothing to run
        return {"status": "skipped", "detail": str(e)}
    lean = _Lean(checker, project_dir)
    rows = sample_rows(args, seed=seed)
    ev, why = lean.eval(stmt, args, ret, rows)
    if ev is None:
        return {"status": "timeout" if why == "timeout" else "skipped", "detail": why}
    kind, outs = ev["kind"], ev["rows"]
    errors = [r for r in outs if r["outcome"] == "error"]
    if len(errors) == len(outs):
        return {"status": "skipped", "detail": errors[0].get("detail", "")[:300]}
    bad = [i for i, r in enumerate(outs) if _bad(kind, r)]
    if bad:
        row, res = rows[bad[0]], outs[bad[0]]
        for _ in range(SHRINK_ROUNDS):
            cands = [row[:j] + [s] + row[j + 1:] for j, t in enumerate(args) for s in shrink(t, row[j])]
            cands = cands[:2 * tc.MAX_BATCH]
            if not cands:
                break
            sev, _ = lean.eval(stmt, args, ret, cands)
            hits = [k for k, r in enumerate(sev["rows"]) if _bad(kind, r)] if sev else []
            if not hits:
                break
            k = min(hits, key=lambda k: sum(size(t, x) for t, x in zip(args, cands[k])))
            row, res = cands[k], sev["rows"][k]
        kernel = False
        if kind == "spec":
            lean.n += 1
            nm = f"lss_refute_{lean.n}"
            text = refutation_text(nm, stmt, name, ev["binders"], args, ret, row, res["outcome"], res["value"])
            hb = _lss_config.proof_cfg()["aeneas_heartbeats"]
            out, _ = lean.run(_lean.proof_check_call(text, nm, hb))
            kernel = bool((_lean.parse_proof_verdicts(out).get(nm) or {}).get("ok")) if out else False
        shown = ", ".join(tc.lean_literal(t, v) for t, v in zip(args, row))
        got = f"returned {res['value']}" if res["outcome"] == "violates" else f"gave {res['outcome']} {res['value']}".strip()
        return {"status": "refuted", "kernel": kernel, "witness": row, "outcome": res["outcome"],
                "value": res.get("value", ""),
                "feedback": (f"On input ({shown}) the function {got}, and the statement is false there "
                             f"(checked by running the function{', and by a kernel proof' if kernel else ''}).")}
    fit = [i for i, r in enumerate(outs) if r["outcome"] == "holds"]
    discard = sum(1 for r in outs if r["outcome"] == "discard")
    warning = None
    if not fit:
        warning = "no_witness"
    elif discard > MAX_DISCARD_RATIO * len(fit):
        warning = "narrow"
    verdict = {"status": "pass", "warning": warning, "fit": len(fit), "discard": discard, "sampled": len(rows)}
    claims_success = discard > 0 or any(r["outcome"] in ("fail", "div") for r in outs)
    checked = 0
    rejects = False
    for i in fit[:PERTURB_ROWS]:
        wrong = perturb(ret, json.loads(outs[i]["value"]))
        if not wrong:
            continue
        got = lean.post(stmt, args, ret, rows[i], wrong)
        if got is None:
            continue
        checked += 1
        if "violates" in got:
            rejects = True
            break
    if checked and not rejects and not claims_success:
        verdict.update(status="vacuous",
                       feedback="The statement holds for every output tried, including wrong ones, "
                                "so it says nothing about what the function computes.")
    return verdict
