"""bounded checking: run a candidate spec on concrete inputs before any prover.

for a rust unit, lean/bounded.lean's `lss_eval_plan` reads the statement first: a
generic one is checked at one instantiation (its type binders at the type of the
crate's instance of a trait it takes, else U32; its trait binders at the crate's
instance, once the kernel has a proof that the instance meets the statement's
hypotheses on it), and a binder that a hypothesis `x = e` defines takes the value
of `e`. sampled inputs for the other binders (edge values, then seeded random
ones) then go through `lss_eval_spec`, which evaluates the call and decides the
spec's hypotheses and postcondition on each. in order:
  false     the postcondition fails on the function's real output, or the call
            fails (or diverges, under a spec that forbids it). the input is
            shrunk, then refuted with a kernel proof of `¬ stmt` through
            lss_check_proof when the witness allows one; otherwise the
            refutation is "evaluation only". a counterexample at the
            instantiation refutes the statement for every type.
  narrow    the hypotheses let through no sampled input, or fewer than one in
            MAX_DISCARD_RATIO + 1 (QuickCheck's maxDiscardRatio): a warning, not
            a rejection, since a real precondition (a sorted list) can be rare
            in samples.
  vacuous   the postcondition also accepts every perturbed (wrong) output, and
            the statement claims no success either (no hypothesis filtered an
            input, the call never failed): it says nothing about the function.
a statement the check cannot evaluate is "not_evaluated", with the reason, and
goes on to the provers: no instance of a trait it takes in the crate, an instance
that does not meet its hypotheses, a type the samplers do not cover, or a
hypothesis or postcondition not Decidable at the instantiation (a statement about
a backward function's every input). types come from Lean itself (lssTypeIR), in
tools/translation_check.py's type IR. the commands run in the check's own env
(_Lean), which holds the gate's Decidable instances and DecidableEq for the
crate's own types; proofs never run in it.
"""
import itertools
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools"))
import translation_check as tc  # noqa: E402
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


def _sized(T):
    """an array whose length a binder gives (a const generic) is drawn like a Vec: its
    length is free, and check_spec then gives that binder the array's length."""
    return ("vec", T[1]) if T[0] == "array" and T[2] is None else T


def _named(T):
    return T[0] in ("struct", "enum", "list_enum")


def edge_values(T, self_T=None):
    """the values a bug most often hides behind, for one type."""
    T = _sized(T)
    kind = T[0]
    if kind == "self":
        return [random_value(self_T, random.Random(i), 3, self_T) for i in range(2)]
    if _named(T):
        self_T = T
    if kind == "bool":
        return [False, True]
    if kind == "int":
        lo, hi = _int_range(T)
        return list(dict.fromkeys([0, 1, hi, hi - 1, lo, lo + 1, -1 if lo < 0 else 2]))
    if kind == "tuple":
        es = [edge_values(e, self_T) for e in T[1]]
        return [[e[i % len(e)] for e in es] for i in range(2)]
    if kind == "array":
        e = edge_values(T[1], self_T)
        return [[e[0]] * T[2], [e[-1]] * T[2]]
    if kind in ("slice", "vec"):
        e = edge_values(T[1], self_T)
        return [[], [e[0]], [e[1 % len(e)], e[0]], [e[0], e[1 % len(e)], e[2 % len(e)]]]
    if kind == "option":
        return [None, edge_values(T[1], self_T)[0]]
    return [random_value(T, random.Random(i)) for i in range(2)]


def _self_refs(t):
    """how many times a variant argument refers to its own type."""
    if t[0] == "self":
        return 1
    if t[0] == "tuple":
        return sum(_self_refs(e) for e in t[1])
    if t[0] in ("option", "array", "slice", "vec"):
        return _self_refs(t[1])
    return 0


def random_value(T, rnd, depth=0, self_T=None):
    T = _sized(T)
    kind = T[0]
    if kind == "self":
        return random_value(self_T, rnd, depth, self_T)
    if _named(T):
        self_T = T
    if kind == "bool":
        return rnd.random() < 0.5
    if kind == "int":
        lo, hi = _int_range(T)
        # small values half the time: preconditions and loop bounds live there
        return rnd.randint(max(lo, -16), min(hi, 16)) if rnd.random() < 0.5 else rnd.randint(lo, hi)
    if kind == "tuple":
        return [random_value(e, rnd, depth, self_T) for e in T[1]]
    if kind == "array":
        return [random_value(T[1], rnd, depth + 1, self_T) for _ in range(T[2])]
    if kind in ("slice", "vec"):
        n = 0 if depth >= 3 and _self_refs(T[1]) else rnd.randint(0, 4 if depth == 0 else 2)
        xs = [random_value(T[1], rnd, depth + 1, self_T) for _ in range(n)]
        if T[1][0] == "int" and rnd.random() < 0.3:
            xs.sort()  # sorted inputs are rare at random but a common precondition
        return xs
    if kind == "struct":
        return {fn: random_value(ft, rnd, depth + 1, self_T) for fn, ft in T[2]}
    if kind == "enum":
        # past depth 3, the variant with the fewest references to itself ends the value
        vname, arg_types = rnd.choice(T[2]) if depth < 3 else \
            min(T[2], key=lambda v: (sum(_self_refs(a) for a in v[1]), len(v[1])))
        return {"tag": vname, "args": [random_value(a, rnd, depth + 1, self_T) for a in arg_types]}
    if kind == "list_enum":
        nil_v, cons_v, elem_T = T[2], T[3], T[4]
        out = {"tag": nil_v, "args": []}
        for _ in range(rnd.randint(0, 3 if depth < 2 else 0)):
            out = {"tag": cons_v, "args": [random_value(elem_T, rnd, depth + 1), out]}
        return out
    if kind == "option":
        if depth >= 3 and _self_refs(T[1]):
            return None
        return None if rnd.random() < 0.3 else random_value(T[1], rnd, depth + 1, self_T)
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


def _children(T, v, self_T):
    """the values of T's own type directly inside v (a tree's subtrees)."""
    kind = T[0]
    if kind == "self":
        return [v]
    if kind == "option":
        return [] if v is None else _children(T[1], v, self_T)
    if kind == "tuple":
        return [c for e, x in zip(T[1], v) for c in _children(e, x, self_T)]
    if kind in ("array", "slice", "vec"):
        return [c for x in v for c in _children(T[1], x, self_T)]
    return []


def perturb(T, v, self_T=None):
    """wrong values of type T near v (never v itself)."""
    T = _sized(T)
    kind = T[0]
    if kind == "self":
        return perturb(self_T, v, self_T)
    if _named(T):
        self_T = T
    out = []
    if kind == "bool":
        out = [not v]
    elif kind == "int":
        lo, hi = _int_range(T)
        n = int(v)
        out = [x for x in dict.fromkeys((n + 1, n - 1, 0, hi, lo)) if lo <= x <= hi and x != n]
    elif kind == "tuple":
        for i, e in enumerate(T[1]):
            for p in perturb(e, v[i], self_T)[:2]:
                out.append(v[:i] + [p] + v[i + 1:])
    elif kind == "array":
        if v:
            out = [[p] + v[1:] for p in perturb(T[1], v[0], self_T)[:2]]
    elif kind in ("slice", "vec"):
        e = edge_values(T[1], self_T)[0]
        out = ([v[:-1]] if v else []) + [v + [e]] + \
            ([[p] + v[1:] for p in perturb(T[1], v[0], self_T)[:1]] if v else [])
    elif kind == "struct":
        for fn, ft in T[2]:
            for p in perturb(ft, v[fn], self_T)[:1]:
                out.append({**v, fn: p})
    elif kind == "enum":
        args = dict(T[2])[v["tag"]]
        out = [{"tag": n, "args": [edge_values(a, self_T)[0] for a in a_t]} for n, a_t in T[2] if n != v["tag"]][:2]
        for i, a in enumerate(args):
            if a[0] == "self" or _self_refs(a):
                continue  # a subtree changed is covered by the variant and leaf changes
            for p in perturb(a, v["args"][i], self_T)[:1]:
                out.append({"tag": v["tag"], "args": v["args"][:i] + [p] + v["args"][i + 1:]})
    elif kind == "list_enum":
        nil_v, cons_v, elem_T = T[2], T[3], T[4]
        out = [v["args"][1]] if v["tag"] == cons_v else []
        out.append({"tag": cons_v, "args": [edge_values(elem_T)[0], v]})
    elif kind == "option":
        out = [None] if v is not None else [edge_values(T[1], self_T)[0]]
        if v is not None:
            out += [p for p in perturb(T[1], v, self_T)[:1]]
    out = [x for x in out if json.dumps(x, sort_keys=True) != json.dumps(v, sort_keys=True)]
    return out[:6]


def shrink(T, v, self_T=None):
    """simpler values than v, never v itself. for an int: 0, 1, the powers of two
    below it, and the steps n - n/2^k toward it (QuickCheck's shrinkIntegral), so
    the smallest failing candidate is found in a few rounds, not one halving each.
    a recursive value shrinks to its own subtrees first, then one argument at a
    time; a struct one field at a time; a list each element in turn (QuickCheck's
    shrinkList: drop an element, or shrink one)."""
    kind = T[0]
    if kind == "self":
        return shrink(self_T, v, self_T)
    if _named(T):
        self_T = T
    key = json.dumps(v, sort_keys=True)
    return [c for c in _shrink(kind, T, v, self_T) if json.dumps(c, sort_keys=True) != key]


def _interleave(lists):
    """every list's first item, then every list's second, ...: each position's simplest
    candidate comes before any position's second, so a cap on how many are tried never
    leaves a position (a field deep inside a list) with none."""
    return [x for rank in itertools.zip_longest(*lists, fillvalue=_NONE) for x in rank if x is not _NONE]


_NONE = object()


def _shrink(kind, T, v, self_T):
    T = _sized(T)
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
        return [v[:i] + v[i + 1:] for i in range(len(v))] + _interleave(
            [[v[:i] + [s] + v[i + 1:] for s in shrink(T[1], x, self_T)] for i, x in enumerate(v)])
    if kind in ("tuple", "array"):
        ts = T[1] if kind == "tuple" else [T[1]] * len(v)
        return _interleave([[v[:i] + [s] + v[i + 1:] for s in shrink(t, v[i], self_T)] for i, t in enumerate(ts)])
    if kind == "option":
        return [None] if v is not None else []
    if kind == "struct":
        return _interleave([[{**v, fn: s} for s in shrink(ft, v[fn], self_T)] for fn, ft in T[2]])
    if kind == "list_enum":
        nil_v, cons_v, elem_T = T[2], T[3], T[4]
        items, x = [], v
        while x["tag"] == cons_v:
            items.append(x["args"][0])
            x = x["args"][1]

        def chain(xs):
            out = {"tag": nil_v, "args": []}
            for e in reversed(xs):
                out = {"tag": cons_v, "args": [e, out]}
            return out
        return ([chain(items[1:])] if items else []) + [chain(items[:i] + items[i + 1:]) for i in range(1, len(items))] \
            + _interleave([[chain(items[:i] + [s] + items[i + 1:]) for s in shrink(elem_T, e)] for i, e in enumerate(items)])
    if kind == "enum":
        args = dict(T[2])[v["tag"]]
        subtrees = [c for a, x in zip(args, v["args"]) for c in _children(a, x, self_T)]
        return subtrees + _interleave([[{"tag": v["tag"], "args": v["args"][:i] + [s] + v["args"][i + 1:]}
                                        for s in shrink(a, v["args"][i], self_T)]
                                       for i, a in enumerate(args) if not _self_refs(a)])
    return []


def size(T, v, self_T=None):
    """how complex a value is, for picking the simplest failing input."""
    kind = T[0]
    if kind == "self":
        return size(self_T, v, self_T)
    if kind == "int":
        return abs(int(v))
    if kind == "bool":
        return int(bool(v))
    if kind in ("slice", "vec", "array"):
        return (1 << 40) * len(v) + sum(size(T[1], x, self_T) for x in v)
    if kind == "tuple":
        return sum(size(t, x, self_T) for t, x in zip(T[1], v))
    if kind == "option":
        return 0 if v is None else 1 + size(T[1], v, self_T)
    return len(json.dumps(v))


# ====================== lean commands ======================

def _q(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def eval_literal(T, v):
    """the Lean term for an evaluated input: an array, vector or slice of numbers as
    text read in compiled code (lean/bounded.lean's lssU/lssI and lssArr/lssVec/
    lssSlice), whose elaboration costs the same at any length; a tuple part by part;
    everything else as tc.lean_literal. a literal of 256 numbers takes elaboration
    about a second (each n#u8 also runs its bound tactic), so a check of 48 such
    inputs spent most of its time limit building them. evaluation only: a kernel
    refutation writes its witness as literals (refutation_text)."""
    kind = T[0]
    if kind in ("array", "vec", "slice") and T[1][0] == "int" and T[1][1] in tc.LEAN_SCALAR_SUFFIX:
        ty = T[1][1].split(".")[-1]
        nums = '"' + " ".join(str(int(x)) for x in v) + '"'
        dec = f"({'lssI' if ty.startswith('I') else 'lssU'} .{ty} {nums})"
        if kind == "array":
            n = len(v) if T[2] is None else T[2]
            return f"(lssArr (⟨0⟩ : {tc.lean_type_str(T[1])}) {n}#usize {dec})"
        return f"({'lssVec' if kind == 'vec' else 'lssSlice'} {dec})"
    if kind == "tuple":
        return "(" + ", ".join(eval_literal(e, x) for e, x in zip(T[1], v)) + ")"
    return tc.lean_literal(T, v)


def _lits(arg_types, row):
    return "[" + ", ".join(_q(eval_literal(t, v)) for t, v in zip(arg_types, row)) + "]"


def plan_command(tag, crate, stmt):
    return f"lss_eval_plan {tag} crate:{crate} stmt:{_q(stmt)}"


def eval_command(tag, crate, stmt, arg_types, ret_type, rows):
    """the encoder's defs (for a result type that contains itself), then the command.
    with no result type (a function in it), outcomes come back without values."""
    defs = []
    enc = "fun v => " + tc.lean_encode_expr(ret_type, "v", defs) if ret_type else 'fun _ => ""'
    return "".join(d + "\n" for d in defs) + (
        f"lss_eval_spec {tag} crate:{crate} stmt:{_q(stmt)} enc:{_q(enc)} rows:["
        + ", ".join(_lits(arg_types, r) for r in rows) + "]")


def post_command(tag, crate, stmt, arg_types, ret_type, row, outs):
    return (f"lss_eval_post {tag} crate:{crate} stmt:{_q(stmt)} row:{_lits(arg_types, row)} outs:["
            + ", ".join(_q(eval_literal(ret_type, o)) for o in outs) + "]")


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


def type_ir(j, top=False):
    """lean/bounded.lean's type IR (JSON) as translation_check's tuples; a Nil/Cons(T,
    Self) inductive becomes a list_enum. raises Unsupported on what Lean could not read."""
    if isinstance(j, dict) or not isinstance(j, list) or not j:
        raise tc.Unsupported((j or {}).get("unsupported", "type not read") if isinstance(j, dict) else "type not read")
    k = j[0]
    if k in ("bool", "self"):
        return (k,)
    if k == "int":
        if j[1] not in tc.INT_TYPES:
            raise tc.Unsupported(f"scalar {j[1]}")
        return ("int", j[1])
    if k == "tuple":
        return ("tuple", [type_ir(e) for e in j[1]])
    if k in ("option", "slice", "vec"):
        return (k, type_ir(j[1]))
    if k == "array":
        if isinstance(j[2], dict):  # a const generic length, named by the binder that gives it
            if not top:
                raise tc.Unsupported("an array whose length a binder gives, inside another type")
            return ("array", type_ir(j[1]), None)
        m = re.match(r"^\(?(\d+)(#usize)?\)?$", j[2].strip())
        if not m:
            raise tc.Unsupported(f"array length {j[2]}")
        return ("array", type_ir(j[1]), int(m.group(1)))
    if k == "struct":
        return ("struct", j[1], [(f, type_ir(t)) for f, t in j[2]], j[3])
    if k == "enum":
        variants = [(v, [type_ir(a) for a in args]) for v, args in j[2]]
        nonrec = [v for v in variants if not v[1]]
        rec = [v for v in variants if len(v[1]) == 2 and v[1][1] == ("self",) and not _self_refs(v[1][0])]
        if len(variants) == 2 and len(nonrec) == 1 and len(rec) == 1:
            return ("list_enum", j[1], nonrec[0][0], rec[0][0], rec[0][1][0], j[3])
        return ("enum", j[1], variants, j[3])
    raise tc.Unsupported(f"type kind {k}")


# Aeneas's own definitions a call's evaluation unfolds into: Vec indexing, the scalar
# operations with their bounds check (ok or integerOverflow), and lean/bounded.lean's
# lemmas that turn a scalar `+ - * / %` (an unnamed instance) into the named operation
EVAL_DEFS = ["Aeneas.Std.alloc.vec.Vec.index_mut_usize", "Aeneas.Std.alloc.vec.Vec.index_usize",
             "Aeneas.Std.alloc.vec.Vec.set", "Aeneas.Std.alloc.vec.Vec.len",
             "lss_eval_uadd", "lss_eval_usub", "lss_eval_umul", "lss_eval_udiv", "lss_eval_urem",
             "lss_eval_iadd", "lss_eval_isub", "lss_eval_imul", "lss_eval_idiv", "lss_eval_irem",
             "Aeneas.Std.UScalar.add", "Aeneas.Std.UScalar.sub", "Aeneas.Std.UScalar.mul", "Aeneas.Std.UScalar.div",
             "Aeneas.Std.UScalar.rem", "Aeneas.Std.IScalar.add", "Aeneas.Std.IScalar.sub", "Aeneas.Std.IScalar.mul",
             "Aeneas.Std.IScalar.div", "Aeneas.Std.IScalar.rem",
             "Aeneas.Std.UScalar.tryMk", "Aeneas.Std.UScalar.tryMkOpt", "Aeneas.Std.IScalar.tryMk",
             "Aeneas.Std.IScalar.tryMkOpt", "Aeneas.Std.Result.ofOption"]
EVAL_ROUNDS = 32
# with the platform split: the Usize/Isize bit width (System.Platform.numBits, fixed by
# the split's hypothesis lss_hb), and the 64-bit edge values written as the platform's
# own constants (EDGE_CONSTS)
WIDTH_DEFS = ["Aeneas.Std.Usize.numBits", "Aeneas.Std.Isize.numBits", "Aeneas.Std.core.num.Usize.MAX",
              "Aeneas.Std.Usize.max", "Aeneas.Std.core.num.Isize.MAX", "Aeneas.Std.Isize.max",
              "Aeneas.Std.core.num.Isize.MIN"]
EDGE_CONSTS = {("Std.Usize", 2 ** 64 - 1): "Aeneas.Std.core.num.Usize.MAX",
               ("Std.Isize", 2 ** 63 - 1): "Aeneas.Std.core.num.Isize.MAX",
               ("Std.Isize", -2 ** 63): "Aeneas.Std.core.num.Isize.MIN"}


def eval_tactic(unfold, ops=(), split=False):
    """a tactic evaluating the call in the goal: unfold `loop` once per round (its
    equation always applies again, so it is never a simp lemma: `simp [loop]` runs
    forever), then simp with the unit, its callees and Aeneas's definitions evaluates
    what that exposed: EVAL_DEFS, the operations the call reaches (`ops`, from
    lss_eval_ops) and, after the platform split, its hypothesis and WIDTH_DEFS. it is
    parenthesized: `iterate` takes a tactic sequence, so a tactic written after it with
    `;` would otherwise run inside every round."""
    names = ", ".join((["lss_hb"] if split else []) + list(unfold) + EVAL_DEFS + list(ops)
                      + (WIDTH_DEFS if split else []))
    return f"(iterate {EVAL_ROUNDS} (try ((try rw [Aeneas.Std.loop]); simp [{names}])))"


def unfold_names(project_dir, unit):
    """the unit and every function it calls, with each loop's body, crate-qualified
    (a unit `C.List.length` stripped of `C.` would clash with Lean's own); opaque ones
    (no body) left out. [] when there is no call graph."""
    import callgraph
    try:
        g = callgraph.for_project(project_dir)
    except OSError:
        return []
    q = unit if unit in g.names else f"{g.crate}.{unit}"
    if q not in g.names:
        return []
    out = []
    for n in sorted({q} | g.transitive_callees(q)):
        for m in (n, f"{n}.body"):
            if m in g.names and not g.is_opaque(m) and m not in out:
                out.append(m)
    return out


def refutation_text(name, stmt, binders, insts, arg_types, ret_type, row, outcome, value, unfold=(),
                    stated=False, ops=(), split=False, div=False):
    """`theorem <name> : ¬ (<stmt>)` proved from the shrunk witness: instantiate the
    statement at the check's instantiation (its types, the crate's instances and their
    laws by lss_law_tac) and the witness (a defined binder by unification, the
    hypotheses by decide), then show the call fails or its value breaks the
    postcondition: by evaluating the call with its value left open (eval_tactic), or,
    with `stated`, by stating that value and letting rfl or decide compute the call (the
    kernel unfolds what simp has no name for, such as a trait instance passed as an
    argument). check_spec tries the evaluation first and the stated value in a theorem
    of its own: a heartbeat or recursion limit is not an error `first` can catch, so
    one way running out must not keep the other from being tried.
    h is first applied to variables in place of the witness, its defined binders and
    its hypotheses, and that function is then applied to them: applying h to the
    literals directly leaves the triple as the application's type, which the elaborator
    reduces looking for further arguments, evaluating the call in unary Nat arithmetic
    (a value like 2^31 reaches the recursion limit). a defined binder is a variable too,
    given as `_` and fixed by the hypothesis that defines it.
    `ops` adds the operations the call reaches to the evaluation. `split` evaluates once
    per platform bit width (System.Platform.numBits_eq: a Usize bound is 2^numBits) and
    writes a witness at a 64-bit edge as the platform's own constant (EDGE_CONSTS): the
    literal itself exists only on a 64-bit platform, so its proof needs native_decide;
    the constant exists on both, and the refutation holds only if the call fails there
    on both. `div` refutes a ⦄div statement (dspec): by lss_dspec_cases the call either
    returns a value its postcondition holds of or diverges, and each case is evaluated."""
    lits = [EDGE_CONSTS.get((t[1], v)) if split and t[0] == "int" and isinstance(v, int) else None
            for t, v in zip(arg_types, row)]
    lits = [lit or tc.lean_literal(t, v) for lit, t, v in zip(lits, arg_types, row)]
    law = "(by lss_law_tac [" + ", ".join(insts) + "])"
    fixed = {"class": "(inferInstance)", "law": law}
    xs, parts, given = [], [], []
    for b in binders:
        k = b.get("k")
        if k in ("type", "inst"):
            parts.append(f"({b.get('v')})")
        elif k in fixed:
            parts.append(fixed[k])
        else:
            x = f"lss_x{len(xs)}"
            xs.append(x)
            parts.append(x)
            given.append({"hyp": "(by first | rfl | decide | simp_all | omega)", "det": "_"}.get(k)
                         or f"({lits[b['i']]})")
    spec = f"{'lss_dspec_cases' if div else 'Aeneas.Std.WP.spec_imp_exists'} (@h {' '.join(parts)})"
    if outcome == "violates":
        got = f"Aeneas.Std.Result.ok ({tc.lean_literal(ret_type, json.loads(value))})"
    elif outcome == "fail":
        got = f"Aeneas.Std.Result.fail {value}"
    else:
        got = "Aeneas.Std.Result.div"
    lines = [f"theorem {name} : ¬ ({stmt}) := by", "  intro h"]
    if xs:
        lines.append(f"  have lss_h := fun {' '.join(xs)} => {spec}")
        spec = f"lss_h {' '.join(given)}"
    if stated:
        ok_case = [f"have hv : (Aeneas.Std.Result.ok y : Aeneas.Std.Result _) = {got} := hy.symm.trans (by first | rfl | decide)",
                   "cases hv"] + (["revert hp", "first | decide | simp | omega"] if outcome == "violates" else [])
        div_case = [f"have hv : (Aeneas.Std.Result.div : Aeneas.Std.Result _) = {got} := hd.symm.trans (by first | rfl | decide)",
                    "cases hv"]
    else:
        ev = ((["rcases System.Platform.numBits_eq with lss_hb | lss_hb", f"all_goals {eval_tactic(unfold, ops, True)}"]
               if split else [eval_tactic(unfold, ops)]) + ["all_goals (first | decide | omega)"])
        ok_case, div_case = ["revert y"] + ev, ["revert hd"] + ev
    if div:
        lines += [f"  rcases {spec} with ⟨y, hy, hp⟩ | hd"] + ["  · " + "\n    ".join(c) for c in (ok_case, div_case)]
    else:
        lines += [f"  obtain ⟨y, hy, hp⟩ := {spec}"] + ["  " + t for t in ok_case]
    return "\n".join(lines)


# ====================== the check ======================

_BOUNDED_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "bounded.lean")


def _bounded_text():
    with open(_BOUNDED_PATH, encoding="utf-8") as f:
        return f.read()


_OPS = {}  # (project_dir, unit) -> the operations its call reaches (_Lean.ops)



class _Lean:
    """the bounded check's own env, built once per crate env on the crate env as
    built before the crate is opened ("env0"): the gate's Decidable instances
    (wf_gate.lean, wf_gate_aeneas.lean), lean/bounded.lean, and DecidableEq for
    the crate's types. proofs never run in it."""

    def __init__(self, checker, project_dir, helpers=""):
        self.checker, self.project_dir, self.n = checker, project_dir, 0
        self.helpers = _lean.helpers_command(helpers)
        self.prefix = _gate._wf_gate_text() + "\n" + _gate._wf_gate_aeneas_text() + "\n"
        self.crate = None

    def _env(self, server):
        state = self.checker._aeneas_env_for(self.project_dir)
        if not state["ok"]:
            return None, "env"
        self.crate = state["crate"]
        if state.get("check_env") is None or state.get("check_env_of") != state["env0"]:
            text = self.prefix + _bounded_text() + f"\nlss_derive_deceq crate:{state['crate']}\n"
            r = server.check(text, timeout=EVAL_TIMEOUT, env=state["env0"])
            self.checker.lean_calls += 1
            if r.timed_out:
                return None, "timeout"
            out = (r.stdout or "") + (r.stderr or "")
            errors = [ln for ln in out.splitlines() if ": error" in ln]
            if errors:
                # LSS's own Lean code failing to build is a setup error, never a verdict on
                # a candidate: stop, as the gate does when its environment is down
                raise RuntimeError("the bounded check's Lean code does not build: " + errors[0][:300])
            if r.new_env is None:  # the server lost it (a memory kill): this candidate goes on unchecked
                return None, "check env lost" + (" (memory cap)" if getattr(r, "mem_killed", False) else "")
            state["check_env"], state["check_env_of"] = r.new_env, state["env0"]
            state["check_derive"] = parse_evals((r.stdout or "") + (r.stderr or "")).get("derive")
        return state["check_env"], ""

    def run(self, text):
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        env, why = self._env(server)
        if env is None:
            return None, why
        r = server.check(f"namespace {self.crate}\n" + self.helpers + text, timeout=EVAL_TIMEOUT, env=env)
        self.checker.lean_calls += 1
        if r.timed_out:
            return None, "timeout"
        return (r.stdout or "") + (r.stderr or ""), ""

    def ops(self, unit, unfold):
        """the Aeneas operations `unit` reaches past EVAL_DEFS (lean/bounded.lean's
        lss_eval_ops), once per crate and unit."""
        key = (self.project_dir, unit)
        if key not in _OPS:
            # asked after an evaluation, which set self.crate
            out, _ = self.run(f"lss_eval_ops {self.crate} " + " ".join(unfold)) if unfold else (None, "")
            m = re.search(r"LSS_OPS (\[[^\n]*\])", out or "")
            if not m:
                return []  # not kept: a failed run (a timeout, a lost env) is asked again next time
            _OPS[key] = [n for n in json.loads(m.group(1)) if n not in EVAL_DEFS]
        return _OPS[key]

    def _one(self, make):
        self.n += 1
        tag = f"lss_eval_{self.n}"
        if self.crate is None:
            server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
            env, why = self._env(server)
            if env is None:
                return None, why
        out, why = self.run(make(tag))
        if out is None:
            return None, why
        v = parse_evals(out).get(tag)
        if v is None:
            return None, out.strip()[:300]
        return v, ""

    def plan(self, stmt):
        return self._one(lambda tag: plan_command(tag, self.crate, stmt))

    def eval(self, stmt, args, ret, rows):
        """the rows' results, batch by batch in the order given. a batch that runs out of
        time ends the evaluation; the batches before it are kept, with `partial` the
        number of rows left unevaluated (check_spec orders rows smallest first, so one
        input too large to evaluate in time, such as a recursion as deep as its
        argument, no longer costs the verdict on the small ones)."""
        results = []
        for i in range(0, max(len(rows), 1), tc.MAX_BATCH):
            v, why = self._one(lambda tag: eval_command(tag, self.crate, stmt, args, ret, rows[i:i + tc.MAX_BATCH]))
            if v is None or not v.get("ok"):
                if v is None and why == "timeout" and results:
                    return {"kind": results[0]["kind"], "rows": [r for v in results for r in v["rows"]],
                            "partial": len(rows) - i}, ""
                return None, why if v is None else v.get("detail", "")
            results.append(v)
        return {"kind": results[0]["kind"], "rows": [r for v in results for r in v["rows"]]}, ""

    def post(self, stmt, args, ret, row, outs):
        v, _ = self._one(lambda tag: post_command(tag, self.crate, stmt, args, ret, row, outs))
        return v["outs"] if v and v.get("ok") else None


def _bad(kind, row):
    o = row["outcome"]
    return o in ("violates", "fail") or (o == "div" and kind == "spec")


NOT_EVALUATED = "not evaluated:"


def _shown(T, value):
    """an encoded output as the statement would write it."""
    try:
        return tc.lean_literal(T, json.loads(value), short=True)
    except (tc.Unsupported, ValueError, KeyError, TypeError):
        return value


def _kernel_refutation(lean, stmt, kind, binders, insts, args, ret, row, res, unfold, unit):
    """(kernel, why): the refutation of a shrunk witness proved through lss_check_proof,
    by the first of these that passes (each a theorem of its own: a heartbeat or recursion
    limit is not an error `first` can catch): the evaluation as it is; the evaluation also
    unfolding the operations the call reaches; that once per platform bit width, with a
    64-bit edge witness written as the platform's constant; the stated value. the plain
    evaluation goes first because unfolding more can cost a refutation it proves (a
    nested loop runs out of rounds). when none passes, why says what each gave and what
    the evaluation left: a goal that still runs the loop needs more rounds than
    EVAL_ROUNDS (a sum that overflows only after 92,800 steps)."""
    lean.n += 1
    nm = f"lss_refute_{lean.n}"
    hb = _lss_config.proof_cfg()["aeneas_heartbeats"]
    whys, text, ops = [], "", None
    for label, kw in [("evaluation", {}), ("with the operations it reaches", {"ops": True}),
                      ("per platform width", {"ops": True, "split": True}), ("stated value", {"stated": True})]:
        if kw.get("ops"):
            ops = lean.ops(unit, unfold) if ops is None else ops  # asked only once the plain evaluation failed
            if not ops and not kw.get("split"):
                continue  # nothing past EVAL_DEFS: the same theorem as the plain evaluation
            kw = {**kw, "ops": ops}
        t = refutation_text(nm, stmt, binders, insts, args, ret, row, res["outcome"], res.get("value", ""),
                            unfold, div=kind == "dspec", **kw)
        out, why = lean.run(_lean.proof_check_call(t, nm, hb))
        verdict = (_lean.parse_proof_verdicts(out).get(nm) or {}) if out else {}
        if verdict.get("ok"):
            return True, ""
        whys.append(f"{label}: {why or verdict.get('detail') or 'no verdict'}"[:300])
        text = t if kw.get("split") else text
    # the goals each case's evaluation leaves (a ⦄div statement has two), closed by sorry
    closer = re.compile(r"^( +)all_goals \(first \| decide \| omega\)$", re.M)
    out, _ = lean.run(closer.sub(r"\1lss_log_goals\n\1all_goals sorry", text)) if closer.search(text) else (None, "")
    left = [g.get("text", "") for g in _lean_goals(out)]
    if any(re.search(r"\bloop\b", g) for g in left):
        whys.insert(0, f"the evaluation stops after {EVAL_ROUNDS} rounds with the loop still running")
    elif left:
        whys.insert(0, "the evaluation leaves: " + left[0][:300])
    return False, "; ".join(whys)


def _lean_goals(out):
    """the goals lss_log_goals reported (aeneas_layer.lean), as dicts."""
    goals = []
    for m in re.finditer(r"LSS_GOALS (\{[^\n]*\})", out or ""):
        try:
            goals.append(json.loads(m.group(1)))
        except json.JSONDecodeError:
            pass
    return goals


@events.layer("bounded")
def check_spec(checker, stmt, unit, project_dir, seed=0, helpers=""):
    """the bounded verdict for one candidate (see the module docstring).
    status: pass, refuted, vacuous, not_evaluated, timeout or skipped; warning:
    None, narrow or no_witness; a refutation carries the shrunk witness, whether
    the kernel checked it, and the feedback text a repair prompt uses. `helpers` (a
    Rust spec's own definitions) are defined before each command."""
    lean = _Lean(checker, project_dir, helpers) if helpers else _Lean(checker, project_dir)
    try:
        plan, why = lean.plan(stmt)
    except OSError as e:  # no translated crate at project_dir: nothing to run
        return {"status": "skipped", "detail": str(e)}
    if plan is None:
        return {"status": "timeout" if why == "timeout" else "skipped", "detail": why}
    if not plan.get("ok"):
        d = plan.get("detail", "")
        if d.startswith(NOT_EVALUATED):
            return {"status": "not_evaluated", "detail": d[len(NOT_EVALUATED):].strip()[:300]}
        return {"status": "skipped", "detail": d[:300]}
    try:
        args = [type_ir(f["ir"], top=True) for f in plan["free"]]
        # (array, its length's binder): the binder takes the array's length in every row
        free_names = [f.get("name") for f in plan["free"]]
        ties = [(j, free_names.index(f["ir"][2]["binder"])) for j, f in enumerate(plan["free"])
                if f["ir"][0] == "array" and isinstance(f["ir"][2], dict)]
    except tc.Unsupported as e:
        return {"status": "not_evaluated", "detail": f"a sampled binder's type: {e.reason}"}
    except ValueError:
        return {"status": "not_evaluated", "detail": "an array's length is a binder the check does not sample"}

    def tie(row):
        row = list(row)
        for j, k in ties:
            row[k] = len(row[j])
        return row
    try:
        ret = type_ir(plan["ret"])
    except tc.Unsupported:
        ret = None  # outcomes still evaluate; no values, perturbations or kernel refutation
    binders, insts = plan["binders"], plan.get("insts", [])
    # a postcondition Lean cannot decide (a statement about a backward function's every
    # input) still lets the call run: a failing call refutes the statement, which claims
    # success whatever the postcondition says; a succeeding one decides nothing
    decided = plan.get("post_decidable", True)
    # smallest first: a batch that runs out of time then holds the largest inputs only
    rows = sorted((tie(r) for r in sample_rows(args, seed=seed)), key=lambda r: sum(size(t, x) for t, x in zip(args, r)))
    ev, why = lean.eval(stmt, args, ret, rows)
    if ev is None:
        return {"status": "timeout" if why == "timeout" else "skipped", "detail": why}
    kind, outs = ev["kind"], ev["rows"]
    rows = rows[:len(outs)]  # the rows evaluated before the time ran out
    # the plan decided the postcondition, so a row whose value it cannot decide is an
    # error, never a row that neither fits nor fails (which would pass with no witness)
    outs = [{"outcome": "error", "detail": "the postcondition is not decided at this input"}
            if decided and r["outcome"] == "unknown" else r for r in outs]
    errors = [r for r in outs if r["outcome"] == "error"]
    if len(errors) == len(outs):
        return {"status": "skipped", "detail": errors[0].get("detail", "")[:300]}
    bad = [i for i, r in enumerate(outs) if _bad(kind, r)]
    if bad:
        row, res = rows[bad[0]], outs[bad[0]]
        for _ in range(SHRINK_ROUNDS):
            cands = [tie(c) for c in _interleave([[row[:j] + [x] + row[j + 1:] for x in shrink(t, row[j])]
                                                  for j, t in enumerate(args)])]
            cands = cands[:2 * tc.MAX_BATCH]
            if not cands:
                break
            sev, _ = lean.eval(stmt, args, ret, cands)
            hits = [k for k, r in enumerate(sev["rows"]) if _bad(kind, r)] if sev else []
            if not hits:
                break
            k = min(hits, key=lambda k: sum(size(t, x) for t, x in zip(args, cands[k])))
            row, res = cands[k], sev["rows"][k]
        kernel, kernel_why = False, "not attempted"
        if ret is not None or res["outcome"] != "violates":
            kernel, kernel_why = _kernel_refutation(lean, stmt, kind, binders, insts, args, ret, row, res,
                                                    unfold_names(project_dir, unit), unit)
        names = [f.get("name") or f"x{i}" for i, f in enumerate(plan["free"])]
        shown = ", ".join(f"{n} := {tc.lean_literal(t, v, short=True)}" for n, t, v in zip(names, args, row))
        types = [f"{b['name']} := {b['v']}" for b in binders if b.get("k") in ("type", "inst") and b.get("name")]
        at = f" at {', '.join(types)}" if types else ""
        got = (f"returned {_shown(ret, res['value'])}" if res["outcome"] == "violates" and ret is not None
               else "returned a value" if res["outcome"] == "violates"
               else f"gave {res['outcome']} {res.get('value', '')}".strip())
        return {"status": "refuted", "kernel": kernel, "kernel_why": kernel_why, "witness": row,
                "outcome": res["outcome"],
                "value": res.get("value", ""), "instantiation": ", ".join(types),
                "feedback": (f"On input ({shown}){at} the function {got}, and the statement is false there "
                             f"(checked by running the function{', and by a kernel proof' if kernel else ''})."
                             + (" `f args ⦃ … ⦄` says the call succeeds, so state as a hypothesis what the inputs "
                                "need for it to succeed. If this input is one the function is never meant to get (a "
                                "value whose fields break what its type is for, such as a table with no slots), state "
                                "the condition that excludes it, on the input's fields, as a hypothesis."
                                if res["outcome"] in ("fail", "div") else ""))}
    if ev.get("partial"):
        # no counterexample among the inputs evaluated, and the larger ones were never run:
        # neither a pass nor a vacuous spec (an unevaluated input could fail)
        return {"status": "timeout", "detail": f"{len(outs)} of {len(outs) + ev['partial']} inputs evaluated "
                                               "before the time ran out, smallest first; none refutes the statement"}
    if not decided:
        return {"status": "not_evaluated", "detail": f"postcondition: {plan.get('post_why', '')}"[:300]}
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
    # the smallest, a middle and the largest input that fit (rows run smallest first): a
    # spec that says nothing on small inputs only is not called vacuous
    probe = sorted({fit[k * (len(fit) - 1) // (PERTURB_ROWS - 1)] for k in range(PERTURB_ROWS)}) if fit else []
    for i in (probe if ret is not None else []):
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
