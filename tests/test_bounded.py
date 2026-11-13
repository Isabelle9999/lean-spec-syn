import json
import random
import re
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
    u32_rows = bounded.sample_rows([U32], seed=0)
    random_rows = u32_rows[len(dict.fromkeys(bounded.edge_values(U32))):]
    check("the first random rows' numbers are small and the sizes grow: most rows of a U32 stay under 10^6 "
          "(a loop it bounds finishes), every bit length is tried",
          all(r[0] <= 16 for r in random_rows[:3]) and sum(r[0] > 10 ** 6 for r in u32_rows) <= 6
          and len({r[0].bit_length() for r in u32_rows}) >= 20,
          str([r[0] for r in u32_rows]))
    rnd = random.Random(0)
    small = sum(bounded.random_int(U32, rnd, 1.0) <= 16 for _ in range(1000))
    check("half the random numbers are small, where indices, preconditions and loop bounds live, even at full size",
          450 <= small <= 700, f"{small} of 1000 at most 16")
    pairs = bounded.sample_rows([U32, U32], seed=0)
    check("two U32 bounds of a nested loop: most rows run under 10^6 steps",
          sum(a * b > 10 ** 6 for a, b in pairs) <= len(pairs) // 2, str(pairs))
    ranged = [("int", t) for t in ("Std.U8", "Std.I8", "Std.I16", "Std.Usize", "Std.I64", "Std.U128")]
    drawn = [v for sd in range(5) for r in bounded.sample_rows(ranged, seed=sd) for v in r]
    check("every drawn number is in its type's range, and signed ones take both signs",
          all(bounded._int_range(t)[0] <= v <= bounded._int_range(t)[1]
              for sd in range(5) for r in bounded.sample_rows(ranged, seed=sd) for t, v in zip(ranged, r))
          and any(v < -16 for v in drawn) and any(v > 16 for v in drawn))
    check("every sampled value renders as a Lean literal",
          all(tc.lean_literal(t, v) for r in rows for t, v in zip([U32, VEC], r)))
    check("the short literal of every sampled value names no proof",
          all("by " not in tc.lean_literal(t, v, short=True) for r in bounded.sample_rows([("int", "Std.Usize"), VEC, PAIR])
              for t, v in zip([("int", "Std.Usize"), VEC, PAIR], r)))
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
    sh = bounded.shrink(PAIR, {"first": 5, "second": 1 << 20})
    check("a struct shrinks one field at a time",
          sh[:2] == [{"first": 0, "second": 1 << 20}, {"first": 5, "second": 0}]
          and all((c["first"] != 5) + (c["second"] != 1 << 20) == 1 for c in sh), str(sh)[:300])


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
    sh = bounded.shrink(NODE, v)
    check("a tree shrinks to its subtrees", sh[:1] == [v["args"][2]], str(sh))
    check("an enum shrinks the arguments that are not subtrees",
          {"tag": "mk", "args": [0, None, v["args"][2]]} in sh[1:], str(sh))
    lst = {"tag": "Cons", "args": [7, {"tag": "Cons", "args": [300, {"tag": "Nil", "args": []}]}]}
    sh = bounded.shrink(LIST, lst)
    check("a crate list shrinks its elements as well as its tail",
          sh[0] == lst["args"][1] and {"tag": "Cons", "args": [7, {"tag": "Cons", "args": [0, {"tag": "Nil", "args": []}]}]}
          in sh and {"tag": "Cons", "args": [7, {"tag": "Nil", "args": []}]} in sh, str(sh))
    deep = {"tag": "mk", "args": [3_000_000_000, None, {"tag": "mk", "args": [7, None, None]}]}
    sh = bounded.shrink(("vec", NODE), [deep, deep])[:2 * tc.MAX_BATCH]
    check("a large field deep inside a list is shrunk within the candidates a round tries",
          [{"tag": "mk", "args": [0, None, deep["args"][2]]}, deep] in sh, str(sh)[:300])
    check("no shrink candidate equals the value it came from",
          all(_key(c) != _key(x) for T, x in [(NODE, v), (LIST, lst), (PAIR, {"first": 0, "second": 9}), (VEC, [0, 0])]
              for c in bounded.shrink(T, x)))
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


RANGE = ("struct", "Aeneas.Std.core.ops.range.Range", [("start", ("int", "Std.Usize")), ("end", ("int", "Std.Usize"))],
         "Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize")
ITER = ("struct", "Aeneas.Std.core.slice.iter.Iter", [("slice", ("slice", U32)), ("i", ("int", "Nat"))],
        "Aeneas.Std.core.slice.iter.Iter Aeneas.Std.U32")


def run_static_core_types():
    """Aeneas's models of Rust's types, the state loop functions take: a Range's
    fields are numbers (one of them named `end`), a slice iterator's position a Nat."""
    print("=== static: a Range, a slice iterator ===")

    def ir(j):
        try:
            return bounded.type_ir(j)
        except tc.Unsupported as e:
            return e.reason
    got = (ir(["struct", RANGE[1], [["start", ["int", "Std.Usize"]], ["end", ["int", "Std.Usize"]]], RANGE[3]]),
           ir(["int", "Nat"]))
    check("a Range reads as a structure, a Nat as a number", got == (RANGE, ("int", "Nat")), str(got))
    check("a type with no values (Aeneas's Infallible) is not sampled",
          ir(["enum", "Aeneas.Std.core.convert.Infallible", [], "core.convert.Infallible"])
          == "type core.convert.Infallible has no values")
    check("a structure's fields are written quoted, so Range's `end` (a keyword) reads",
          tc.lean_literal(RANGE, {"start": 1, "end": 3}) == "{ «start» := 1#usize, «end» := 3#usize }"
          and bounded.eval_literal(RANGE, {"start": 1, "end": 3}) == "{ «start» := 1#usize, «end» := 3#usize }",
          tc.lean_literal(RANGE, {"start": 1, "end": 3}))
    enc = tc.lean_encode_expr(RANGE, "v")
    check("and read back through quoted fields", "(v).«end»" in enc and "(v).«start»" in enc and '\\"end\\":' in enc, enc)
    check("a Nat is written as a Nat and read back with no `.val`",
          tc.lean_literal(("int", "Nat"), 5) == "(5 : Nat)" and tc.lean_literal(("int", "Nat"), 5, short=True) == "5"
          and tc.lean_encode_expr(("int", "Nat"), "v") == '("\\"" ++ toString (v) ++ "\\"")',
          tc.lean_encode_expr(("int", "Nat"), "v"))
    rows = bounded.sample_rows([ITER], n=24, seed=0)
    check("a slice iterator's inputs are a slice and a position from 0, every position kind tried",
          all(set(r[0]) == {"slice", "i"} and r[0]["i"] >= 0 for r in rows)
          and any(r[0]["i"] < len(r[0]["slice"]) for r in rows) and any(r[0]["i"] >= len(r[0]["slice"]) for r in rows),
          str(rows[:4]))
    step_by = ("struct", "Aeneas.Std.core.iter.adapters.step_by.StepBy", [("iter", RANGE), ("step_by", ("int", "Std.Usize"))],
               "core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)")
    first = bounded.sample_rows([step_by], n=48, seed=0)[:2]
    check("a structure's first inputs are its fields' edge values (0, then 1), not a full-size draw",
          first == [[{"iter": {"start": 0, "end": 0}, "step_by": 0}], [{"iter": {"start": 1, "end": 1}, "step_by": 1}]],
          str(first))
    lits = [tc.lean_literal(ITER, r[0]) for r in rows]
    check("each written with its fields quoted and its position a Nat",
          all(x.startswith("{ «slice» := ") and ", «i» := (" in x and x.endswith(" : Nat) }") for x in lits), lits[0])


def run_static_nested_text():
    """numbers inside a structure, an option or an array of arrays go to an evaluation
    as text too (SymCrypt's Key: matrices of 256-number arrays in its fields)."""
    print("=== static: number arrays at any depth as text ===")
    u8, u16 = ("int", "Std.U8"), ("int", "Std.U16")
    key = ("struct", "symcrust.mlkem.key.Key",
           [("seed", ("array", u8, 2)), ("m", ("array", ("array", u16, 2), 2)), ("t", ("option", ("slice", u8))),
            ("n", u8)], "symcrust.mlkem.key.Key")
    lit = bounded.eval_literal(key, {"seed": [1, 2], "m": [[3, 4], [5, 6]], "t": [7], "n": 9})
    check("a structure's number arrays, an array of arrays and an option's slice are text, its scalars literals",
          lit.count("lssArr") == 3 and lit.count("lssSlice") == 1 and "«n» := 9#u8" in lit
          and "#u16" not in lit and lit.startswith("{ «seed» := (lssArr"), lit)
    check("a kernel refutation still writes the literal", "lss" not in tc.lean_literal(key, {
        "seed": [1, 2], "m": [[3, 4], [5, 6]], "t": [7], "n": 9}))


def run_static_server():
    """a Lean server whose REPL was killed from outside while idle, or grew past half its
    memory cap, is restarted before it is used (lean_server.ReplWorker.ready)."""
    print("=== static: a REPL gone or too big ===")
    import lean_server

    class Proc:
        pid = 1

        def __init__(self, code):
            self.code = code

        def poll(self):
            return self.code
    w = lean_server.ReplWorker("/nowhere", mem_cap_bytes=1000)
    w._restart = lambda: setattr(w, "restarts", w.restarts + 1)
    real = lean_server._rss_anon_bytes
    try:
        lean_server._rss_anon_bytes = lambda pgid: 400
        w._proc = Proc(None)
        w.ready()
        check("a live REPL under half its cap is used as it is", w.restarts == 0)
        w._proc = Proc(143)
        w.ready(big=False)
        check("one killed while idle (SIGTERM, exit 143) is restarted before the next command", w.restarts == 1)
        size = [600]
        lean_server._rss_anon_bytes = lambda pgid: size[0]
        w._proc = Proc(None)
        w.ready(big=False)
        check("a command never restarts a live one, so its caller's env ids stay good", w.restarts == 1)
        s = object.__new__(lean_server.LeanServer)
        s._worker = w
        n = [s.restarts() for _ in range(4)]
        check("one past half its cap, its size since its caller built its envs, is not restarted (no rebuild loop)",
              n == [1, 1, 1, 1], str(n))
        size[0] = 900
        check("one past half its cap that has grown by a quarter of it is restarted where a caller reads the count",
              s.restarts() == 2, str(w.restarts))
        check("and its next reads measure the new one's size again", [s.restarts() for _ in range(3)] == [2, 2, 2],
              str(w.restarts))
    finally:
        lean_server._rss_anon_bytes = real


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
    u8, i16, usz = ("int", "Std.U8"), ("int", "Std.I16"), ("int", "Std.Usize")
    check("an evaluated array of numbers is text read in compiled code, its length as the type gives it",
          bounded.eval_literal(("array", u8, 3), [1, 2, 255]) == '(lssArr (⟨0⟩ : Std.U8) 3#usize (lssU .U8 "1 2 255"))',
          bounded.eval_literal(("array", u8, 3), [1, 2, 255]))
    check("a const generic array's length is its value's",
          bounded.eval_literal(("array", u8, None), [7, 8]) == '(lssArr (⟨0⟩ : Std.U8) 2#usize (lssU .U8 "7 8"))',
          bounded.eval_literal(("array", u8, None), [7, 8]))
    check("a vector of signed numbers keeps their signs; an empty slice is empty text",
          bounded.eval_literal(("vec", i16), [-5, 7, -32768]) == '(lssVec (lssI .I16 "-5 7 -32768"))'
          and bounded.eval_literal(("slice", usz), []) == '(lssSlice (lssU .Usize ""))',
          bounded.eval_literal(("vec", i16), [-5, 7, -32768]))
    check("a tuple's arrays are text too; an array of anything else is written as today",
          bounded.eval_literal(("tuple", [("array", u8, 1), U32]), [[4], 9]) == '((lssArr (⟨0⟩ : Std.U8) 1#usize '
          '(lssU .U8 "4")), 9#u32)' and bounded.eval_literal(("array", ("bool",), 1), [True])
          == tc.lean_literal(("array", ("bool",), 1), [True]),
          bounded.eval_literal(("tuple", [("array", u8, 1), U32]), [[4], 9]))
    arr = [("array", u8, 2)]
    cmd = bounded.eval_command("t1", "C", stmt, arr, U32, [[[1, 2]]])
    post = bounded.post_command("t2", "C", stmt, arr, arr[0], [[1, 2]], [[3, 4]])
    check("eval and post commands carry an array input, and a wrong array output, as text", cmd.endswith(
        'rows:[["(lssArr (⟨0⟩ : Std.U8) 2#usize (lssU .U8 \\"1 2\\"))"]]')
          and 'row:["(lssArr ' in post and 'outs:["(lssArr (⟨0⟩ : Std.U8) 2#usize (lssU .U8 \\"3 4\\"))"]' in post,
          cmd[-90:] + " " + post[-120:])
    ref = bounded.refutation_text("rf", "S", [{"k": "arg", "i": 0}], [], arr, U32, [[1, 2]], "fail",
                                  "Aeneas.Std.Error.panic", stated=True)
    check("a kernel refutation writes an array witness as a literal, never as text the kernel would have to "
          "parse", "(⟨[1#u8, 2#u8], by decide⟩ : Array Std.U8 2#usize)" in ref and "lssArr" not in ref, ref)
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
          "fun lss_x0 lss_x1 lss_x2 lss_x3 => Aeneas.Std.WP.spec_imp_exists (@h (Aeneas.Std.I32) (C.I32.Insts.Ord) "
          "(inferInstance) (by lss_law_tac [C.I32.Insts.Ord]) lss_x0 lss_x1 lss_x2 lss_x3)" in ref
          and "obtain ⟨y, hy, hp⟩ := lss_h (true) (5#u32) _ (by first | rfl | decide | simp_all | omega)" in ref, ref)
    check("refutation applies the statement to variables and only then to the witness, so the elaborator never "
          "reduces the triple at the witness (which evaluates the call in unary arithmetic)",
          "(@h " in ref and "#u32" not in ref.split("(@h ", 1)[1].split("\n", 1)[0], ref)
    stated = bounded.refutation_text("rf", "S", binders, ["C.I32.Insts.Ord"], [U32, ("bool",)], U32,
                                     [5, True], "violates", '"6"', stated=True)
    check("refutation computes the call's value without restating it, or, as a theorem of its own, states it for "
          "rfl or decide",
          "  revert y\n  (iterate " in ref and "hv" not in ref
          and "  have hv : (Aeneas.Std.Result.ok y : Aeneas.Std.Result _) = Aeneas.Std.Result.ok (6#u32) := "
          "hy.symm.trans (by first | rfl | decide)\n  cases hv\n" in stated and "iterate" not in stated, ref + stated)
    check("the evaluation is closed off from what follows it (iterate takes a tactic sequence)",
          ref.endswith("])))\n  all_goals (first | decide | omega)"), ref[-200:])
    check("refutation of a violated postcondition decides it",
          stated.endswith("  cases hv\n  revert hp\n  first | decide | simp | omega"), stated[-200:])
    tac = bounded.eval_tactic(["f", "f_loop", "f_loop.body"])
    check("the refutation unrolls loop one step at a time and never hands its equation to simp",
          "(try rw [Aeneas.Std.loop])" in tac and "simp [f, f_loop, f_loop.body, " in tac
          and all("Aeneas.Std.loop" not in part.split("]", 1)[0] for part in tac.split("simp [")[1:]), tac)
    check("the evaluation turns scalar operators into Aeneas's operations by lemmas typed at scalars, never by "
          "unfolding the operator classes (which would rewrite Nat arithmetic too)",
          "lss_eval_uadd" in tac and "lss_eval_urem" in tac and "Aeneas.Std.UScalar.tryMk" in tac
          and not any(c in tac for c in ("HAdd.hAdd", "HMod.hMod", "HDiv.hDiv")), tac)
    import callgraph
    text = "\n".join(f"line{i}" for i in range(1, 10))
    units = [{"name": n, "callees": c, "generic": False, "range": [i + 1, i + 1], "no_eqn": False}
             for i, (n, c) in enumerate([("C.f", ["C.f_loop"]), ("C.f_loop", ["C.f_loop.body"]),
                                         ("C.f_loop.body", ["C.g", "C.h"]), ("C.g", []), ("C.h", []), ("C.other", [])])]
    info = {"C.h": {"is_opaque": True}}
    g = callgraph.CallGraph(text, units, manifest_info=info)
    g.crate = "C"
    old_fp = callgraph.for_project
    callgraph.for_project = lambda p: g
    try:
        names = bounded.unfold_names("/p", "f_loop")
    finally:
        callgraph.for_project = old_fp
    check("the unfold list of a loop unit holds the unit, its callees and each loop's body, and nothing outside "
          "the call graph", names == ["C.f_loop", "C.f_loop.body", "C.g"], str(names))
    ref = bounded.refutation_text("rf", "S", [{"k": "arg", "i": 0}], [], [U32], U32, [0], "fail",
                                  "Aeneas.Std.Error.integerOverflow", stated=True)
    check("refutation of a failing call needs only the constructor clash",
          ref.endswith("  cases hv") and "Result.fail Aeneas.Std.Error.integerOverflow" in ref
          and "obtain ⟨y, hy, hp⟩ := lss_h (0#u32)\n" in ref, ref)
    ref = bounded.refutation_text("rf", "S", [{"k": "type", "v": "Aeneas.Std.U32"}], [], [], U32, [], "fail",
                                  "Aeneas.Std.Error.integerOverflow")
    check("a refutation with no witness applies the statement directly",
          "obtain ⟨y, hy, hp⟩ := Aeneas.Std.WP.spec_imp_exists (@h (Aeneas.Std.U32))" in ref and "lss_h" not in ref, ref)
    usz, isz = ("int", "Std.Usize"), ("int", "Std.Isize")
    check("the kernel literal of a Usize or Isize that fits in 32 bits is n#usize / n#isize, whose bound decide "
          "proves on any platform",
          [tc.lean_literal(usz, v) for v in (0, 2 ** 32 - 1)] == ["0#usize", "4294967295#usize"]
          and [tc.lean_literal(isz, v) for v in (-2 ** 31, 2 ** 31 - 1)] == ["(-2147483648)#isize", "2147483647#isize"],
          str([tc.lean_literal(usz, 0), tc.lean_literal(isz, -2 ** 31)]))
    check("a wider Usize or Isize keeps the platform bound",
          tc.lean_literal(usz, 2 ** 32).startswith("(Usize.ofNatCore 4294967296 ")
          and tc.lean_literal(isz, -2 ** 31 - 1).startswith("(Isize.ofIntCore (-2147483649) "),
          tc.lean_literal(usz, 2 ** 32))


def _raises(fn):
    try:
        fn()
    except Exception:
        return True
    return False


def _plan(free=None, ret=None, binders=None, insts=None):
    free = free if free is not None else [{"name": "x", "type": "Aeneas.Std.U32", "ir": ["int", "Std.U32"]}]
    return {"ok": True, "kind": "spec", "free": free, "ret": ret or ["int", "Std.U32"],
            "binders": binders or [{"k": "arg", "i": 0}], "insts": insts or []}


class FakeLean:
    """bounded._Lean with scripted answers: `row_outcome(row)` gives one row's
    result, `post_outcome(row, out)` one perturbed output's, `plan` the plan."""
    calls = []

    def __init__(self, row_outcome, post_outcome=None, kernel=True, timeout=False, plan=None, ops=(), goals=()):
        self.row_outcome, self.post_outcome, self.kernel, self.timeout = row_outcome, post_outcome, kernel, timeout
        self.plan_ = plan or _plan()
        self.n = 0
        self.sent = []
        self.ops_, self.goals = list(ops), list(goals)

    def __call__(self, checker, project_dir):
        return self

    def plan(self, stmt):
        return (None, "timeout") if self.timeout == "plan" else (self.plan_, "")

    def eval(self, stmt, args, ret, rows, alone=True):
        if self.timeout:
            return None, "timeout"
        return {"kind": "dspec" if "div" in stmt else "spec", "rows": [self.row_outcome(r) for r in rows]}, ""

    def post(self, stmt, args, ret, row, outs):
        return [self.post_outcome(row, o) for o in outs] if self.post_outcome else None

    def ops(self, unit, unfold):
        return self.ops_

    def run(self, text):
        self.sent.append(text)
        if " name:" not in text:  # the goals the last evaluation left (lss_log_goals)
            return "\n".join(f"LSS_GOALS {json.dumps({'head': 'Not', 'text': g})}" for g in self.goals), ""
        name = text.split(" name:")[1].split()[0]
        ok = self.kernel(text) if callable(self.kernel) else self.kernel
        return f'LSS_PROOF {{"name":"{name}","ok":{"true" if ok else "false"},"stage":"ok","detail":"no","axioms":[]}}', ""


def _check(fake, stmt="S"):
    old_lean = bounded._Lean
    bounded._Lean = fake  # type: ignore[assignment]
    try:
        return bounded.check_spec(None, stmt, "f", "/p")
    finally:
        bounded._Lean = old_lean


def _ok(v):
    return {"outcome": "holds", "value": json.dumps(str(v))}


class NoCodeLean(FakeLean):
    """an evaluation Lean refuses to compile: the function calls an axiom."""
    def eval(self, stmt, args, ret, rows, alone=True):
        return None, ("<input>:3:0: error: failed to compile definition, consider marking it as 'noncomputable' "
                      "because it depends on 'symcrust.common.wipe', which is 'noncomputable'")


def run_static_check():
    print("=== static: the verdict ===")
    v = _check(NoCodeLean(lambda r: _ok(r[0])))
    check("a function with no code (it calls an axiom, a hardware model) is not evaluated, labelled so",
          v["status"] == "not_evaluated" and v["detail"].startswith("cannot run: symcrust.common.wipe has no code"),
          str(v))
    lcnf = bounded._no_code("error: Failed to find LCNF signature for symcrust.mlkem.ntt.sample_loop")
    check("and so is one whose loop was never compiled (Lean's other message for it)",
          (lcnf or {}).get("detail", "").startswith("cannot run: symcrust.mlkem.ntt.sample_loop has no code"), str(lcnf))
    # f x = x, spec "r.val < 5": false from 5 on; the witness shrinks to 5
    fake = FakeLean(lambda r: _ok(r[0]) if int(r[0]) < 5 else {"outcome": "violates", "value": json.dumps(str(r[0]))})
    v = _check(fake)
    check("a false spec is refuted", v["status"] == "refuted", str(v))
    check("the witness shrinks to the smallest failing input", v.get("witness") == [5], str(v.get("witness")))
    check("the refutation is kernel-checked when lss_check_proof accepts it",
          v.get("kernel") is True and "5#u32" in fake.sent[-1], fake.sent[-1][-200:] if fake.sent else "")
    check("the feedback names the input by its binder and the output as a literal",
          "(x := 5#u32)" in v.get("feedback", "") and "returned 5#u32" in v.get("feedback", ""), v.get("feedback"))
    usize = _plan(free=[{"name": "n", "type": "Aeneas.Std.Usize", "ir": ["int", "Std.Usize"]},
                        {"name": "v", "type": "alloc.vec.Vec Aeneas.Std.U32", "ir": ["vec", ["int", "Std.U32"]]}])
    fake = FakeLean(lambda r: {"outcome": "violates", "value": '"1"'} if r[0] == 3 and r[1] == [2]
                    else _ok(1), plan=usize)
    old_rows = bounded.sample_rows
    bounded.sample_rows = lambda args, seed=0: [[3, [2]]]
    try:
        v = _check(fake)
    finally:
        bounded.sample_rows = old_rows
    check("feedback writes a Usize as n#usize, never Usize.ofNatCore",
          "n := 3#usize" in v.get("feedback", "") and "ofNatCore" not in v.get("feedback", ""), v.get("feedback"))
    check("feedback writes a Vec as a list literal", "v := [2#u32]" in v.get("feedback", ""), v.get("feedback"))
    check("the kernel refutation writes a Usize that fits in 32 bits as n#usize, a literal the kernel accepts",
          bool(fake.sent) and "(3#usize)" in fake.sent[-1] and "native_decide" not in fake.sent[-1].split("lss_h ")[-1],
          fake.sent[-1][-300:] if fake.sent else "")
    gen = _plan(binders=[{"k": "type", "v": "Aeneas.Std.U32", "name": "T"}, {"k": "arg", "i": 0}])
    v = _check(FakeLean(lambda r: {"outcome": "violates", "value": '"1"'}, plan=gen))
    check("a generic spec's refutation says at which instantiation",
          v["status"] == "refuted" and "at T := Aeneas.Std.U32" in v["feedback"]
          and v["instantiation"] == "T := Aeneas.Std.U32", str(v))
    v = _check(FakeLean(lambda r: {"outcome": "violates", "value": '"1"'}, kernel=False))
    check("a refutation the kernel does not check is evaluation-only", v["status"] == "refuted" and v["kernel"] is False)
    check("and the verdict keeps why the kernel did not check it, for each way it tried",
          "evaluation: " in v.get("kernel_why", "") and "stated value: " in v.get("kernel_why", ""), str(v))
    fake = FakeLean(lambda r: {"outcome": "violates", "value": '"1"'}, kernel=lambda text: "have hv" in text)
    v = _check(fake)
    check("when no evaluation is kernel-checked, the stated value is tried in a theorem of its own",
          v["kernel"] is True and len(fake.sent) == 3 and "revert y" in fake.sent[0] and "have hv" in fake.sent[-1]
          and not any("have hv" in t for t in fake.sent[:-1]), str(fake.sent)[:300])
    op = "Aeneas.Std.Slice.index_usize"
    fake = FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.arrayOutOfBounds"}, ops=[op],
                    kernel=lambda text: op in text)
    v = _check(fake)
    check("when the plain evaluation is not kernel-checked, the evaluation also unfolding the operations the call "
          "reaches is tried next, in a theorem of its own",
          v["kernel"] is True and len(fake.sent) == 2 and op not in fake.sent[0] and "lss_hb" not in fake.sent[1]
          and f", {op}" in fake.sent[1].split("simp [", 1)[1].split("]", 1)[0], str(fake.sent)[:300])
    usize1 = _plan(free=[{"name": "n", "type": "Aeneas.Std.Usize", "ir": ["int", "Std.Usize"]}])
    fake = FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"} if r[0] == 2 ** 64 - 1
                    else _ok(1), plan=usize1,
                    ops=[op], kernel=lambda text: "with lss_hb | lss_hb" in text)
    old_rows = bounded.sample_rows
    bounded.sample_rows = lambda args, seed=0: [[2 ** 64 - 1]]
    try:
        v = _check(fake)
    finally:
        bounded.sample_rows = old_rows
    split = fake.sent[-1].replace("\\n", "\n") if fake.sent else ""  # the proof text, as lss_check_proof reads it
    check("then once per platform bit width, the 64-bit edge witness written as the platform's own constant",
          v["kernel"] is True and len(fake.sent) == 3
          and "  revert y\n  rcases System.Platform.numBits_eq with lss_hb | lss_hb\n  all_goals (iterate " in split
          and "simp [lss_hb, " in split and "Aeneas.Std.Usize.numBits" in split
          and "lss_h (Aeneas.Std.core.num.Usize.MAX)" in split and "18446744073709551615" not in split
          and "18446744073709551615" in fake.sent[0], split[-400:])
    fake = FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"})
    v = _check(fake, stmt="S div")
    ref = fake.sent[0].replace("\\n", "\n") if fake.sent else ""
    check("a ⦄div statement is refuted through its two cases, a returned value or divergence, each evaluated",
          v["status"] == "refuted" and v["kernel"] is True and "lss_dspec_cases (@h " in ref
          and " with ⟨y, hy, hp⟩ | hd\n  · revert y\n    (iterate " in ref and "\n  · revert hd\n    (iterate " in ref
          and ref.count("all_goals (first | decide | omega)") == 2, ref[-500:])
    fake = FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"}, kernel=False,
                    goals=["∀ (y : U32), ¬loop (fun x => ok (done x)) (16#u32, 9#u32) = ok y"])
    v = _check(fake)
    check("a refutation no attempt proves says the evaluation ran out of rounds when the loop is still running",
          v["kernel"] is False and v.get("kernel_why", "").startswith(
              f"the evaluation stops after {bounded.EVAL_ROUNDS} rounds with the loop still running")
          and "lss_log_goals" in fake.sent[-1] and "lss_hb" in fake.sent[-1], v.get("kernel_why", "")[:300])
    fake = FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"}, kernel=False)
    _check(fake, stmt="S div")
    log = fake.sent[-1] if fake.sent else ""
    check("for a ⦄div statement the goals both cases leave are logged, each case closed by sorry",
          log.count("lss_log_goals") == 2 and log.count("all_goals sorry") == 2
          and "decide | omega)" not in log and "\n    lss_log_goals\n    all_goals sorry" in log, log[-400:])
    class Partial(FakeLean):
        """the first `k` rows evaluate, the rest run out of time"""
        def __init__(self, row_outcome, k, **kw):
            super().__init__(row_outcome, **kw)
            self.k, self.rows_seen = k, []

        def eval(self, stmt, args, ret, rows, alone=True):
            self.rows_seen.append(rows)
            got, _ = super().eval(stmt, args, ret, rows)
            if len(self.rows_seen) == 1:
                return {**got, "rows": got["rows"][:self.k], "partial": len(rows) - self.k}, ""
            return got, ""
    fake = Partial(lambda r: {"outcome": "violates", "value": '"1"'} if r[0] == 3 else _ok(r[0]), k=8)
    old_rows = bounded.sample_rows
    bounded.sample_rows = lambda args, seed=0: [[2 ** 31], [9], [3], [2 ** 32 - 1], [0]] + [[n] for n in range(10, 30)]
    try:
        v = _check(fake)
    finally:
        bounded.sample_rows = old_rows
    first = fake.rows_seen[0] if fake.rows_seen else []
    check("inputs are evaluated smallest first, so the largest are the ones a timeout leaves out",
          [r[0] for r in first[:5]] == [0, 3, 9, 10, 11] and first[-2:] == [[2 ** 31], [2 ** 32 - 1]], str(first))
    check("a counterexample among the inputs evaluated before the time ran out still refutes the statement",
          v["status"] == "refuted" and v.get("witness") == [3], str(v)[:300])
    fake = Partial(lambda r: _ok(r[0]), k=8)
    v = _check(fake)
    check("with none among them, a check that ran out of time is a timeout that says how far it got, "
          "never a pass or a vacuous spec",
          v["status"] == "timeout" and "of " in v.get("detail", "") and "none refutes" in v.get("detail", ""), str(v))
    gen_arr = _plan(free=[{"name": "N", "type": "Aeneas.Std.Usize", "ir": ["int", "Std.Usize"]},
                          {"name": "a", "type": "Aeneas.Std.Array Aeneas.Std.U32 N",
                           "ir": ["array", ["int", "Std.U32"], {"binder": "N"}]}],
                    binders=[{"k": "arg", "i": 0}, {"k": "arg", "i": 1}])
    seen_rows = []
    fake = FakeLean(lambda r: (seen_rows.append(r), {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"}
                               if len(r[1]) == 2 else _ok(0))[1], plan=gen_arr)
    v = _check(fake)
    ref = fake.sent[0].replace("\\n", "\n") if fake.sent else ""
    check("an array whose length is a const generic is drawn with that length binder set to its length, in every row "
          "and every shrink candidate",
          bool(seen_rows) and all(r[0] == len(r[1]) for r in seen_rows) and v["status"] == "refuted"
          and len(v["witness"][1]) == 2 and v["witness"][0] == 2
          and "lss_h (2#usize) ((⟨[" in ref and "] , by decide⟩" not in ref and ": Array Std.U32 2#usize)" in ref,
          f"{[r for r in seen_rows if r[0] != len(r[1])][:3]} {v.get('witness')} {ref[-300:]}")
    check("such a length is read only for an array binder of the statement, not one inside another type",
          bounded.type_ir(["array", ["int", "Std.U32"], {"binder": "N"}], top=True) == ("array", ("int", "Std.U32"), None)
          and _raises(lambda: bounded.type_ir(["tuple", [["array", ["int", "Std.U32"], {"binder": "N"}]]], top=True)))
    bl = open(bounded._BOUNDED_PATH, encoding="utf-8").read()
    tir = bl[bl.index("partial def lssTypeIR"):bl.index("lssTypeIR crate stack ty'") + 30]
    check("the type reader names a const generic length's binder, never evaluates it, and reads a crate's type alias "
          "as what it stands for",
          'args[1]!.isFVar' in tir and '("binder", Json.str' in tir and "unfoldDefinition? ty" in tir
          and tir.index("args[1]!.isFVar") < tir.index("lssEvalString"), tir[:300])
    G = bounded.EVAL_GROUP
    ok = lambda k: ({"ok": True, "kind": "spec", "rows": [{"outcome": "holds"}] * k}, "")  # noqa: E731
    for why in ("timeout", "memory"):
        lb = bounded._Lean.__new__(bounded._Lean)
        lb.crate, answers, sent = "C", [ok(G), (None, why), ok(1), ok(1), (None, why)], []
        lb._one = lambda make, timeout=None: (sent.append((make("t"), timeout)), answers.pop(0))[1]
        got, _ = lb.eval("S", [U32], U32, [[n] for n in range(3 * G)])
        check(f"inputs go {G} to a command, each with {bounded.EVAL_GROUP_TIMEOUT}s; a group that runs out of "
              f"{'time' if why == 'timeout' else 'memory'} goes again one input to a command, up to the first that "
              "runs out: the inputs before it are kept, it and the larger ones get no result",
              got is not None and len(got["rows"]) == G + 2 and got["partial"] == 2 * G - 2 and got["why"] == why
              and [t for _, t in sent] == [bounded.EVAL_GROUP_TIMEOUT] * 5
              and sent[0][0].count("#u32") == G and [c.count("#u32") for c, _ in sent[2:]] == [1, 1, 1]
              and f'"{G}#u32"' in sent[1][0] and f'"{G + 2}#u32"' in sent[4][0],
              f"{got} {[(c[-60:], t) for c, t in sent]}")
    lb = bounded._Lean.__new__(bounded._Lean)
    lb.crate, answers = "C", [(None, "timeout")] + [ok(1)] * G + [ok(G)]
    lb._one = lambda make, timeout=None: answers.pop(0)
    got, _ = lb.eval("S", [U32], U32, [[n] for n in range(2 * G)])
    check("a group that runs out only as a whole, every input finishing alone, is kept and the evaluation goes on",
          got is not None and len(got["rows"]) == 2 * G and "partial" not in got and not answers, str(got)[:200])
    lb = bounded._Lean.__new__(bounded._Lean)
    lb.crate, answers = "C", [ok(G), (None, "timeout"), ok(1)]
    lb._one = lambda make, timeout=None: answers.pop(0)
    got, _ = lb.eval("S", [U32], U32, [[n] for n in range(3 * G)], alone=False)
    check("shrinking's evaluation ends at a group that runs out, trying none of its inputs alone",
          got is not None and len(got["rows"]) == G and got["partial"] == 2 * G and answers == [ok(1)], str(got)[:200])
    lb = bounded._Lean.__new__(bounded._Lean)
    lb.crate, answers = "C", [ok(G), (None, "timeout"), ok(1)]
    lb._one = lambda make, timeout=None: answers.pop(0)
    got, _ = lb.eval("S", [U32], U32, [[n] for n in range(G + 1)])
    check("a group of one input that runs out is not run alone again: it already was",
          got is not None and len(got["rows"]) == G and got["partial"] == 1 and answers == [ok(1)], str(got)[:200])
    lb = bounded._Lean.__new__(bounded._Lean)
    lb.crate = "C"
    lb._one = lambda make, timeout=None: (None, "timeout")
    got, _ = lb.eval("S", [U32], U32, [[n] for n in range(G)])
    check("an input that never ends among the smallest is still a result: every input from it on left without one",
          got == {"kind": None, "rows": [], "partial": G, "why": "timeout"}, str(got))

    class Alone(FakeLean):
        seen = []

        def eval(self, stmt, args, ret, rows, alone=True):
            self.seen.append(alone)
            return super().eval(stmt, args, ret, rows, alone)
    fake = Alone(lambda r: {"outcome": "violates", "value": '"1"'} if r[0] >= 3 else _ok(r[0]))
    v = _check(fake)
    check("the sampled inputs are tried alone after a group runs out; shrink candidates are not",
          v["status"] == "refuted" and fake.seen[0] is True and len(fake.seen) > 1 and not any(fake.seen[1:]),
          f"{v['status']} {fake.seen}")
    class NoneFinish(FakeLean):
        def eval(self, stmt, args, ret, rows, alone=True):
            return {"kind": None, "rows": [], "partial": len(rows), "why": "timeout"}, ""
    v = _check(NoneFinish(lambda r: _ok(r[0])))
    check("when no input finishes the check is a timeout naming the one that ran past the limit",
          v["status"] == "timeout" and "0 of " in v["detail"] and "(x := 0#u32) ran past" in v["detail"]
          and v.get("unevaluated", 0) > 0, str(v))
    lb = bounded._Lean.__new__(bounded._Lean)
    lb.project_dir, lb.crate, runs = "/p-ops", "C", []
    lb.run = lambda text: (runs.append(text) or ('x:1:0: warning: LSS_OPS ["Aeneas.Std.Slice.index_usize",'
                                                 '"Aeneas.Std.UScalar.add"]', ""))
    got = [lb.ops("C.f", ["C.f", "C.g"]), lb.ops("C.f", ["C.f", "C.g"])]
    check("the operations a call reaches come from lss_eval_ops, past EVAL_DEFS, asked once per unit",
          got == [[op], [op]] and runs == ["lss_eval_ops C C.f C.g"], f"{got} {runs}")
    bl = open(bounded._BOUNDED_PATH, encoding="utf-8").read()
    body = bl[bl.index('elab "lss_eval_ops "'):]
    check("lss_eval_ops never names how a scalar is stored, a type, an instance, a matcher or loop",
          all(x in body for x in ['"val", "bv", "ofNatCore", "ofIntCore", "numBits"', "``Aeneas.Std.loop",
                                  "getForallBody.isSort", 'startsWith "match_"', 'startsWith "inst"', "isInternal",
                                  "d.safety == .safe"]),
          body[:300])
    fake = FakeLean(lambda r: {"outcome": "violates", "value": '"1"'})
    v = _check(fake)
    check("a refutation the evaluation proves is not tried again", v["kernel"] is True and len(fake.sent) == 1,
          str(len(fake.sent)))
    v = _check(FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.integerOverflow"}))
    check("a spec whose call fails is refuted", v["status"] == "refuted" and v["outcome"] == "fail", str(v))
    check("its feedback says the triple claims success and asks for the precondition that gives it",
          "says the call succeeds, so state as a hypothesis" in v.get("feedback", ""), v.get("feedback"))
    check("a failing call's feedback asks for the hypothesis that excludes an invalid input",
          "never meant to get" in v.get("feedback", "") and "on the input's fields, as a hypothesis" in v.get("feedback", ""),
          v.get("feedback"))
    undecided = {**_plan(), "post_decidable": False, "post_why": "not Decidable: ∀ t, P t"}
    v = _check(FakeLean(lambda r: {"outcome": "fail", "value": "Aeneas.Std.Error.panic"} if int(r[0]) == 0
                        else {"outcome": "unknown", "value": ""}, plan=undecided))
    check("with an undecided postcondition, a failing call still refutes the statement",
          v["status"] == "refuted" and v["outcome"] == "fail" and v["witness"] == [0], str(v))
    v = _check(FakeLean(lambda r: {"outcome": "unknown", "value": ""}, post_outcome=lambda row, o: "holds",
                        plan=undecided))
    check("an undecided postcondition never passes and is never called vacuous",
          v["status"] == "not_evaluated" and "not Decidable" in v["detail"], str(v))
    v = _check(FakeLean(lambda r: {"outcome": "unknown", "value": ""}))
    check("a postcondition the plan decided but no row can is an error, never a pass", v["status"] == "skipped", str(v))
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
    v = _check(FakeLean(same, lambda row, o: "holds" if int(row[0]) <= 5 else "violates"))
    check("a spec that says nothing on small inputs only is not vacuous: the largest input is probed too",
          v["status"] == "pass", str(v))
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
        sent, roles, n_restarts = [], [], 0

        def check(self, code, timeout=None, env=None):
            self.sent.append((code, env))

            class R:
                timed_out = False
                stdout, stderr = 'LSS_EVAL {"tag":"derive","ok":true,"derived":["C.T"],"via_beq":[],"none":[]}', ""
                new_env = 70 if code == "CRATE TEXT" else 77
            return R()

        def restarts(self):
            return self.n_restarts

        def stats(self):
            return {"restarts": self.n_restarts}

    class Checker:
        lean_calls = 0
        state = {"ok": True, "env": 42, "env0": 41, "crate": "C"}

        def _aeneas_env_for(self, project_dir):
            return self.state

        def _aeneas_env_text(self, project_dir):
            return "CRATE TEXT", ""

    server = Server()
    old = bounded._lean_server.get_server

    def fake_get_server(*a, **k):
        server.roles.append(k.get("role", "main"))
        return server
    bounded._lean_server.get_server = fake_get_server  # type: ignore[assignment]
    bounded._EVAL_ENVS.clear()
    try:
        ck = Checker()
        lean_ = bounded._Lean(ck, "/p")
        lean_.run("lss_eval_spec x")
        lean_.run("lss_eval_spec y")
        bounded._Lean(ck, "/p").run("lss_eval_spec z")
        ck.state = {"ok": True, "env": 52, "env0": 51, "crate": "C"}  # the main server's crate env was rebuilt
        bounded._Lean(ck, "/p").run("lss_eval_spec v")
        server.n_restarts = 1  # the evaluation server restarted
        bounded._Lean(ck, "/p").run("lss_eval_spec w")
        n_before = len(server.sent)
        server2 = Server()
        server2.sent, server2.n_restarts = [], 1  # the same restart count as the old one
        bounded._lean_server.get_server = lambda *a, **k: server2  # type: ignore[assignment]
        bounded._Lean(ck, "/p").run("lss_eval_spec u")  # a new server (shutdown_all), its restart count 0 again
    finally:
        bounded._lean_server.get_server = old
    check("every command of the check goes to the evaluation server, none to the main one",
          server.roles and set(server.roles) == {"eval"}, str(server.roles))
    code, env = server.sent[1]
    check("the check's env is built in the evaluation server on the crate env, from the main server's text, as "
          "built before the crate is opened", server.sent[0] == ("CRATE TEXT", None) and env == 70,
          str([(c[:30], e) for c, e in server.sent[:2]]))
    check("it holds the gate's Decidable instances, then bounded.lean, then DecidableEq for the crate's types",
          code.index("lssSubtypeDecEq") < code.index("deriving instance DecidableEq for Aeneas.Std.Result")
          < code.index("elab \"lss_eval_plan ") < code.index("lss_derive_deceq crate:C"), code[-200:])
    check("it is built once per evaluation server start, every command then runs in it, inside the crate's "
          "namespace, whatever happens to the main server's envs",
          [e for _, e in server.sent[2:6]] == [77, 77, 77, 77] and server.sent[2][0] == "namespace C\nlss_eval_spec x",
          str([(c[:30], e) for c, e in server.sent]))
    check("a restarted evaluation server gets its crate env and check env built again",
          [(c[:10], e) for c, e in server.sent[6:]] == [("CRATE TEXT", None), (code[:10], 70), ("namespace ", 77)],
          str([(c[:30], e) for c, e in server.sent[6:]]))
    check("a new evaluation server (after shutdown_all) builds its own envs, never reusing another process's ids",
          len(server.sent) == n_before and [c[:10] for c, _ in server2.sent] == ["CRATE TEXT", code[:10], "namespace "],
          str([(c[:30], e) for c, e in server2.sent]))
    check("what was derived is kept with the crate env", ck.state.get("check_derive", {}).get("derived") == ["C.T"],
          str(ck.state.get("check_derive")))

    class Broken(Server):
        def check(self, code, timeout=None, env=None):
            class R:
                timed_out = False
                stdout, stderr = ("", "") if code == "CRATE TEXT" else (":778:30: error: unexpected token ':='; "
                                                                        "expected '}'", "")
                new_env = 78
            return R()
    bounded._lean_server.get_server = lambda *a, **k: Broken()  # type: ignore[assignment]
    bounded._EVAL_ENVS.clear()
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
    bounded._EVAL_ENVS.clear()
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
    old_gate, old_b, old_emit = synth._gate.check_candidate, synth._bounded.check_spec, synth.events.emit
    synth._gate.check_candidate = lambda *a, **k: [{"check": c, "ok": True, "detail": ""} for c in gate.checks_for("rust-aeneas")]
    synth._bounded.check_spec = lambda checker, stmt, unit, project_dir, **k: dict(verdicts[stmt])
    emitted = []
    synth.events.emit = lambda kind, **f: emitted.append((kind, f))
    try:
        checker, llm = Checker(), LLM()
        specs = [{"name": "s", "stmt": "S"}, {"name": "v", "stmt": "V"}]
        synth.validate(specs, "def f (x : U32) : Result U32 := ok x", [], checker, llm=llm, func_name="f",
                       project_dir="/p", source="rust-aeneas")
    finally:
        synth._gate.check_candidate, synth._bounded.check_spec, synth.events.emit = old_gate, old_b, old_emit
    vs = [f for k, f in emitted if k == "verdict"]
    check("every verdict event carries the statement it was decided on, proved ones too",
          {(f["status"], f.get("stmt")) for f in vs} == {("refuted", "S"), ("rejected", "V"), ("proved", "FIXED")},
          str(vs))
    ref = next((f for f in vs if f["status"] == "refuted"), {})
    check("a refutation's event carries its witness, outcome and the feedback the repair got",
          ref.get("witness") == [5] and ref.get("outcome") == "violates" and "On input (5#u32)" in ref.get("feedback", ""),
          str(ref))
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


def run_static_preamble():
    print("=== static: the LLM's helper definitions ===")
    import synth
    seen = []

    class Checker:
        def typecheck(self, code, project_dir=None):
            seen.append(code)
            return True, []
    old_gate = synth._gate.check_candidate
    synth._gate.check_candidate = lambda *a, **k: (_ for _ in ()).throw(StopIteration)
    try:
        synth.validate([{"name": "s", "stmt": "S", "preamble": "def helper (x : U32) : Prop := ext x = x"}],
                       "import Mathlib\n", [], Checker(), func_name="f", project_dir="/p", source=None)
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("helper definitions sit in their own noncomputable section, closed after them",
          bool(seen) and seen[0].endswith("noncomputable section\ndef helper (x : U32) : Prop := ext x = x\nend"),
          str(seen)[-200:])

    pre = ("def toList {T : Type} : C.List T → _root_.List T\n  | .Cons x tl => x :: toList tl\n  | .Nil => []\n\n"
           "theorem other : True := trivial\n")
    stmt = "∀ {T : Type} (l : C.List T), f l ⦃ r => r = (toList l).length ⦄"
    helpers, renamed = synth.rust_helpers(pre, stmt)
    name = re.search(r"def (lss_hp_toList_[0-9a-f]{8}) ", helpers)
    check("a Rust helper is renamed by its text's hash, in the helper and in the statement",
          bool(name) and helpers.startswith("@[simp] def ") and f":: {name.group(1)} tl" in helpers
          and f"({name.group(1)} l)" in renamed and "toList l" not in renamed.replace(name.group(1), ""), helpers + renamed)
    check("two specs with the same helper share one name", synth.rust_helpers(pre, "x")[0] == helpers)
    copied, st = synth.rust_helpers(helpers + "\n\nabbrev twice (n : Nat) : Nat := 2 * n\n",
                                    f"f l ⦃ r => twice ({name.group(1) if name else 'x'} l).length = r ⦄")
    check("a helper copied from a callee's spec keeps its name, and an abbrev is a helper too",
          bool(name) and copied.startswith(helpers) and "@[simp] def lss_hp_twice_" in copied
          and st.startswith("f l ⦃ r => lss_hp_twice_"), copied + st)
    check("a Rust spec keeps only the helper definitions, @[simp] and outside any noncomputable section",
          "theorem other" not in helpers and "noncomputable" not in helpers, helpers)
    seen.clear()
    got = {}
    Checker.ensure_helpers = lambda self, project_dir, text: (seen.append(text), (True, []))[1]  # type: ignore[attr-defined]
    synth._gate.check_candidate = lambda checker, text, func, eff, *a, **k: got.setdefault("eff", eff) and (
        _ for _ in ()).throw(StopIteration)
    try:
        spec = {"name": "s", "stmt": stmt, "preamble": pre}
        synth.validate([spec], "import Aeneas\nimport C.Code.Funs\n", [], Checker(), func_name="f",
                       project_dir="/p", source="rust-aeneas")
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("a Rust helper is defined in the crate's env, never checked against the crate's imports",
          seen == [helpers], str(seen)[-300:])
    check("a Rust spec carries its helpers and the renamed statement",
          spec.get("helpers") == helpers and spec["stmt"] == renamed, str(spec))

    class Reuse(Checker):
        def known_helpers(self, project_dir, text):
            return helpers if name and name.group(1) in text else ""
    synth._gate.check_candidate = lambda *a, **k: (_ for _ in ()).throw(StopIteration)
    try:
        spec = {"name": "s", "stmt": renamed}
        synth.validate([spec], "import Aeneas\n", [], Reuse(), func_name="f", project_dir="/p", source="rust-aeneas")
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("a Rust spec that reuses a callee's helper, with no preamble, carries that helper",
          spec.get("helpers") == helpers, str(spec))

    class Bad(Checker):
        def ensure_helpers(self, project_dir, text):
            return False, ["error: unknown identifier"]
    synth._gate.check_candidate = lambda *a, **k: (_ for _ in ()).throw(StopIteration)
    try:
        spec = {"name": "s", "stmt": stmt, "preamble": pre}
        synth.validate([spec], "import Aeneas\n", [], Bad(), func_name="f", project_dir="/p", source="rust-aeneas")
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("a helper that does not elaborate is dropped and the spec goes on without it",
          "helpers" not in spec and spec["stmt"] == stmt, str(spec))

    class AskLLM:
        def __init__(self):
            self.asked = []

        def _ask(self, prompt):
            self.asked.append(prompt)
            return "def toList (l : C.List) : List Nat := []"

    class FixedOnly(Checker):
        def ensure_helpers(self, project_dir, text):
            # this Lean rejects the first helpers and accepts the repaired ones
            return ("List Nat := []" in text), ([] if "List Nat := []" in text else ["error: unknown identifier"])
    llm = AskLLM()
    gated = []
    synth._gate.check_candidate = lambda *a, **k: gated.append(k.get("helpers", "")) or (
        _ for _ in ()).throw(StopIteration)
    spec = {"name": "s", "stmt": stmt, "preamble": pre}
    try:
        synth.validate([spec], "import Aeneas\n", [], FixedOnly(), llm=llm, func_name="f", project_dir="/p",
                       source="rust-aeneas")
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("a helper Lean rejects gets one repair from Lean's own error, and the statement goes on to the gate "
          "with the fixed helpers",
          len(llm.asked) == 1 and "error: unknown identifier" in llm.asked[0] and pre.strip() in llm.asked[0]
          and len(gated) == 1 and "List Nat := []" in gated[0] and "lss_hp_toList_" in spec.get("stmt", ""),
          str(gated)[:300] + str(spec)[-300:])
    llm = AskLLM()
    spec = {"name": "s", "stmt": stmt, "preamble": pre}
    synth._gate.check_candidate = lambda *a, **k: (_ for _ in ()).throw(StopIteration)
    try:
        synth.validate([spec], "import Aeneas\n", [], Bad(), llm=llm, func_name="f", project_dir="/p",
                       source="rust-aeneas")
    except StopIteration:
        pass
    finally:
        synth._gate.check_candidate = old_gate
    check("a repair Lean still rejects is asked once only, and the spec goes on without helpers",
          len(llm.asked) == 1 and "helpers" not in spec and spec["stmt"] == stmt, str(spec))


def run_static_with_proof():
    print("=== static: a statement the LLM proved itself ===")
    import synth
    import lean
    emitted = []

    class Checker:
        def try_proof(self, code, stmt, **k):
            return lean.ProofResult(proved=False, method="", error="")
    old_gate, old_emit = synth._gate.check_candidate, synth.events.emit
    asked = []
    synth._gate.check_candidate = lambda checker, text, *a, **k: asked.append(a) or (
        [{"check": "conclusion_shape", "ok": False, "detail": "the conclusion does not call `f`"}] if "BAD" in text
        else [{"check": c, "ok": True, "detail": ""} for c in synth._gate.checks_for(None)])
    synth.events.emit = lambda kind, **f: emitted.append((kind, f))
    try:
        specs = [{"name": "u", "stmt": "SAME", "status": "rejected", "fail_gate": "pbt"}]
        synth._admit_with_proof([{"name": "g", "stmt": "GOOD", "status": "proved", "method": "llm-gen-with-proof"},
                                 {"name": "b", "stmt": "BAD", "status": "proved", "method": "llm-gen-with-proof"},
                                 {"name": "s", "stmt": "SAME", "status": "proved", "method": "llm-gen-with-proof",
                                  "proof": "by rfl"}],
                                specs, "def f (n : Nat) : Nat := n", "f", Checker(), "/p", "lean-native")
    finally:
        synth._gate.check_candidate, synth.events.emit = old_gate, old_emit
    check("a statement proved by the LLM's own proof still passes the gate before it counts",
          [x["stmt"] for x in specs] == ["SAME", "GOOD"] and set(asked) == {("f", "def f (n : Nat) : Nat := n", "/p", "lean-native")},
          f"{specs} {asked}")
    check("a statement already there takes the proof, and loses its old failure",
          specs[0].get("proof") == "by rfl" and specs[0]["status"] == "proved" and "fail_gate" not in specs[0], str(specs[0]))
    got = {f.get("stmt"): f.get("status") for k, f in emitted if k == "verdict"}
    check("every statement gets a verdict event with its statement",
          got == {"GOOD": "proved", "BAD": "rejected", "SAME": "proved"}, str(emitted))


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
    run_planted_iter(checker)
    run_eval_inputs(checker, rust_dir)
    run_suite_refutations(checker)
    run_suite_types(checker)
    run_suite_runaways(checker)

    # a diverging evaluation: the evaluation server times out and restarts, the main one does not, and the
    # next check works
    main = lean_server.get_server(lss_config.project_dir("aeneas"))
    ev_server = lean_server.get_server(lss_config.project_dir("aeneas"), role="eval")
    st = _eval_env0(checker, rust_dir)
    r = ev_server.check("partial def lss_spin (x : Std.U32) : Result Std.U32 := lss_spin x", env=st.get("env0"),
                        timeout=60)
    check("diverging helper added", r.rc == 0 and r.new_env is not None, (r.stderr or "")[:200])
    if r.new_env is not None:
        st["env0"] = r.new_env
        before = (main.stats()["restarts"], ev_server.stats()["restarts"])
        ev, why = bounded._Lean(checker, rust_dir).eval("∀ (x : Std.U32), lss_spin x ⦃ _ => True ⦄",
                                                        [U32], U32, [[0]])
        check("a diverging evaluation leaves its input without a result, as running out of time",
              ev == {"kind": None, "rows": [], "partial": 1, "why": "timeout"}, f"{ev} {why}")
        after = (main.stats()["restarts"], ev_server.stats()["restarts"])
        check("only the evaluation server restarted", after[0] == before[0] and after[1] > before[1],
              f"{before} -> {after}")
        v = bounded.check_spec(checker, "∀ (value : Std.U32), identity value ⦃ r => r = value ⦄", "identity", rust_dir)
        check("after the timeout the evaluation env is rebuilt and checks still run", v["status"] == "pass", str(v))
    lean_server.shutdown_all()


def _eval_env0(checker, project_dir):
    """the bounded check's envs for a crate in the evaluation server, built now; a
    test's own function added to "env0" is in the next check env."""
    bounded._Lean(checker, project_dir)._env()
    return bounded.eval_state(project_dir)


def run_suite_runaways(checker):
    """inputs that run away, on the suite's own crates, read-only: each costs only
    itself and the larger inputs, is named, and restarts only the evaluation server."""
    print("=== full: inputs that never end, or run too long ===")
    import lean_server
    import lss_config
    suite = os.path.expanduser("~/rust_suite")
    main = lean_server.get_server(lss_config.project_dir("aeneas"))
    for crate, unit, stmt, title, want in [
            ("Tutorial", "i32_id", "∀ (i : Std.I32), i32_id i ⦃ _ => True ⦄",
             "a recursion that never ends on a negative number: the inputs before it are evaluated, it is named",
             lambda v: v["status"] == "timeout" and "(i := (-1)#i32) ran past" in v.get("detail", "")
             and v["detail"].startswith("2 of ")),
            ("AeneasStandalone", "loops_nested.iter", "∀ (m : Std.U32) (n : Std.U32), loops_nested.iter m n ⦃ _ => True ⦄",
             "a nested loop over two U32 bounds: the inputs that finish in time are evaluated, the larger ones are not",
             lambda v: v["status"] in ("pass", "vacuous", "refuted")
             or (v["status"] == "timeout" and v.get("unevaluated", 99) <= 24 and "ran past" in v.get("detail", ""))),
            ("Tutorial", "even", "∀ (i : Std.U32), even i ⦃ _ => True ⦄",
             "a recursion as deep as its argument: the inputs that finish in time are evaluated",
             lambda v: v["status"] in ("pass", "vacuous", "refuted")
             or (v["status"] == "timeout" and v.get("unevaluated", 99) <= 24))]:
        d = os.path.join(suite, crate)
        if not os.path.isdir(d):
            check(f"{d} exists", False, "not a directory")
            continue
        before = main.stats()["restarts"]
        v = bounded.check_spec(checker, stmt, unit, d)
        check(title, want(v), str(v)[:400])
        check(f"{unit}: the main server did not restart", main.stats()["restarts"] == before,
              f"{before} -> {main.stats()['restarts']}")


def run_eval_inputs(checker, rust_dir):
    """arrays, vectors and slices of numbers given to an evaluation as text: every
    number comes back exactly (signs, each type's edges, the empty one), as from
    today's literals; on the suite, a function over two 256-byte arrays is evaluated
    on all its inputs where building them as literals ran out of time."""
    print("=== full: number arrays given to the evaluation as text ===")
    import lean_server
    import lss_config
    state = _eval_env0(checker, rust_dir)
    server = lean_server.get_server(lss_config.project_dir("aeneas"), role="eval")
    r = server.check("def lss_echo_vi (v : alloc.vec.Vec Std.I64) : Result (alloc.vec.Vec Std.I64) := .ok v\n"
                     "def lss_echo_au (a : Array Std.U64 3#usize) : Result (Array Std.U64 3#usize) := .ok a\n"
                     "def lss_echo_su (s : Slice Std.Usize) : Result (Slice Std.Usize) := .ok s",
                     env=state.get("env0"), timeout=60)
    check("echo functions added", r.rc == 0 and r.new_env is not None, (r.stderr or r.stdout or "")[:200])
    if r.new_env is None:
        return
    state["env0"] = r.new_env
    i64, u64, usz = ("int", "Std.I64"), ("int", "Std.U64"), ("int", "Std.Usize")
    for fn, T, rows in [
            ("lss_echo_vi", ("vec", i64), [[[]], [[-2 ** 63, 2 ** 63 - 1, 0, -1]], [[5] * 64]]),
            ("lss_echo_au", ("array", u64, 3), [[[0, 2 ** 64 - 1, 7]], [[1, 1, 1]]]),
            ("lss_echo_su", ("slice", usz), [[[]], [[2 ** 64 - 1, 2 ** 32, 3]]])]:
        stmt = f"∀ (x : {tc.lean_type_str(T)}), {fn} x ⦃ _ => True ⦄"
        got = {}
        for form in ("text", "literal"):
            old = bounded.eval_literal
            if form == "literal":
                bounded.eval_literal = lambda t, v: tc.lean_literal(t, v)
            try:
                ev, why = bounded._Lean(checker, rust_dir).eval(stmt, [T], T, rows)
            finally:
                bounded.eval_literal = old
            got[form] = [json.loads(o["value"]) if o.get("outcome") == "holds" else o for o in ev["rows"]] \
                if ev else why
        want = [[str(x) for x in row[0]] for row in rows]
        check(f"{fn}: every number comes back exactly from text, as from literals",
              got["text"] == want and got["literal"] == want, str(got)[:400])
    suite = os.path.expanduser("~/rust_suite/AeneasStandalone")
    if not os.path.isdir(suite):
        check(f"{suite} exists", False, "not a directory")
        return
    v = bounded.check_spec(checker, "∀ (src : Array Std.U8 256#usize) (dst : Array Std.U8 256#usize), "
                           "iterators.copy_arrays src dst ⦃ _ => True ⦄", "iterators.copy_arrays", suite)
    check("a function over two 256-byte arrays is evaluated on every input, none cut short",
          v["status"] in ("pass", "vacuous", "refuted"), str(v)[:300])


def run_suite_refutations(checker):
    """kernel refutations that evaluate the call: a recursive function, a loop, plain
    arithmetic. on the suite's own crates, read-only."""
    print("=== full: kernel refutations that evaluate the call ===")
    suite = os.path.expanduser("~/rust_suite")
    for crate, unit, stmt, title in [
            ("NoNestedBorrows", "list_nth_mut",
             "∀ {T : Type} (l : NoNestedBorrows.List T) (i : Std.U32), list_nth_mut l i ⦃ _ => True ⦄",
             "a recursive function's failing call is refuted by the kernel"),
            ("AeneasStandalone", "hashmap.HashMap.move_elements_loop",
             "∀ {T : Type} (ntable : hashmap.HashMap T) (slots : alloc.vec.Vec (hashmap.AList T)) (i : Std.Usize), "
             "hashmap.HashMap.move_elements_loop ntable slots i ⦃ _ => True ⦄",
             "a loop's failing call is refuted by the kernel"),
            ("Tutorial", "mul2_add1", "∀ (x : Std.U32), mul2_add1 x ⦃ _ => True ⦄",
             "an arithmetic overflow is refuted by the kernel"),
            ("AeneasStandalone", "arrays.sum", "∀ (s : Slice Std.U32), arrays.sum s ⦃ _ => True ⦄",
             "a loop over a slice that overflows is refuted by the kernel, through Slice.index_usize and the platform "
             "split"),
            ("AeneasStandalone", "overflowing_ops.isize_overflowing_div",
             "∀ (x y : Std.Isize), overflowing_ops.isize_overflowing_div x y ⦃ _ => True ⦄",
             "a division by zero in a library operation is refuted by the kernel"),
            ("AeneasStandalone", "scalars.match_isize", "∀ (x : Std.Isize), scalars.match_isize x ⦃ _ => True ⦄",
             "an overflow at Isize's 64-bit maximum is refuted by the kernel, at the platform's own maximum"),
            ("Tutorial", "Usize.Insts.TutorialCounter.incr",
             "∀ (self : Std.Usize), Usize.Insts.TutorialCounter.incr self ⦃ _ => True ⦄",
             "an overflow at Usize's 64-bit maximum is refuted by the kernel, at the platform's own maximum"),
            ("Tutorial", "add_with_carry", "∀ (x y : alloc.vec.Vec Std.U32), add_with_carry x y ⦃ _ => True ⦄",
             "an out-of-bounds index after a cast and an overflowing add is refuted by the kernel"),
            ("AeneasStandalone", "hashmap.HashMap.move_elements_loop",
             "∀ {T : Type} (ntable : hashmap.HashMap T) (slots : alloc.vec.Vec (hashmap.AList T)) (i : Std.Usize), "
             "hashmap.HashMap.move_elements_loop ntable slots i ⦃ r => r.1.max_load_factor = ntable.max_load_factor ⦄div",
             "a ⦄div statement whose call fails is refuted by the kernel")]:
        d = os.path.join(suite, crate)
        if not os.path.isdir(d):
            check(f"{d} exists", False, "not a directory")
            continue
        v = bounded.check_spec(checker, stmt, unit, d)
        check(title, v["status"] == "refuted" and v.get("kernel") is True, str(v)[:400])
    d = os.path.join(suite, "Loops")
    if os.path.isdir(d):
        v = bounded.check_spec(checker, "∀ (max i s : Std.U32), sum_loop max i s ⦃ _ => True ⦄", "sum_loop", d)
        check("an overflow that needs more loop steps than the evaluation unrolls is evaluation-only, and says so",
              v["status"] == "refuted" and v.get("kernel") is False
              and "with the loop still running" in v.get("kernel_why", ""), str(v)[:400])


def _trivial(def_text, name):
    """`∀ <the def's binders>, name <its explicit arguments> ⦃ _ => True ⦄` from an
    Aeneas def `def <name> <binders> : Result <T> :=`."""
    text = re.sub(r"--[^\n]*", " ", re.sub(r"/-.*?-/", " ", def_text, flags=re.DOTALL))
    m = re.search(r"\bdef\s+\S+\s*(.*?)\s*:\s*(?:Aeneas\.)?(?:Std\.)?Result\b", text, re.DOTALL)
    binders = " ".join(m.group(1).split()) if m else ""
    args = [n for g in re.findall(r"\(([^():]+):", binders) for n in g.split()]
    return f"∀ {binders}, {' '.join([name] + args)} ⦃ _ => True ⦄"


def run_suite_types(checker):
    """types the sampler reads through: a const generic array's length, a crate's type
    aliases. on the suite's own crates, read-only."""
    print("=== full: const generic arrays and type aliases ===")
    import callgraph
    suite = os.path.expanduser("~/rust_suite")
    for crate, unit, title in [
            ("Loops", "sum_array", "a function over an array of const generic length is evaluated, its length "
                                   "drawn with the array"),
            ("AeneasStandalone", "curve25519.mul_internal", "a function over a crate's alias for an array is evaluated"),
            ("NoNestedBorrows", "read_tuple_struct", "a function over a crate's alias for a pair is evaluated"),
            ("AeneasStandalone", "iterators.iter_range_loop", "a loop over a Range is evaluated"),
            ("AeneasStandalone", "iterators.copy_arrays_loop", "a loop over a Range and two arrays is evaluated"),
            ("AeneasStandalone", "iterators.iter_range_step_by_loop", "a loop over a StepBy of a Range is evaluated"),
            ("AeneasStandalone", "iterators.slice_iter_while_loop0", "a loop over a slice iterator is evaluated")]:
        d = os.path.join(suite, crate)
        if not os.path.isdir(d):
            check(f"{d} exists", False, "not a directory")
            continue
        g = callgraph.for_project(d)
        q = unit if unit in g.names else f"{g.crate}.{unit}"
        stmt = _trivial(g.def_text(q) or "", unit)
        v = bounded.check_spec(checker, stmt, unit, d)
        # a loop whose bound is drawn large runs past its time on some input: the smaller ones were evaluated
        some = v["status"] == "timeout" and re.match(r"[1-9]\d* of \d+ inputs evaluated", v.get("detail") or "")
        check(title, v["status"] in ("pass", "refuted", "vacuous") or some, f"{stmt} -> {str(v)[:300]}")


PLANTED_TYPES = """-- hand-written in the shape Aeneas generates, for LSS's tests
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

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

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

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


PLANTED_ITER_FUNS = """-- hand-written in the shape Aeneas generates, for LSS's tests
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace LssIter

/-- [lss_iter::range_len] -/
def range_len (r : core.ops.range.Range Std.Usize) : Result Std.Usize :=
  if r.start ≤ r.«end» then r.«end» - r.start else ok 0#usize

/-- [lss_iter::iter_left] -/
def iter_left (it : core.slice.iter.Iter Std.U32) : Result Bool :=
  ok (decide (it.i < it.slice.length))

/-- [lss_iter::ext] -/
axiom ext : Std.U32 → Result Std.U32

/-- [lss_iter::uses_ext] -/
def uses_ext (x : Std.U32) : Result Std.U32 := ext x

end LssIter
"""


def run_planted_iter(checker):
    """Aeneas's models of Rust's types as inputs: a Range (a field named `end`) and a
    slice iterator (its position a Nat), sampled, evaluated and refuted by the kernel;
    and a function with no code."""
    print("=== full: a Range and a slice iterator as inputs, a function with no code ===")
    import shutil
    import tempfile
    d = tempfile.mkdtemp()
    try:
        os.makedirs(os.path.join(d, "LssIter", "Code"))
        with open(os.path.join(d, "LssIter", "Code", "Funs.lean"), "w", encoding="utf-8") as f:
            f.write(PLANTED_ITER_FUNS)
        decls = [{"kind": "function", "is_local": True, "lean_name": f"LssIter.{u}", "rust_name": f"lss_iter::{u}"}
                 for u in ("range_len", "iter_left", "uses_ext")]
        with open(os.path.join(d, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump({"import": "LssIter", "declarations": decls}, f)
        rng = "∀ (r : core.ops.range.Range Std.Usize), range_len r "
        v = bounded.check_spec(checker, rng + "⦃ n => n.val = r.«end».val - r.start.val ⦄", "range_len", d)
        check("a true spec over a Range passes, rejecting wrong outputs", v["status"] == "pass" and v["warning"] is None,
              str(v)[:400])
        v = bounded.check_spec(checker, rng + "⦃ n => n.val = r.«end».val ⦄", "range_len", d)
        check("a false spec over a Range is refuted, its witness a Range",
              v["status"] == "refuted" and isinstance((v.get("witness") or [None])[0], dict), str(v)[:400])
        check("and the kernel checks it, the field `end` written quoted", v.get("kernel") is True, str(v)[:400])
        it = "∀ (it : core.slice.iter.Iter Std.U32), iter_left it "
        v = bounded.check_spec(checker, it + "⦃ b => b = decide (it.i < it.slice.length) ⦄", "iter_left", d)
        check("a true spec over a slice iterator passes", v["status"] == "pass", str(v)[:400])
        v = bounded.check_spec(checker, it + "⦃ b => b = true ⦄", "iter_left", d)
        check("a false one is refuted where the iterator is at its end, by the kernel, its position a Nat",
              v["status"] == "refuted" and v.get("kernel") is True, str(v)[:400])
        v = bounded.check_spec(checker, "∀ (x : Std.U32), uses_ext x ⦃ _ => True ⦄", "uses_ext", d)
        check("a function calling an axiom (a hardware model) is not evaluated, labelled: cannot run",
              v["status"] == "not_evaluated" and v.get("detail", "").startswith("cannot run: "), str(v)[:400])
    finally:
        shutil.rmtree(d, ignore_errors=True)


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
        check("a statement about a backward function's every input is refuted when its call fails",
              v["status"] == "refuted" and v.get("outcome") == "fail", str(v))
        check("that refutation is kernel-checked without deciding the postcondition", v.get("kernel") is True, str(v))
        v = b("∀ {T : Type} (x : T) (tl : LssPlanted.List T), nth_back (LssPlanted.List.Cons x tl) 0#u32 "
              "⦃ r => ∀ t, ∃ tl', r.2 t = LssPlanted.List.Cons t tl' ⦄", "nth_back")
        check("a statement about a backward function's every input whose call never fails is not evaluated",
              v["status"] == "not_evaluated" and "Decidable" in v.get("detail", ""), str(v))
        v = b("∀ {T : Type} (v : T), singleton v ⦃ r => r = some (LssPlanted.Node.mk v none none) ⦄", "singleton")
        check("equality on a tree is decided: the true spec passes", v["status"] == "pass", str(v))
        v = b("∀ {T : Type} (v : T), singleton v ⦃ r => r = none ⦄", "singleton")
        check("and a false one is refuted", v["status"] == "refuted", str(v))
    finally:
        shutil.rmtree(d, ignore_errors=True)


run_static_values()
run_static_recursive()
run_static_server()
run_static_nested_text()
run_static_commands()
run_static_core_types()
run_static_check()
run_static_run()
run_static_synth()
run_static_preamble()
run_static_with_proof()
if not static:
    run_full()
print()
print("all pass" if not fails else f"FAILED: {fails}")
sys.exit(1 if fails else 0)
