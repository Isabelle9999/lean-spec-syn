import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

import translation_check as tc

RUST_DIR = os.path.expanduser("~/rust_benchmarks")

static = "--static" in sys.argv
fails = []


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


print(f"mode {'static' if static else 'full'}")


def _roundtrip(label, T, v):
    enc = tc.canonical_encode(T, v)
    dec = tc.canonical_decode(T, enc)
    check(f"roundtrip {label}", dec == v, f"enc={enc!r} dec={dec!r}")


def run_static():
    print("=== static ===")

    BOOL = ("bool",)
    _roundtrip("bool true", BOOL, True)
    _roundtrip("bool false", BOOL, False)

    for lean_ty, (rty, bits, signed) in tc.INT_TYPES.items():
        T = ("int", lean_ty)
        lo = -(2 ** (bits - 1)) if signed else 0
        hi = 2 ** (bits - 1) - 1 if signed else 2 ** bits - 1
        _roundtrip(f"{lean_ty} min", T, lo)
        _roundtrip(f"{lean_ty} max", T, hi)
        _roundtrip(f"{lean_ty} 0", T, 0)

    U32 = ("int", "Std.U32")
    _roundtrip("tuple(U32, bool) extremes", ("tuple", [U32, BOOL]), [4294967295, True])
    _roundtrip("array[U32;3] extremes", ("array", U32, 3), [0, 1, 4294967295])
    _roundtrip("slice[U32] empty", ("slice", U32), [])
    _roundtrip("slice[U32] short", ("slice", U32), [4294967295])
    _roundtrip("vec[U32] empty", ("vec", U32), [])
    _roundtrip("vec[U32] short", ("vec", U32), [0, 4294967295])

    _roundtrip("Option<U32> None", ("option", U32), None)
    _roundtrip("Option<U32> Some(extremes)", ("option", U32), 0)
    _roundtrip("Option<U32> Some(max)", ("option", U32), 4294967295)
    _roundtrip("Option<Usize> None", ("option", ("int", "Std.Usize")), None)
    _roundtrip("Option<bool> Some(false)", ("option", BOOL), False)
    _roundtrip("Option<vec[U32]> None", ("option", ("vec", U32)), None)
    _roundtrip("Option<vec[U32]> Some(empty)", ("option", ("vec", U32)), [])
    _roundtrip("Option<vec[U32]> Some(short)", ("option", ("vec", U32)), [4294967295])
    check("rust_type_str Option<U32>", tc.rust_type_str(("option", U32)) == "Option<u32>",
          tc.rust_type_str(("option", U32)))
    check("lean_type_str Option U32", tc.lean_type_str(("option", U32)) == "(Option Std.U32)",
          tc.lean_type_str(("option", U32)))
    check("lean_literal Option<U32> None is 'none'",
          tc.lean_literal(("option", U32), None) == "none",
          tc.lean_literal(("option", U32), None))
    check("lean_literal Option<U32> Some uses 'some'",
          tc.lean_literal(("option", U32), 5).startswith("(some "),
          tc.lean_literal(("option", U32), 5))

    # a synthetic plain enum (FeatureSuite itself only has the Nil/Cons list
    # shape) exercises the general "enum" branch of every function below.
    enum_T = ("enum", "synthetic.Color",
              [("Red", []), ("Point", [("int", "Std.I32"), ("int", "Std.I32")])])
    _roundtrip("synthetic enum nullary variant", enum_T, ("Red", []))
    _roundtrip("synthetic enum variant with args, extremes", enum_T,
               ("Point", [-2147483648, 2147483647]))
    check("rust_type_str on a general enum", tc.rust_type_str(enum_T) == "Color",
          tc.rust_type_str(enum_T))
    for fn, label in ((tc.rust_strategy_expr, "rust_strategy_expr"),
                       (lambda t: tc._rust_custom_body(t, "self"), "_rust_custom_body")):
        out = fn(enum_T)
        check(f"{label} on a general enum produces text", isinstance(out, str) and len(out) > 0, repr(out))
    lean_out = tc.lean_encode_expr(enum_T, "x")
    check("lean_encode_expr on a general enum produces text",
          isinstance(lean_out, str) and len(lean_out) > 0, repr(lean_out))

    # &mut handling: FeatureSuite has no function with a &mut parameter (checked
    # against the pinned crate source directly), so exercise the mut-final merge
    # logic statically instead of against a real run. Aeneas orders a function's
    # merged output as (return value, each &mut final in parameter order) and
    # drops a unit return when at least one &mut final exists, without wrapping
    # a lone surviving component in a tuple (SymbolicToPureTypes.ml:1190-1204,
    # mk_simpl_tuple_ty in PureUtils.ml:831-834).
    VEC_U32 = ("vec", U32)

    # fn f(v: &mut Vec<u32>, x: u32) -> () : the unit return is dropped, and the
    # single &mut final is not tuple-wrapped -- "ok" is exactly its own encoding.
    synth_f = {
        "name": "Synthetic.f", "rust_fn": "f",
        "args": [("v", VEC_U32, "mutref"), ("x", U32, "val")],
        "ret": VEC_U32, "ret_is_unit": True, "inputs": 4, "seed": 0,
    }
    synth_f_src = tc._gen_test_fn(synth_f, "ENV")
    check("mut-only merge: outcome has no separate mut_finals field",
          "mut_finals" not in synth_f_src, synth_f_src)
    ok_lines_f = [l for l in synth_f_src.splitlines() if "Ok(v) =>" in l]
    check("mut-only merge: exactly one Ok(v) arm generated", len(ok_lines_f) == 1, str(ok_lines_f))
    expect_f_arg = tc.rust_encode_expr(VEC_U32, "a0")
    check("mut-only merge: ok is exactly the &mut final's own encoding, unwrapped",
          bool(ok_lines_f) and ok_lines_f[0].rstrip().endswith(f", {expect_f_arg}),"),
          str(ok_lines_f))

    # fn g(v: &mut Vec<u32>, x: u32) -> u32 : the return survives, so "ok" is the
    # (return, mut final) pair in parameter order.
    synth_g = {
        "name": "Synthetic.g", "rust_fn": "g",
        "args": [("v", VEC_U32, "mutref"), ("x", U32, "val")],
        "ret": ("tuple", [U32, VEC_U32]), "ret_is_unit": False, "inputs": 4, "seed": 0,
    }
    synth_g_src = tc._gen_test_fn(synth_g, "ENV")
    ok_lines_g = [l for l in synth_g_src.splitlines() if "Ok(v) =>" in l]
    check("mut+return merge: exactly one Ok(v) arm generated", len(ok_lines_g) == 1, str(ok_lines_g))
    expect_g_arg = ('format!("[{}]", vec![' + tc.rust_encode_expr(U32, "v") + ", "
                     + tc.rust_encode_expr(VEC_U32, "a0") + '].join(","))')
    check("mut+return merge: ok tuples (return, mut final) in parameter order",
          bool(ok_lines_g) and ok_lines_g[0].rstrip().endswith(f", {expect_g_arg}),"),
          str(ok_lines_g))

    # the two sides must target the same canonical shape for the merged type:
    # the Lean encoder for the (unwrapped) merged type, and a canonical
    # encode/decode roundtrip over a sample value of it.
    lean_shape = tc.lean_encode_expr(VEC_U32, "r")
    check("mut-only merge: lean encoder's shape for the same merged type is an "
          "array of elements, not a 1-tuple", "String.intercalate" in lean_shape, lean_shape)
    _roundtrip("merged mut-only return shape vec[U32]", VEC_U32, [0, 4294967295])

    # the crate's own custom types, parsed statically from the real Types.lean
    # (no cargo, no Lean process -- this is the same file-reading loader.py
    # and callgraph.py already do).
    if not os.path.isdir(RUST_DIR):
        print("SKIP: custom-type roundtrips (FeatureSuite not built)")
    else:
        manifest = tc.loader.load_manifest(RUST_DIR)
        crate = tc.loader.detect_crate(RUST_DIR, manifest)
        types_path = os.path.join(RUST_DIR, crate, "Code", "Types.lean")
        types_text = open(types_path, encoding="utf-8").read()
        raw = tc.parse_custom_types(types_text, crate)
        custom_types, skip_reasons = tc.resolve_custom_types(raw, crate)
        check("records.Pair resolved", "records.Pair" in custom_types, str(skip_reasons))
        check("lists.List resolved", "lists.List" in custom_types, str(skip_reasons))
        if "records.Pair" in custom_types:
            _roundtrip("records.Pair extremes", custom_types["records.Pair"],
                       {"first": 0, "second": 4294967295})
        if "lists.List" in custom_types:
            for v in ([], [0], [4294967295, 0, 1]):
                _roundtrip(f"lists.List {v!r}", custom_types["lists.List"], v)

    # comparison rules on synthetic results
    check("ok==ok agrees", tc.compare_one({"ok": "5"}, {"ok": "5"}) is True)
    check("ok!=ok disagrees", tc.compare_one({"ok": "5"}, {"ok": "6"}) is False)
    check("panic+fail agrees", tc.compare_one({"panic": "boom"}, {"fail": "integerOverflow"}) is True)
    check("panic+div disagrees (div is its own bug, not a fail)",
          tc.compare_one({"panic": "boom"}, {"div": True}) is False)
    check("ok+fail disagrees", tc.compare_one({"ok": "5"}, {"fail": "panic"}) is False)
    check("panic+ok disagrees", tc.compare_one({"panic": "boom"}, {"ok": "5"}) is False)


def run_full():
    print("=== full ===")
    if not os.path.isdir(RUST_DIR):
        check("~/rust_benchmarks exists", False, "not built")
        return

    results = tc.run_check(RUST_DIR, inputs_per_function=8, seed=12345)
    check("some functions were checked", len(results["checked"]) > 0, str(results["checked"]))
    disagreeing = {n: e["disagreements"] for n, e in results["function_results"].items()
                    if e["disagreements"]}
    check("no disagreements on the real translation", not disagreeing, str(disagreeing))

    # plant a bug: a copy of a simple extracted function (identity) with one
    # operation changed, pointed at for that one Rust function only.
    overrides = {
        "feature_suite::identity": {
            "setup": ["def _planted_identity (value : Std.U32) : Result Std.U32 := do\n"
                      "  value + 1#u32"],
            "call_expr": "_planted_identity {a0}",
        }
    }
    bad = tc.run_check(RUST_DIR, inputs_per_function=8, seed=12345,
                        functions=["identity"], overrides=overrides)
    bad_entry = bad["function_results"].get("FeatureSuite.identity", {})
    check("planted bug is reported as a disagreement",
          bool(bad_entry.get("disagreements")), str(bad_entry))

    good = tc.run_check(RUST_DIR, inputs_per_function=8, seed=12345, functions=["identity"])
    good_entry = good["function_results"].get("FeatureSuite.identity", {})
    check("the unchanged copy reports no disagreement",
          good_entry.get("disagreements") == [], str(good_entry))


if static:
    run_static()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
