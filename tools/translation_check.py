"""translation differential check.

for every extracted Lean function of a crate, run the Lean function (through
LeanServer, against the pinned aeneas project) and the compiled Rust function
(through a cargo test harness written into a scratch copy of the crate) on
the same generated inputs, and report every disagreement.

usage: python tools/translation_check.py <crate_path> [--inputs N] [--seed N]
       [--out report.json]

crate_path is the Lean-side project path loader.py/callgraph.py use (the
directory holding <crate>/Code/{Types,Funs}.lean and the manifest), e.g.
~/rust_benchmarks for FeatureSuite. the real Rust crate is found from the
manifest's own input.path field.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import loader  # noqa: E402
import callgraph  # noqa: E402
import lean_server  # noqa: E402
import lss_config  # noqa: E402

SCRATCH = "/tmp/lss_diffcheck"
CARGO_TARGET_DIR = os.path.expanduser("~/.cache/lss/diffcheck-target")
LEAN_EVAL_TIMEOUT = 900
# elaborating one big list of N literal-and-proof terms grows much faster
# than N (measured: n=32 ~0.5s, n=64 ~50-100s, on both the real call and an
# elaborate-only control -- so it's the term elaboration, not evaluating the
# function, and splitting the batch is the fix). 32 is comfortably inside
# the fast region measured for arrays.is_sorted.
MAX_BATCH = 32
CARGO_TIMEOUT = 600

# lean scalar type name -> (rust type, bits, signed)
INT_TYPES = {
    "Std.U8": ("u8", 8, False), "Std.U16": ("u16", 16, False),
    "Std.U32": ("u32", 32, False), "Std.U64": ("u64", 64, False),
    "Std.U128": ("u128", 128, False), "Std.Usize": ("usize", 64, False),
    "Std.I8": ("i8", 8, True), "Std.I16": ("i16", 16, True),
    "Std.I32": ("i32", 32, True), "Std.I64": ("i64", 64, True),
    "Std.I128": ("i128", 128, True), "Std.Isize": ("isize", 64, True),
}
LEAN_SCALAR_SUFFIX = {
    "Std.U8": "u8", "Std.U16": "u16", "Std.U32": "u32", "Std.U64": "u64",
    "Std.U128": "u128", "Std.Usize": "usize",
    "Std.I8": "i8", "Std.I16": "i16", "Std.I32": "i32", "Std.I64": "i64",
    "Std.I128": "i128", "Std.Isize": "isize",
}


# ====================== type IR ======================
# a type is a tuple:
#  ("bool",)
#  ("int", lean_ty)                       -- lean_ty is one of INT_TYPES keys
#  ("tuple", [T, ...])
#  ("array", T, n)
#  ("slice", T)
#  ("vec", T)
#  ("struct", lean_name, [(field, T), ...])
#  ("enum", lean_name, [(variant, [T, ...]), ...])
#  ("list_enum", lean_name, nil_variant, cons_variant, elem_T)  -- Nil/Cons(T,Self) shape
#  ("option", T)  -- Rust Option<T> / Lean Option T, for any T already supported

class Unsupported(Exception):
    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


def _split_top(s, sep):
    """split s on sep at top level (not inside parens)."""
    parts, depth, cur = [], 0, ""
    i = 0
    while i < len(s):
        c = s[i]
        if c == "(":
            depth += 1
            cur += c
        elif c == ")":
            depth -= 1
            cur += c
        elif depth == 0 and s[i:i + len(sep)] == sep:
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        else:
            cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def parse_lean_type(s, custom_types):
    """lean type string -> TypeIR, or raises Unsupported."""
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        # strip a fully-wrapping paren pair
        depth = 0
        wraps = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    wraps = False
                    break
        if wraps:
            return parse_lean_type(s[1:-1], custom_types)

    if "×" in s:
        parts = _split_top(s, "×")
        if len(parts) > 1:
            return ("tuple", [parse_lean_type(p, custom_types) for p in parts])

    if s == "Bool":
        return ("bool",)
    if s == "Unit":
        return ("tuple", [])
    if s in INT_TYPES:
        return ("int", s)

    m = re.match(r'^Array\s+(.+?)\s+(\d+)#usize$', s)
    if m:
        elem = parse_lean_type(m.group(1), custom_types)
        return ("array", elem, int(m.group(2)))

    m = re.match(r'^Slice\s+(.+)$', s)
    if m:
        return ("slice", parse_lean_type(m.group(1), custom_types))

    m = re.match(r'^Option\s+(.+)$', s)
    if m:
        return ("option", parse_lean_type(m.group(1), custom_types))

    m = re.match(r'^alloc\.vec\.Vec\s+(.+)$', s)
    if m:
        return ("vec", parse_lean_type(m.group(1), custom_types))
    m = re.match(r'^Vec\s+(.+)$', s)
    if m:
        return ("vec", parse_lean_type(m.group(1), custom_types))

    if s in custom_types:
        return custom_types[s]

    raise Unsupported(f"unsupported Lean type {s!r}")


# ====================== Types.lean parsing ======================

def _parse_struct_block(name, body):
    fields = []
    for line in body.splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        fname, ftype = line.split(":", 1)
        fields.append((fname.strip(), ftype.strip()))
    return fields


def _parse_enum_block(name, body):
    variants = []
    for m in re.finditer(r'^\|\s*(\w+)\s*(?::\s*(.*))?$', body, re.MULTILINE):
        vname, sig = m.group(1), (m.group(2) or "").strip()
        if not sig:
            variants.append((vname, []))
            continue
        arg_strs = [p.strip() for p in sig.split("→")]
        arg_strs = arg_strs[:-1]  # last part is the return type (the enum itself)
        variants.append((vname, arg_strs))
    return variants


def parse_custom_types(types_text, crate):
    """crate's Types.lean -> {short_name: raw struct/enum spec (unresolved field type strings)}."""
    raw = {}
    for m in re.finditer(
        r'^structure\s+([\w.]+)\s+where\n((?:^  .+\n?)*)',
        types_text, re.MULTILINE,
    ):
        raw[m.group(1)] = ("struct", _parse_struct_block(m.group(1), m.group(2)))
    for m in re.finditer(
        r'^inductive\s+([\w.]+)\s+where\n((?:\|.*\n?)*)',
        types_text, re.MULTILINE,
    ):
        raw[m.group(1)] = ("enum", _parse_enum_block(m.group(1), m.group(2)))
    return raw


def resolve_custom_types(raw, crate):
    """raw Types.lean specs -> {short_name: TypeIR}, skipping ones whose fields
    don't resolve; returns (resolved, skip_reasons)."""
    resolved = {}
    skip_reasons = {}
    pending = dict(raw)

    changed = True
    while changed and pending:
        changed = False
        for name, (kind, spec) in list(pending.items()):
            try:
                if kind == "struct":
                    fields = [(fn, parse_lean_type(ft if ft != name.split(".")[-1] else name, resolved))
                              for fn, ft in spec]
                    resolved[name] = ("struct", name, fields)
                else:
                    variants = []
                    for vname, arg_strs in spec:
                        args = []
                        for a in arg_strs:
                            a = a.strip()
                            if a == name or a == name.split(".")[-1]:
                                args.append(("self",))
                            else:
                                args.append(parse_lean_type(a, resolved))
                        variants.append((vname, args))
                    # detect the Nil/Cons(T, Self) list shape
                    nonrec = [v for v in variants if not any(a == ("self",) for a in v[1])]
                    rec = [v for v in variants if any(a == ("self",) for a in v[1])]
                    if (len(variants) == 2 and len(nonrec) == 1 and len(rec) == 1
                            and len(nonrec[0][1]) == 0 and len(rec[0][1]) == 2
                            and rec[0][1][1] == ("self",)):
                        resolved[name] = ("list_enum", name, nonrec[0][0], rec[0][0], rec[0][1][0])
                    elif rec:
                        raise Unsupported("recursive enum shape other than Nil/Cons(T, Self)")
                    else:
                        resolved[name] = ("enum", name, variants)
                del pending[name]
                changed = True
            except Unsupported as e:
                skip_reasons[name] = str(e)
    for name in pending:
        skip_reasons.setdefault(name, "could not resolve field/variant types")
    return resolved, skip_reasons


# ====================== signature parsing ======================

def parse_signature(def_text, short_name, custom_types):
    m = re.search(r'^def\s+' + re.escape(short_name) + r'\b', def_text, re.MULTILINE)
    if m is None:
        raise Unsupported("could not find def header")
    rest = def_text[m.end():]
    body_start = rest.find(":=")
    if body_start == -1:
        raise Unsupported("could not find ':=' in def header")
    head = rest[:body_start]
    param_groups, pos = [], 0
    while True:
        while pos < len(head) and head[pos].isspace():
            pos += 1
        if pos >= len(head) or head[pos] != "(":
            break
        depth, start = 1, pos
        pos += 1
        while pos < len(head) and depth > 0:
            if head[pos] == "(":
                depth += 1
            elif head[pos] == ")":
                depth -= 1
            pos += 1
        param_groups.append(head[start + 1:pos - 1])
    after = head[pos:]
    ret_m = re.search(r':\s*(.+)', after, re.DOTALL)
    if ret_m is None:
        raise Unsupported("no return type found")
    ret_str = " ".join(ret_m.group(1).split())
    rm = re.match(r'^Result\s+(.+)$', ret_str)
    if rm is None:
        raise Unsupported(f"return type {ret_str!r} is not 'Result <T>'")
    ret_type = parse_lean_type(rm.group(1), custom_types)

    args = []
    for grp in param_groups:
        if ":" not in grp:
            continue
        names_part, type_part = grp.split(":", 1)
        names = names_part.split()
        t = parse_lean_type(" ".join(type_part.split()), custom_types)
        for nm in names:
            args.append((nm, t))
    return args, ret_type


# ====================== Rust codegen ======================

def rust_type_str(T):
    kind = T[0]
    if kind == "bool":
        return "bool"
    if kind == "int":
        return INT_TYPES[T[1]][0]
    if kind == "tuple":
        return "(" + ", ".join(rust_type_str(e) for e in T[1]) + ")"
    if kind == "array":
        return f"[{rust_type_str(T[1])}; {T[2]}]"
    if kind in ("slice",):
        return f"Vec<{rust_type_str(T[1])}>"
    if kind == "vec":
        return f"Vec<{rust_type_str(T[1])}>"
    if kind in ("struct", "enum", "list_enum"):
        return T[1].split(".")[-1]
    if kind == "option":
        return f"Option<{rust_type_str(T[1])}>"
    raise Unsupported(f"no rust type for {T!r}")


def _rust_ident(name):
    return re.sub(r'[^a-zA-Z0-9_]', '_', name)


def rust_strategy_expr(T):
    kind = T[0]
    if kind == "bool":
        return "proptest::prelude::any::<bool>()"
    if kind == "int":
        rty = INT_TYPES[T[1]][0]
        return f"proptest::prelude::any::<{rty}>()"
    if kind == "tuple":
        return "(" + ", ".join(rust_strategy_expr(e) for e in T[1]) + ")"
    if kind == "array":
        n = T[2]
        if 1 <= n <= 32:
            return f"proptest::array::uniform{n}({rust_strategy_expr(T[1])})"
        raise Unsupported(f"array length {n} not supported by proptest::array::uniformN")
    if kind in ("slice", "vec"):
        return f"proptest::collection::vec({rust_strategy_expr(T[1])}, 0..=6)"
    if kind == "struct":
        field_strats = ", ".join(rust_strategy_expr(ft) for _, ft in T[2])
        tyname = rust_type_str(T)
        return (f"({field_strats},).prop_map(|v| {tyname} {{ "
                + ", ".join(f"{fn}: v.{i}" for i, (fn, _) in enumerate(T[2])) + " })")
    if kind == "enum":
        tyname = rust_type_str(T)
        arms = []
        for vname, arg_types in T[2]:
            if not arg_types:
                arms.append(f"proptest::prelude::Just({tyname}::{vname})")
            else:
                strat = "(" + ", ".join(rust_strategy_expr(a) for a in arg_types) + ",)"
                ctor = ", ".join(f"v.{i}" for i in range(len(arg_types)))
                arms.append(f"{strat}.prop_map(|v| {tyname}::{vname}({ctor}))")
        return "proptest::prelude::Union::new(vec![" + ", ".join(f"{a}.boxed()" for a in arms) + "])"
    if kind == "list_enum":
        tyname = T[1].split(".")[-1]
        nil_v, cons_v = T[2], T[3]
        elem = rust_strategy_expr(T[4])
        return (f"proptest::collection::vec({elem}, 0..=5).prop_map(|v| {{ "
                f"let mut acc = {tyname}::{nil_v}; "
                f"for x in v.into_iter().rev() {{ acc = {tyname}::{cons_v}(x, Box::new(acc)); }} "
                f"acc }})")
    if kind == "option":
        return f"proptest::option::of({rust_strategy_expr(T[1])})"
    raise Unsupported(f"no strategy for {T!r}")


def rust_encode_expr(T, var):
    kind = T[0]
    if kind == "bool":
        return f'(if {var} {{ "true".to_string() }} else {{ "false".to_string() }})'
    if kind == "int":
        return f'format!("\\"{{}}\\"", {var})'
    if kind == "tuple":
        if not T[1]:
            return '"[]".to_string()'
        parts = [rust_encode_expr(e, f"{var}.{i}") for i, e in enumerate(T[1])]
        return 'format!("[{}]", vec![' + ", ".join(parts) + '].join(","))'
    if kind in ("array", "slice", "vec"):
        elem_var = "_e"
        inner = rust_encode_expr(T[1], elem_var)
        return (f'format!("[{{}}]", {var}.iter().map(|{elem_var}| {inner})'
                f'.collect::<Vec<_>>().join(","))')
    if kind in ("struct", "enum", "list_enum", "option"):
        # custom types get one DiffJson impl (see _rust_custom_body); Option<T>
        # gets a blanket one (see generate_module_harness). every call site
        # just dispatches through the trait, including recursive ones
        # (list_enum's tail is a Box<Self>, which auto-derefs).
        return f"({var}).to_diff_json()"
    raise Unsupported(f"no encoder for {T!r}")


def _rust_custom_body(T, var):
    """the match/field expression for a custom type's to_diff_json body
    (used only once per type, inside its DiffJson impl)."""
    kind = T[0]
    if kind == "struct":
        parts = [f'format!("\\"{fn}\\":{{}}", {rust_encode_expr(ft, f"{var}.{fn}")})'
                 for fn, ft in T[2]]
        return 'format!("{{{}}}", vec![' + ", ".join(parts) + '].join(","))'
    if kind == "enum":
        tyname = rust_type_str(T)
        arms = []
        for vname, arg_types in T[2]:
            if not arg_types:
                arms.append(f'{tyname}::{vname} => "{{\\"tag\\":\\"{vname}\\",\\"args\\":[]}}".to_string()')
            else:
                binders = ", ".join(f"a{i}" for i in range(len(arg_types)))
                encs = ", ".join(rust_encode_expr(a, f"a{i}") for i, a in enumerate(arg_types))
                arms.append(f'{tyname}::{vname}({binders}) => format!("{{{{\\"tag\\":\\"{vname}\\",\\"args\\":[{{}}]}}}}", '
                            f'vec![{encs}].join(","))')
        return "(match " + var + " { " + " ".join(a + "," for a in arms) + " })"
    if kind == "list_enum":
        tyname = T[1].split(".")[-1]
        nil_v, cons_v = T[2], T[3]
        enc_elem = rust_encode_expr(T[4], "h")
        return ("(match " + var + " { "
                + f'{tyname}::{nil_v} => "{{\\"tag\\":\\"{nil_v}\\",\\"args\\":[]}}".to_string(), '
                + f'{tyname}::{cons_v}(h, t) => format!("{{{{\\"tag\\":\\"{cons_v}\\",\\"args\\":[{{}},{{}}]}}}}", '
                + f'{enc_elem}, t.to_diff_json()), '
                + "})")
    raise Unsupported(f"no custom body for {T!r}")


def rust_filler_expr(T):
    """a harmless concrete value of T, for argument slots not under edge-testing
    in a given edge-case row. avoids relying on #[derive(Default)], which an
    enum needs a #[default] variant to get."""
    kind = T[0]
    if kind == "bool":
        return "false"
    if kind == "int":
        return f"0{INT_TYPES[T[1]][0]}"
    if kind == "tuple":
        return "(" + ", ".join(rust_filler_expr(e) for e in T[1]) + ",)"
    if kind == "array":
        return "[" + ", ".join([rust_filler_expr(T[1])] * T[2]) + "]"
    if kind in ("slice", "vec"):
        return "vec![]"
    if kind == "struct":
        tyname = rust_type_str(T)
        fields = ", ".join(f"{fn}: {rust_filler_expr(ft)}" for fn, ft in T[2])
        return f"{tyname} {{ {fields} }}"
    if kind == "enum":
        vname, arg_types = T[2][0]
        tyname = rust_type_str(T)
        if not arg_types:
            return f"{tyname}::{vname}"
        return f"{tyname}::{vname}(" + ", ".join(rust_filler_expr(a) for a in arg_types) + ")"
    if kind == "list_enum":
        return f'{T[1].split(".")[-1]}::{T[2]}'
    if kind == "option":
        return "None"
    raise Unsupported(f"no filler for {T!r}")


def rust_edge_values(T):
    """concrete rust literal expressions for 0/1/MIN/MAX (ints), empty/short (collections)."""
    kind = T[0]
    if kind == "int":
        rty, _, _ = INT_TYPES[T[1]]
        vals = [f"0{rty}", f"1{rty}", f"{rty}::MIN", f"{rty}::MAX"]
        return vals
    if kind == "bool":
        return ["false", "true"]
    if kind in ("array",):
        return []  # fixed length, no "empty" variant possible
    if kind in ("slice", "vec"):
        elem_edges = rust_edge_values(T[1]) or [rust_filler_expr(T[1])]
        return ["vec![]", f"vec![{elem_edges[0]}]"]
    if kind == "list_enum":
        tyname = T[1].split(".")[-1]
        return [f"{tyname}::{T[2]}"]
    if kind == "option":
        inner = rust_edge_values(T[1]) or [rust_filler_expr(T[1])]
        return ["None", f"Some({inner[0]})"]
    return []


def generate_module_harness(funcs, out_dir_env):
    """funcs: list of dicts with name, args (name,T,mode), ret (T), inputs, seed."""
    lines = [
        "#[cfg(test)]",
        "mod _lss_diffcheck {",
        "    #![allow(dead_code, unused_imports, non_snake_case)]",
        "    use super::*;",
        "    use proptest::prelude::*;",
        "    use proptest::test_runner::{TestRunner, Config, TestRng, RngAlgorithm};",
        "    use std::io::Write;",
        "",
        "    trait DiffJson { fn to_diff_json(&self) -> String; }",
    ]
    for rty in {"bool"} | {v[0] for v in INT_TYPES.values()}:
        if rty == "bool":
            lines.append('    impl DiffJson for bool { fn to_diff_json(&self) -> String { '
                          'if *self { "true".to_string() } else { "false".to_string() } } }')
        else:
            lines.append(f'    impl DiffJson for {rty} {{ fn to_diff_json(&self) -> String {{ '
                          f'format!("\\"{{}}\\"", self) }} }}')
    lines.append('    impl<T: DiffJson> DiffJson for Option<T> { fn to_diff_json(&self) -> String { '
                  'match self { None => "null".to_string(), Some(x) => x.to_diff_json() } } }')
    lines.append("")

    for fdesc in funcs:
        for T in [t for _, t, _ in fdesc["args"]] + [fdesc["ret"]]:
            for tyname, tydef in _collect_custom(T):
                impl = _rust_custom_impl(tyname, tydef)
                if impl not in lines:
                    lines.append(impl)

    for fdesc in funcs:
        lines.append(_gen_test_fn(fdesc, out_dir_env))

    lines.append("}")
    return "\n".join(lines) + "\n"


def _collect_custom(T, seen=None):
    seen = seen if seen is not None else set()
    out = []
    kind = T[0]
    if kind == "struct" and T[1] not in seen:
        seen.add(T[1])
        out.append((T[1], T))
        for _, ft in T[2]:
            out.extend(_collect_custom(ft, seen))
    elif kind == "enum" and T[1] not in seen:
        seen.add(T[1])
        out.append((T[1], T))
        for _, args in T[2]:
            for a in args:
                out.extend(_collect_custom(a, seen))
    elif kind == "list_enum" and T[1] not in seen:
        seen.add(T[1])
        out.append((T[1], T))
        out.extend(_collect_custom(T[4], seen))
    elif kind in ("tuple",):
        for e in T[1]:
            out.extend(_collect_custom(e, seen))
    elif kind in ("array", "slice", "vec", "option"):
        out.extend(_collect_custom(T[1], seen))
    return out


def _rust_custom_impl(tyname, T):
    short = tyname.split(".")[-1]
    body = _rust_custom_body(T, "self")
    return f"    impl DiffJson for {short} {{ fn to_diff_json(&self) -> String {{ {body} }} }}"


def _gen_test_fn(fdesc, out_dir_env):
    name = fdesc["name"]
    rust_fn = fdesc["rust_fn"]
    args = fdesc["args"]  # [(name, T, mode)] mode in "val"/"ref"/"mutref"
    ret = fdesc["ret"]
    n = fdesc["inputs"]
    seed = fdesc["seed"]
    fn_id = _rust_ident(name)

    strat_tuple = "(" + ", ".join(rust_strategy_expr(t) for _, t, _ in args) + ",)"
    seed_bytes = ", ".join(str(b) for b in _seed_bytes(seed, fn_id))

    edge_rows = []
    for i, (an, at, _) in enumerate(args):
        for ev in rust_edge_values(at):
            row = []
            for j, (an2, at2, _) in enumerate(args):
                row.append(ev if j == i else rust_filler_expr(at2))
            edge_rows.append(row)

    lines = []
    lines.append(f'    #[test]')
    lines.append(f'    fn _diffcheck_{fn_id}() {{')
    lines.append(f'        let out_dir = std::env::var("{out_dir_env}").expect("{out_dir_env} not set");')
    lines.append(f'        let path = format!("{{}}/{name}.jsonl", out_dir);')
    lines.append(f'        let mut f = std::fs::File::create(&path).expect("create output file");')
    lines.append(f'        let seed: [u8; 32] = [{seed_bytes}];')
    lines.append(f'        let mut runner = TestRunner::new_with_rng(Config::default(), '
                 f'TestRng::from_seed(RngAlgorithm::ChaCha, &seed));')
    lines.append(f'        let strategy = {strat_tuple};')
    lines.append(f'        let mut inputs: Vec<_> = Vec::new();')

    for row in edge_rows:
        lines.append(f'        inputs.push(({", ".join(row)},));')

    lines.append(f'        while inputs.len() < {n} {{')
    lines.append(f'            use proptest::strategy::{{Strategy, ValueTree}};')
    lines.append(f'            let tree = strategy.new_tree(&mut runner).unwrap();')
    lines.append(f'            inputs.push(tree.current());')
    lines.append(f'        }}')
    lines.append(f'        inputs.truncate({n});')
    lines.append(f'        for args_tuple in inputs {{')

    call_args = []
    arg_json_parts = []
    mut_locals = []
    for i, (an, at, mode) in enumerate(args):
        local = f"a{i}"
        decl = "let mut" if mode == "mutref" else "let"
        lines.append(f'            {decl} {local} = args_tuple.{i}.clone();')
        arg_json_parts.append(rust_encode_expr(at, local))
        if mode == "val":
            call_args.append(f"{local}.clone()")
        elif mode == "ref":
            call_args.append(f"&{local}")
        else:
            call_args.append(f"&mut {local}")
            mut_locals.append((an, at, local))

    call = f"{rust_fn}(" + ", ".join(call_args) + ")"
    lines.append(f'            let args_json = vec![{", ".join(arg_json_parts)}].join(",");')
    lines.append(f'            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {call}));')
    # Aeneas orders a function's outputs as (return value, each &mut final in
    # parameter order), dropping a unit return when there is at least one
    # &mut final (see SymbolicToPureTypes.ml:compute_output_ty_from_decomposed);
    # mirror that here so "ok" lines up element-for-element with the Lean side.
    mut_parts = [rust_encode_expr(t, local) for _, t, local in mut_locals]
    drop_ret = bool(mut_locals) and fdesc["ret_is_unit"]
    if drop_ret:
        ok_parts = mut_parts
    else:
        ret_component = ret[1][0] if mut_locals else ret
        ok_parts = [rust_encode_expr(ret_component, "v")] + mut_parts
    ok_enc = ok_parts[0] if len(ok_parts) == 1 else (
        'format!("[{}]", vec![' + ", ".join(ok_parts) + '].join(","))')
    lines.append(f'            let outcome_json = match result {{')
    lines.append(f'                Ok(v) => format!("{{{{\\"ok\\":{{}}}}}}", {ok_enc}),')
    lines.append(f'                Err(e) => {{')
    lines.append(f'                    let msg = if let Some(s) = e.downcast_ref::<&str>() {{ s.to_string() }}')
    lines.append(f'                        else if let Some(s) = e.downcast_ref::<String>() {{ s.clone() }}')
    lines.append(f'                        else {{ "panic".to_string() }};')
    lines.append(f'                    format!("{{{{\\"panic\\":{{:?}}}}}}", msg)')
    lines.append(f'                }}')
    lines.append(f'            }};')
    lines.append('            writeln!(f, "{{\\"args\\":[{}],\\"outcome\\":{}}}", '
                 'args_json, outcome_json).unwrap();')
    lines.append(f'        }}')
    lines.append(f'    }}')
    return "\n".join(lines)


def _seed_bytes(seed, fn_id):
    import hashlib
    h = hashlib.sha256(f"{seed}:{fn_id}".encode()).digest()
    return list(h[:32])


# ====================== Lean codegen ======================

def lean_literal(T, value):
    kind = T[0]
    if kind == "bool":
        return "true" if value else "false"
    if kind == "int":
        n = int(value)
        lit = f"({n})" if n < 0 else str(n)
        # Usize/Isize are platform-width scalars. ofNat/ofInt's default proof
        # obligation is x <= cMax, which for Usize/Isize is deliberately the
        # *conservative* (32-bit) bound, not the actual platform width -- so
        # it rejects any in-range value above U32/I32's max on a 64-bit
        # platform. ofNatCore/ofIntCore's own obligation (x < 2^numBits) is
        # the real platform bound; proving that symbolically needs to case
        # split on System.Platform.numBits_eq (32 or 64), and the 32-bit case
        # is then genuinely false for a value that only fits in 64 bits, so
        # native_decide (which runs the check instead of reasoning about it)
        # is what actually resolves it on this (64-bit) platform.
        if T[1] == "Std.Usize":
            return (f"(Usize.ofNatCore {lit} (by first | "
                     f"(simp [Usize.numBits]; cases System.Platform.numBits_eq <;> simp_all; done) | "
                     f"native_decide))")
        if T[1] == "Std.Isize":
            return (f"(Isize.ofIntCore {lit} (by first | "
                     f"(simp [Isize.numBits]; cases System.Platform.numBits_eq <;> simp_all; done) | "
                     f"native_decide))")
        suf = LEAN_SCALAR_SUFFIX[T[1]]
        return f"{lit}#{suf}"
    if kind == "tuple":
        return "(" + ", ".join(lean_literal(e, v) for e, v in zip(T[1], value)) + ")"
    if kind == "array":
        # Array's obligation is l.length = n.val for a small literal n: a
        # plain structural fact, nothing to do with Usize.max/numBits.
        inner = ", ".join(lean_literal(T[1], v) for v in value)
        return f"(⟨[{inner}], by decide⟩ : Array {lean_type_str(T[1])} {T[2]}#usize)"
    if kind in ("slice", "vec"):
        # Vec/Slice's obligation is l.length <= Usize.max, which needs the
        # irreducible Usize.max/numBits unfolded and cased on the platform
        # width; decide alone is a cheap fast path for the (common) short
        # lists this produces, native_decide a fallback for anything it
        # can't close symbolically.
        ctor = "Slice" if kind == "slice" else "alloc.vec.Vec"
        inner = ", ".join(lean_literal(T[1], v) for v in value)
        return (f"(⟨[{inner}], by first | decide | "
                f"(simp [Usize.max, Usize.numBits]; cases System.Platform.numBits_eq <;> simp_all; done) | "
                f"native_decide⟩ : {ctor} {lean_type_str(T[1])})")
    if kind == "struct":
        parts = ", ".join(f"{fn} := {lean_literal(ft, value[fn])}" for fn, ft in T[2])
        return "{ " + parts + " }"
    if kind == "enum":
        for vname, arg_types in T[2]:
            if value.get("tag") == vname:
                if not arg_types:
                    return f"{T[1]}.{vname}"
                args = " ".join(lean_literal(a, v) for a, v in zip(arg_types, value["args"]))
                return f"({T[1]}.{vname} {args})"
        raise Unsupported(f"unknown variant {value.get('tag')!r} for {T[1]}")
    if kind == "list_enum":
        _, lean_name, nil_v, cons_v, elem_T = T
        items = _list_enum_to_list(T, value)
        acc = f"{lean_name}.{nil_v}"
        for item in reversed(items):
            acc = f"({lean_name}.{cons_v} {lean_literal(elem_T, item)} {acc})"
        return acc
    if kind == "option":
        if value is None:
            return "none"
        return f"(some {lean_literal(T[1], value)})"
    raise Unsupported(f"no literal for {T!r}")


def _list_enum_to_list(T, value):
    _, lean_name, nil_v, cons_v, elem_T = T
    items = []
    v = value
    while isinstance(v, dict) and v.get("tag") == cons_v:
        items.append(v["args"][0])
        v = v["args"][1]
    return items


def lean_type_str(T):
    kind = T[0]
    if kind == "bool":
        return "Bool"
    if kind == "int":
        return T[1]
    if kind == "tuple":
        return "(" + " × ".join(lean_type_str(e) for e in T[1]) + ")"
    if kind == "array":
        return f"(Array {lean_type_str(T[1])} {T[2]}#usize)"
    if kind == "slice":
        return f"(Slice {lean_type_str(T[1])})"
    if kind == "vec":
        return f"(alloc.vec.Vec {lean_type_str(T[1])})"
    if kind in ("struct", "enum", "list_enum"):
        return T[1]
    if kind == "option":
        return f"(Option {lean_type_str(T[1])})"
    raise Unsupported(f"no lean type string for {T!r}")


def lean_encode_expr(T, var):
    kind = T[0]
    if kind == "bool":
        return f'(if {var} then "true" else "false")'
    if kind == "int":
        return f'("\\"" ++ toString ({var}).val ++ "\\"")'
    if kind == "tuple":
        n = len(T[1])
        parts = []
        for i, e in enumerate(T[1]):
            if n == 2:
                acc = f"{var}.1" if i == 0 else f"{var}.2"
            else:
                acc = var
                for _ in range(i):
                    acc = f"{acc}.2"
                if i < n - 1:
                    acc = f"{acc}.1"
            parts.append(lean_encode_expr(e, acc))
        return '("[" ++ String.intercalate "," [' + ", ".join(parts) + '] ++ "]")'
    if kind in ("array", "slice", "vec"):
        inner = lean_encode_expr(T[1], "_x")
        return ('("[" ++ String.intercalate "," (' + f'({var}).val.map (fun _x => {inner})'
                + ') ++ "]")')
    if kind == "struct":
        parts = [f'("\\"{fn}\\":" ++ {lean_encode_expr(ft, f"({var}).{fn}")})' for fn, ft in T[2]]
        return '("{" ++ String.intercalate "," [' + ", ".join(parts) + '] ++ "}")'
    if kind == "enum":
        arms = []
        for vname, arg_types in T[2]:
            if not arg_types:
                arms.append(f'| {T[1]}.{vname} => "{{\\"tag\\":\\"{vname}\\",\\"args\\":[]}}"')
            else:
                binders = " ".join(f"b{i}" for i in range(len(arg_types)))
                encs = ", ".join(lean_encode_expr(a, f"b{i}") for i, a in enumerate(arg_types))
                arms.append(f'| {T[1]}.{vname} {binders} => "{{\\"tag\\":\\"{vname}\\",\\"args\\":[" ++ '
                            f'String.intercalate "," [{encs}] ++ "]}}"')
        return f"(match {var} with " + " ".join(arms) + ")"
    if kind == "list_enum":
        _, lean_name, nil_v, cons_v, elem_T = T
        enc_elem = lean_encode_expr(elem_T, "h")
        return (f"(let rec _enc (x : {lean_name}) : String := match x with "
                f'| {lean_name}.{nil_v} => "{{\\"tag\\":\\"{nil_v}\\",\\"args\\":[]}}" '
                f"| {lean_name}.{cons_v} h t => "
                f'"{{\\"tag\\":\\"{cons_v}\\",\\"args\\":[" ++ {enc_elem} ++ "," ++ _enc t ++ "]}}" '
                f"_enc {var})")
    if kind == "option":
        inner = lean_encode_expr(T[1], "x")
        return f'(match {var} with | none => "null" | some x => {inner})'
    raise Unsupported(f"no encoder for {T!r}")


ERROR_ENCODE = (
    '(fun (e : Error) => match e with '
    '| Error.assertionFailure => "assertionFailure" '
    '| Error.integerOverflow => "integerOverflow" '
    '| Error.divisionByZero => "divisionByZero" '
    '| Error.arrayOutOfBounds => "arrayOutOfBounds" '
    '| Error.maximumSizeExceeded => "maximumSizeExceeded" '
    '| Error.panic => "panic" '
    '| Error.undef => "undef")'
)


def lean_result_encode_expr(ret_type, var):
    ok_enc = lean_encode_expr(ret_type, "v")
    return (f'(match {var} with '
            f'| Result.ok v => "{{\\"ok\\":" ++ {ok_enc} ++ "}}" '
            f'| Result.fail e => "{{\\"fail\\":\\"" ++ {ERROR_ENCODE} e ++ "\\"}}" '
            f'| Result.div => "{{\\"div\\":true}}")')


def build_eval_command(arg_types, ret_type, call_expr, input_rows):
    """call_expr is a python format string with {a0},{a1},... placeholders for
    the argument variables inside the lambda body, e.g. 'arrays.is_sorted {a0}'."""
    n = len(arg_types)
    if n == 1:
        pat = "a0"
    else:
        pat = "(" + ", ".join(f"a{i}" for i in range(n)) + ")"
    lits = []
    for row in input_rows:
        if n == 1:
            lits.append(lean_literal(arg_types[0], row[0]))
        else:
            lits.append("(" + ", ".join(lean_literal(t, v) for t, v in zip(arg_types, row)) + ")")
    list_lit = "[" + ", ".join(lits) + "]"
    call = call_expr.format(**{f"a{i}": f"a{i}" for i in range(n)})
    result_enc = lean_result_encode_expr(ret_type, "(" + call + ")")
    body = f'fun {pat} => {result_enc}'
    return f'#eval "[" ++ String.intercalate "," (({list_lit}).map ({body})) ++ "]"'


# ====================== unit selection ======================

def select_units(crate_path):
    manifest = loader.load_manifest(crate_path)
    crate = loader.detect_crate(crate_path, manifest)
    types_path = os.path.join(crate_path, crate, "Code", "Types.lean")
    types_text = open(types_path, encoding="utf-8").read() if os.path.exists(types_path) else ""
    raw_types = parse_custom_types(types_text, crate)
    custom_types, type_skip_reasons = resolve_custom_types(raw_types, crate)

    decls = {d["lean_name"]: d for d in loader.normalize_declarations(manifest)}
    g = callgraph.for_project(crate_path)

    selected, skipped = [], []
    for name in sorted(g.names):
        if g.loop_id(name) is not None:
            continue  # internal loop helper, no standalone Rust function to match
        if g.generic(name):
            skipped.append((name, "generic"))
            continue
        decl = decls.get(name)
        if decl is None or not decl.get("rust_name"):
            skipped.append((name, "no rust_name in manifest"))
            continue
        short_name = name[len(crate) + 1:] if name.startswith(crate + ".") else name
        def_text = g.def_text(name)
        if def_text is None:
            skipped.append((name, "no def_text from callgraph"))
            continue
        try:
            args, ret = parse_signature(def_text, short_name, custom_types)
        except Unsupported as e:
            skipped.append((name, str(e)))
            continue
        # TypeIR is a deliberately loose union of differently-shaped tuples
        # (see the comment at the top of the file); pyright can't verify
        # index 1 is in bounds just from checking index 0's value.
        bad = None
        for _, t in args:
            if t[0] in ("struct", "enum", "list_enum") and t[1] in type_skip_reasons:  # type: ignore[reportGeneralTypeIssues]
                bad = f"argument type {t[1]} not supported: {type_skip_reasons[t[1]]}"  # type: ignore[reportGeneralTypeIssues]
        if ret[0] in ("struct", "enum", "list_enum") and ret[1] in type_skip_reasons:  # type: ignore[reportGeneralTypeIssues]
            bad = f"return type {ret[1]} not supported: {type_skip_reasons[ret[1]]}"  # type: ignore[reportGeneralTypeIssues]
        if bad:
            skipped.append((name, bad))
            continue
        selected.append({
            "lean_name": name, "short_name": short_name, "crate": crate,
            "rust_name": decl["rust_name"], "args": args, "ret": ret,
        })
    for tname, reason in type_skip_reasons.items():
        skipped.append((f"type {tname}", reason))
    return crate, custom_types, selected, skipped


# ====================== Rust-side orchestration ======================

def _rust_source_map(manifest):
    inp = manifest.get("input")
    if not inp or not inp.get("path"):
        raise Unsupported("manifest has no input.path; cannot locate the Rust crate")
    return inp["path"]


def _rust_fn_module_and_name(rust_name):
    parts = rust_name.split("::")
    fn = parts[-1]
    mod_path = parts[1:-1]  # drop the crate name
    return mod_path, fn


def _split_top_rust(s, sep=","):
    parts, depth, cur = [], 0, ""
    opens, closes = "([<", ")]>"
    for c in s:
        if c in opens:
            depth += 1
            cur += c
        elif c in closes:
            depth -= 1
            cur += c
        elif depth == 0 and c == sep:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    parts.append(cur)
    return [p.strip() for p in parts]


def parse_rust_param_modes(src_file, fn_name):
    """'val'/'ref'/'mutref' per parameter, and whether the return type is unit
    (no '-> ...' or an explicit '-> ()'), read from the real fn signature."""
    text = open(src_file, encoding="utf-8").read()
    m = re.search(r'\bfn\s+' + re.escape(fn_name) + r'\s*\(', text)
    if m is None:
        raise Unsupported(f"could not find rust fn {fn_name} in {src_file}")
    i, depth, start = m.end(), 1, m.end()
    while depth > 0:
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
        i += 1
    params = [p for p in _split_top_rust(text[start:i - 1]) if p.strip()]
    modes = []
    for p in params:
        if ":" not in p:
            continue
        _, ty = p.split(":", 1)
        ty = ty.strip()
        if ty.startswith("&mut "):
            modes.append("mutref")
        elif ty.startswith("&"):
            modes.append("ref")
        else:
            modes.append("val")
    tail = text[i:text.index("{", i)].strip()
    ret_is_unit = tail in ("", "-> ()")
    return modes, ret_is_unit


def prepare_rust_copy(src_path):
    dst = os.path.join(SCRATCH, "crate")
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(src_path, dst)
    cargo_toml = os.path.join(dst, "Cargo.toml")
    with open(cargo_toml, "a", encoding="utf-8") as f:
        f.write('\n[dev-dependencies]\nproptest = "1"\n\n[profile.test]\noverflow-checks = true\n')
    for dirpath, _, files in os.walk(os.path.join(dst, "src")):
        for fn in files:
            if not fn.endswith(".rs"):
                continue
            path = os.path.join(dirpath, fn)
            text = open(path, encoding="utf-8").read()
            new_text = re.sub(r'^(pub (?:struct|enum)\s)', r'#[derive(Debug, Clone, PartialEq)]\n\1',
                               text, flags=re.MULTILINE)
            if new_text != text:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(new_text)
    return dst


def inject_rust_harness(crate_copy, selected, inputs_per_function, seed, out_dir_env):
    by_module = {}
    for fdesc in selected:
        mod_path, fn = _rust_fn_module_and_name(fdesc["rust_name"])
        rel = os.path.join(*mod_path) + ".rs" if mod_path else "lib.rs"
        src_file = os.path.join(crate_copy, "src", rel)
        if not os.path.exists(src_file):
            src_file = os.path.join(crate_copy, "src", "lib.rs")
        modes, ret_is_unit = parse_rust_param_modes(src_file, fn)
        args = []
        def_text_args = fdesc["args"]
        for (an, at), mode in zip(def_text_args, modes):
            args.append((an, at, mode))
        by_module.setdefault(tuple(mod_path), []).append({
            "name": fdesc["lean_name"], "rust_fn": fn, "args": args,
            "ret": fdesc["ret"], "ret_is_unit": ret_is_unit,
            "inputs": inputs_per_function, "seed": seed,
        })

    injected = []
    for mod_path, funcs in by_module.items():
        rel = os.path.join(*mod_path) + ".rs" if mod_path else "lib.rs"
        src_file = os.path.join(crate_copy, "src", rel)
        if not os.path.exists(src_file):
            src_file = os.path.join(crate_copy, "src", "lib.rs")
        harness = generate_module_harness(funcs, out_dir_env)
        with open(src_file, "a", encoding="utf-8") as f:
            f.write("\n" + harness)
        injected.append((src_file, [f["name"] for f in funcs]))
    return injected


def run_cargo_tests(crate_copy, out_dir, timeout=CARGO_TIMEOUT):
    env = dict(os.environ)
    env["LSS_DIFFCHECK_OUT"] = out_dir
    env["CARGO_TARGET_DIR"] = CARGO_TARGET_DIR
    os.makedirs(out_dir, exist_ok=True)
    try:
        r = subprocess.run(
            ["cargo", "test", "--", "--test-threads=1"],
            cwd=crate_copy, env=env, capture_output=True, text=True, timeout=timeout,
        )
        return r.returncode, r.stdout, r.stderr, False
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        err = e.stderr.decode() if isinstance(e.stderr, bytes) else (e.stderr or "")
        return 1, out, err + "\nTIMEOUT", True


def read_rust_rows(out_dir, lean_name):
    path = os.path.join(out_dir, f"{lean_name}.jsonl")
    if not os.path.exists(path):
        return None
    rows = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


# ====================== Lean-side orchestration ======================
# no setup commands are needed: lean_encode_expr reaches every value down to
# its scalars by field projection and pattern matching, neither of which
# needs a Repr/BEq instance on the composite type.

def _parse_eval_output(text):
    """#eval on a String-typed expression prints it quoted (Lean's own display
    wraps and escapes it), so the info message text is itself JSON-encoded
    text of our JSON array; decode twice."""
    return json.loads(json.loads(text))


def lean_preamble(crate):
    return (f"import {crate}.Code.Funs\nimport {crate}.Code.Types\n"
            f"set_option maxHeartbeats 4000000\nset_option maxRecDepth 4096\n"
            f"open Aeneas Aeneas.Std Result ControlFlow Error\nopen {crate}\n")


def _peak_rss_during(server, fn):
    """run fn() while sampling RssAnon across the worker's process group every
    0.25s; return (fn()'s result, peak bytes seen)."""
    worker = server._worker
    pgid = worker._proc.pid if worker and worker._proc else None
    samples = [0]
    stop = threading.Event()

    def _poll():
        while not stop.is_set():
            if pgid is not None:
                samples[0] = max(samples[0], lean_server._rss_anon_bytes(pgid))
            stop.wait(0.25)

    th = threading.Thread(target=_poll, daemon=True)
    th.start()
    try:
        result = fn()
    finally:
        stop.set()
        th.join(timeout=2)
    return result, samples[0]


def run_eval_batches(server, crate, arg_types, ret_type, call_expr, rows, setup=""):
    """send one #eval per MAX_BATCH-sized slice of rows (elaborating one huge
    literal list scales far worse than linearly -- see MAX_BATCH), each still
    bounded by the server's own timeout. returns (results or None, last
    CheckResult, peak RssAnon bytes seen across every batch)."""
    preamble = lean_preamble(crate)
    all_results = []
    peak = 0
    last_r = None
    for start in range(0, len(rows), MAX_BATCH):
        chunk = rows[start:start + MAX_BATCH]
        input_rows = [row["args"] for row in chunk]
        cmd = build_eval_command(arg_types, ret_type, call_expr, input_rows)
        full_cmd = preamble + setup + ("\n" if setup else "") + cmd

        def _send():
            return server.check(full_cmd, timeout=LEAN_EVAL_TIMEOUT)

        r, batch_peak = _peak_rss_during(server, _send)
        peak = max(peak, batch_peak)
        last_r = r
        if r.timed_out or r.mem_killed:
            return None, last_r, peak
        info = [m for m in r.messages if m["severity"] == "info"]
        if not info:
            return None, last_r, peak
        try:
            all_results.extend(_parse_eval_output(info[-1]["text"]))
        except json.JSONDecodeError:
            return None, last_r, peak
    return all_results, last_r, peak


# ====================== canonical value encoding (pure, no cargo/lean) ======
# the shape both rust_encode_expr/DiffJson and lean_encode_expr are meant to
# produce for a value of a given type, and its inverse. used to statically
# check the two codegens agree on a shape without running either side.

def canonical_encode(T, v):
    kind = T[0]
    if kind == "bool":
        return bool(v)
    if kind == "int":
        return str(int(v))
    if kind == "tuple":
        return [canonical_encode(t, x) for t, x in zip(T[1], v)]
    if kind in ("array", "slice", "vec"):
        return [canonical_encode(T[1], x) for x in v]
    if kind == "struct":
        return {fn: canonical_encode(ft, v[fn]) for fn, ft in T[2]}
    if kind == "enum":
        vname, args = v
        arg_types = dict(T[2])[vname]
        return {"tag": vname, "args": [canonical_encode(t, x) for t, x in zip(arg_types, args)]}
    if kind == "list_enum":
        _, _, nil_v, cons_v, elem_T = T
        if not v:
            return {"tag": nil_v, "args": []}
        return {"tag": cons_v, "args": [canonical_encode(elem_T, v[0]), canonical_encode(T, v[1:])]}
    if kind == "option":
        return None if v is None else canonical_encode(T[1], v)
    raise Unsupported(f"no canonical encoding for {T!r}")


def canonical_decode(T, j):
    kind = T[0]
    if kind == "bool":
        return bool(j)
    if kind == "int":
        return int(j)
    if kind == "tuple":
        return [canonical_decode(t, x) for t, x in zip(T[1], j)]
    if kind in ("array", "slice", "vec"):
        return [canonical_decode(T[1], x) for x in j]
    if kind == "struct":
        return {fn: canonical_decode(ft, j[fn]) for fn, ft in T[2]}
    if kind == "enum":
        arg_types = dict(T[2])[j["tag"]]
        return (j["tag"], [canonical_decode(t, x) for t, x in zip(arg_types, j["args"])])
    if kind == "list_enum":
        _, _, nil_v, cons_v, elem_T = T
        if j["tag"] == nil_v:
            return []
        return [canonical_decode(elem_T, j["args"][0])] + canonical_decode(T, j["args"][1])
    if kind == "option":
        return None if j is None else canonical_decode(T[1], j)
    raise Unsupported(f"no canonical decoding for {T!r}")


# ====================== comparison ======================

def compare_one(rust_outcome, lean_result):
    """a Rust ok must equal the Lean ok value; a Rust panic must meet a Lean
    fail. a Lean div (ran out of fuel) never agrees with either -- it is a
    translation bug (non-termination) on its own, not a stand-in for fail."""
    rust_ok = "ok" in rust_outcome
    lean_ok = "ok" in lean_result
    if rust_ok and lean_ok:
        return rust_outcome["ok"] == lean_result["ok"]
    if (not rust_ok) and "fail" in lean_result:
        return True
    return False


# ====================== main driver ======================

def run_check(crate_path, inputs_per_function, seed, out_json=None,
              functions=None, overrides=None):
    crate_path = os.path.expanduser(crate_path)
    crate, custom_types, selected, skipped = select_units(crate_path)
    if functions is not None:
        selected = [f for f in selected if f["short_name"] in functions or f["lean_name"] in functions]

    manifest = loader.load_manifest(crate_path)
    rust_src = _rust_source_map(manifest)
    crate_copy = prepare_rust_copy(rust_src)
    out_dir = os.path.join(SCRATCH, "outputs")
    if os.path.exists(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)

    inject_rust_harness(crate_copy, selected, inputs_per_function, seed, "LSS_DIFFCHECK_OUT")
    rc, cargo_out, cargo_err, cargo_timed_out = run_cargo_tests(crate_copy, out_dir)

    server = lean_server.LeanServer(crate_path, lss_config.server_cfg())

    results = {"functions_found": len(selected) + len(skipped),
               "checked": [], "skipped": [{"name": n, "reason": r} for n, r in skipped],
               "rust_timeout": cargo_timed_out, "function_results": {},
               "peak_rss_bytes": 0}

    for fdesc in selected:
        name = fdesc["lean_name"]
        rows = read_rust_rows(out_dir, name)
        entry = {"rust_name": fdesc["rust_name"], "lean_name": name,
                 "inputs": inputs_per_function, "agreements": 0, "disagreements": [],
                 "rust_timeout": False, "lean_timeout": False, "mem_killed": False}
        if rows is None:
            entry["rust_timeout"] = True
            results["function_results"][name] = entry
            continue

        override = (overrides or {}).get(fdesc["rust_name"])
        # setup and eval must be in the same command: each server.check()
        # starts over from the cached *import-only* environment, so a def
        # sent on its own would not still be visible to a later #eval.
        setup = "\n".join(override["setup"]) if override else ""
        call_expr = override["call_expr"] if override else (
            fdesc["short_name"] + " " + " ".join(f"{{a{i}}}" for i in range(len(fdesc["args"]))))
        arg_types = [t for _, t in fdesc["args"]]
        # peak RssAnon is one shared REPL's high-water mark across the whole
        # run, not a per-function cost -- tracked once, at the top level.
        lean_results, r, peak = run_eval_batches(
            server, crate, arg_types, fdesc["ret"], call_expr, rows, setup=setup)
        results["peak_rss_bytes"] = max(results["peak_rss_bytes"], peak)

        if lean_results is None:
            if r is not None and r.mem_killed:
                entry["mem_killed"] = True
            else:
                entry["lean_timeout"] = True
            results["function_results"][name] = entry
            continue

        for row, lr in zip(rows, lean_results):
            ok = compare_one(row["outcome"], lr)
            if ok:
                entry["agreements"] += 1
            else:
                entry["disagreements"].append({
                    "args": row["args"], "rust_outcome": row["outcome"], "lean_result": lr,
                })
        results["checked"].append(name)
        results["function_results"][name] = entry

    server.close()
    lean_server.shutdown_all()

    if out_json:
        with open(out_json, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=2)
    return results


def print_summary(results):
    print(f"functions found: {results['functions_found']}")
    print(f"checked: {len(results['checked'])}")
    print(f"skipped: {len(results['skipped'])}")
    for s in results["skipped"]:
        print(f"  skip {s['name']}: {s['reason']}")
    total_agree = total_disagree = total_rust_to = total_lean_to = total_mem_killed = 0
    for name, entry in results["function_results"].items():
        if entry["rust_timeout"]:
            total_rust_to += 1
            print(f"  {name}: RUST TIMEOUT")
            continue
        if entry["lean_timeout"]:
            total_lean_to += 1
            print(f"  {name}: LEAN TIMEOUT")
            continue
        if entry["mem_killed"]:
            total_mem_killed += 1
            print(f"  {name}: LEAN MEM KILLED")
            continue
        total_agree += entry["agreements"]
        total_disagree += len(entry["disagreements"])
        status = "ok" if not entry["disagreements"] else "DISAGREE"
        print(f"  {name}: inputs={entry['inputs']} agree={entry['agreements']} "
              f"disagree={len(entry['disagreements'])} [{status}]")
        for d in entry["disagreements"][:5]:
            print(f"      args={d['args']} rust={d['rust_outcome']} lean={d['lean_result']}")
    peak_mb = results.get("peak_rss_bytes", 0) / 1024 ** 2
    print(f"total agreements={total_agree} disagreements={total_disagree} "
          f"rust_timeouts={total_rust_to} lean_timeouts={total_lean_to} "
          f"mem_killed={total_mem_killed} "
          f"peak_rss={peak_mb:.0f}MiB (one shared REPL for the whole run)")


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("crate_path")
    ap.add_argument("--inputs", type=int, default=32)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default=None)
    args = ap.parse_args(argv)
    results = run_check(args.crate_path, args.inputs, args.seed, out_json=args.out)
    print_summary(results)
    return 0 if not any(e["disagreements"] for e in results["function_results"].values()) else 1


if __name__ == "__main__":
    sys.exit(main())
