import os
import sys
import random
import json
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

import callgraph
import loader

static = "--static" in sys.argv
fails = []


def check(name, ok, msg=""):
    if ok:
        print(f"  pass: {name}")
    else:
        print(f"  FAIL: {name}" + (f" ({msg})" if msg else ""))
        fails.append(name)


print(f"mode {'static' if static else 'full'}")


def _hand_units():
    text = "\n".join(f"line{i}" for i in range(1, 10))
    units = [
        {"name": "even", "callees": ["odd"], "generic": False, "range": [1, 1], "no_eqn": False},
        {"name": "odd", "callees": ["even"], "generic": False, "range": [2, 2], "no_eqn": False},
        {"name": "leaf", "callees": [], "generic": False, "range": [3, 3], "no_eqn": False},
        {"name": "loop_body", "callees": ["leaf"], "generic": False, "range": [4, 4], "no_eqn": False},
        {"name": "loop", "callees": ["loop_body"], "generic": False, "range": [5, 5], "no_eqn": False},
        {"name": "parent", "callees": ["loop"], "generic": False, "range": [6, 6], "no_eqn": False},
    ]
    manifest_info = {
        "even": {"is_recursive": True},
        "odd": {"is_recursive": True},
        "leaf": {"is_recursive": False, "can_diverge": False},
        "loop_body": {"is_recursive": False, "loop_id": 0, "loop_is_body": True,
                       "parent_lean_name": "parent", "can_diverge": True},
        "loop": {"is_recursive": False, "loop_id": 0, "loop_is_body": False,
                 "parent_lean_name": "parent", "can_diverge": True},
        "parent": {"is_recursive": False, "can_diverge": True},
    }
    return text, units, manifest_info


def _write(root, rel, text):
    path = os.path.join(root, *rel.split("/"))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return path


def run_static_layout():
    """a crate committed with its own Lean project (SymCrypt's shape): Code files that
    import modules outside Code, an Aeneas template beside them, a namespace that is
    not the module root."""
    with tempfile.TemporaryDirectory() as tmp:
        lean_dir = os.path.join(tmp, "their", "lean")
        funs = _write(lean_dir, "Demo/Code/Funs.lean", "import Aeneas\nimport Demo.Code.Types\nimport Helper.Opens\n"
                      "open Aeneas Aeneas.Std Result\nnamespace demo\n/-- [demo::f] -/\ndef f (x : Std.U32) : "
                      "Result Std.U32 := ok x\nend demo\n")
        types = _write(lean_dir, "Demo/Code/Types.lean", "import Aeneas Helper.Deep.Model -- the model\nnamespace demo\n"
                       "structure P where\n  a : Std.U32\nend demo\n")
        _write(lean_dir, "Demo/Code/FunsExternal_Template.lean", "-- This is a template file: rename it\n"
               "import Aeneas\naxiom demo.dup : Nat\n")
        external = _write(lean_dir, "Demo/Code/FunsExternal.lean", "import Aeneas\naxiom demo.dup : Nat\n")
        stand_in = _write(lean_dir, "Demo/Code/TypesExternal_Template.lean", "-- This is a template file\n"
                          "import Aeneas\naxiom demo.ty : Type\n")
        opens = _write(lean_dir, "Helper/Opens.lean", "import Aeneas\nopen Aeneas Std\ndef Helper.h : Nat := 1\n")
        model = _write(lean_dir, "Helper/Deep/Model.lean", "import Aeneas\npublic import Mathlib.Data.ZMod.Defs\n"
                       "def Helper.Deep.m : Nat := 2\n")
        funs, types, external, stand_in, opens, model = map(os.path.realpath, (funs, types, external, stand_in,
                                                                                opens, model))
        ordered, texts, outside = callgraph._crate_files(lean_dir, "Demo")
        check("a crate's code is its Code files and every module of its Lean folder they import, callees first",
              ordered == [model, types, opens, funs, external, stand_in],
              str([os.path.relpath(p, lean_dir) for p in ordered]))
        check("an Aeneas template is left out once its file is written, and stands in for it until then",
              not any(p.endswith("FunsExternal_Template.lean") for p in ordered) and stand_in in ordered)
        text = callgraph._concat_code_files(ordered, texts, outside)
        check("import lines are read as Lean reads them: several modules, a comment, `public import`",
              outside == ["Aeneas", "Mathlib.Data.ZMod.Defs"], str(outside))
        check("a module imported from outside the Lean folder is imported by the joined text, and no file's own "
              "import line is left in it", text.startswith("import Aeneas\nimport Mathlib.Data.ZMod.Defs\nsection\n")
              and text.count("import ") == 2, text[:300])
        proj = os.path.join(tmp, "project")
        os.makedirs(proj)
        manifest = {"import": "Demo", "namespace": "demo", "lean_root": "../their/lean",
                    "declarations": [{"kind": "function", "is_local": True, "lean_name": "demo.f",
                                      "rust_name": "demo::f"}]}
        check("a manifest names the crate's Lean folder, module root and namespace",
              loader.crate_layout(proj, manifest) == (lean_dir, "Demo", "demo"),
              str(loader.crate_layout(proj, manifest)))
        check("a crate our translation writes is all three at once: its project folder and its import",
              loader.crate_layout(proj, {"import": "Demo"}) == (proj, "Demo", "Demo"))
        with open(os.path.join(proj, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f)
        b = loader.load_rust_project(proj)
        check("its functions are named in its namespace, their code read from its Lean folder",
              [x["func_name"] for x in b] == ["f"] and "def f (x : Std.U32)" in b[0]["func_source"]
              and "open demo" in b[0]["lean_preamble"], str([(x["func_name"], x["lean_preamble"]) for x in b]))
        import lean

        class _G:
            crate_text = "import Aeneas\nsection\nset_option maxHeartbeats 1000000\ndef x := 1\nend"
        real = callgraph.for_project
        callgraph.for_project = lambda p: _G()
        try:
            env, _ = lean.LeanChecker()._aeneas_env_text(proj)
        finally:
            callgraph.for_project = real
        after = env[len(_G.crate_text):]
        check("the crate env sets Aeneas's options and opens again after the crate's own files",
              "set_option maxHeartbeats 1000000\n" in after and "set_option maxRecDepth 2048\n" in after
              and "set_option linter.unusedVariables false\n" in after
              and "open Aeneas Aeneas.Std Result ControlFlow Error\n" in after, after[:400])


# what lean/unit_graph.lean's dumpDecls says of a crate in Aeneas's shape (its output
# on a hand-written crate, by the pinned Lean, with the doc comments Aeneas writes):
# the Code file's lines are 36-51 of the joined text, an imported model's 2-35
DECLS = {
    "decls": [
        {"name": "demo.f", "doc": "[demo::f]:\nSource: 'src/lib.rs' ", "returns_result": True, "opaque": False,
         "noncomputable": False, "diverges": False},
        {"name": "demo.f_loop", "doc": "[demo::f]: loop 0:\nSource: 'src/lib.rs' ", "returns_result": True,
         "opaque": False, "noncomputable": False, "diverges": True},
        {"name": "demo.ext", "doc": "[demo::ext] ", "returns_result": True, "opaque": True, "noncomputable": False,
         "diverges": False},
        {"name": "demo.g", "doc": "[demo::g] ", "returns_result": True, "opaque": False, "noncomputable": True,
         "diverges": False},
        {"name": "demo.C", "doc": "[demo::C] ", "returns_result": False, "opaque": False, "noncomputable": False,
         "diverges": False},
        {"name": "demo.w_loop.body", "doc": "[demo::f]: loop body 1: ", "returns_result": True, "opaque": False,
         "noncomputable": False, "diverges": False},
        {"name": "demo.model", "doc": "[demo::model]: ", "returns_result": True, "opaque": False,
         "noncomputable": False, "diverges": False},
        {"name": "root_ext", "doc": "[demo::root_ext]: ", "returns_result": True, "opaque": True,
         "noncomputable": False, "diverges": False},
        {"name": "demo.Insts.Foo", "doc": "Trait implementation: [demo::{impl Foo for [u8; 4]}] ",
         "returns_result": False, "opaque": False, "noncomputable": False, "diverges": False}],
    "units": [
        {"name": "demo.f", "callees": ["demo.f_loop"], "generic": False, "range": [37, 38], "no_eqn": False},
        {"name": "demo.f_loop", "callees": ["demo.f_loop"], "generic": False, "range": [39, 41], "no_eqn": False},
        {"name": "demo.ext", "callees": [], "generic": False, "range": [42, 42], "no_eqn": True},
        {"name": "demo.g", "callees": ["demo.ext"], "generic": False, "range": [43, 43], "no_eqn": False},
        {"name": "demo.C", "callees": [], "generic": False, "range": [44, 44], "no_eqn": False},
        {"name": "demo.w_loop.body", "callees": [], "generic": False, "range": [46, 46], "no_eqn": False},
        {"name": "demo.model", "callees": [], "generic": False, "range": [5, 6], "no_eqn": False},
        {"name": "root_ext", "callees": [], "generic": False, "range": [48, 48], "no_eqn": True},
        {"name": "demo.Insts.Foo", "callees": [], "generic": False, "range": [45, 45], "no_eqn": False}]}


def run_static_manifest():
    check("a Rust name and loop are read off Aeneas's doc comment",
          callgraph._aeneas_doc("[symcrust::a::f]:\nSource: 'x.rs'") == ("symcrust::a::f", None, False)
          and callgraph._aeneas_doc("[x::f]: loop 1:\nSource") == ("x::f", 1, False)
          and callgraph._aeneas_doc("[x::f]: loop body 1:\nSource") == ("x::f", 1, True)
          and callgraph._aeneas_doc("no name") == ("", None, False))
    check("a trait implementation's Rust name keeps the brackets inside it",
          callgraph._aeneas_doc("Trait implementation: [demo::{impl Foo for [u8; 4]}] ")
          == ("demo::{impl Foo for [u8; 4]}", None, False))
    with tempfile.TemporaryDirectory() as tmp:
        lean_dir = os.path.join(tmp, "lean")
        _write(lean_dir, "Demo/Code/Funs.lean", "import Aeneas\nimport Spec.Model\nnamespace demo\n" + "\n" * 12
               + "end demo\n")
        _write(lean_dir, "Spec/Model.lean", "import Aeneas\nnamespace demo\n" + "\n" * 30 + "end demo\n")
        sent = []

        class _Server:
            def check(self, code, timeout=None):
                sent.append((code, timeout))
                return type("R", (), {"stderr": "x:1:0: warning: LSS_DECLS " + json.dumps(DECLS), "stdout": ""})()
        real = callgraph._lean_server.get_server
        callgraph._lean_server.get_server = lambda d: _Server()
        try:
            m = callgraph.manifest_from_lean(tmp, "lean", "Demo", "demo")
        finally:
            callgraph._lean_server.get_server = real
        check("the manifest is read in one Lean command, with the crate build's time limit",
              len(sent) == 1 and sent[0][0].rstrip().endswith("#eval LssUnitGraph.dumpDecls .anonymous")
              and sent[0][1] == callgraph.CRATE_BUILD_TIMEOUT, str([s[1] for s in sent]))
        by = {d["lean_name"]: d for d in m["declarations"]}
        check("a definition returning a Result is a function, others a constant or a trait implementation",
              {n: d["kind"] for n, d in by.items()} == {"demo.f": "function", "demo.f_loop": "function",
                                                        "demo.ext": "function", "demo.g": "function",
                                                        "demo.C": "global", "demo.Insts.Foo": "trait_impl",
                                                        "demo.w_loop.body": "function", "root_ext": "function"},
              str(by))
        check("an axiom outside the crate's namespace (SymCrypt's, at the root) is read too",
              by.get("root_ext", {}).get("is_opaque") is True, str(by.get("root_ext")))
        check("a definition in a module the crate imports, though in its namespace, is not the crate's",
              "demo.model" not in by)
        body = by.get("demo.w_loop.body", {})
        check("the body a pinned-Aeneas loop iterates is a loop body (never a unit), its parent the function",
              body.get("loop_is_body") and body.get("loop_id") == 1 and body.get("parent_lean_name") == "demo.f"
              and not by["demo.f_loop"]["loop_is_body"], str(body))
        loop = by["demo.f_loop"]
        check("a loop gets its id, its parent function, recursion and divergence",
              loop["loop_id"] == 0 and loop["parent_lean_name"] == "demo.f" and loop["is_recursive"]
              and loop["can_diverge"] and not by["demo.f"]["is_recursive"], str(loop))
        check("an axiom has no body, a definition calling one cannot run",
              by["demo.ext"]["is_opaque"] and not by["demo.g"]["is_opaque"] and by["demo.g"]["noncomputable"]
              and not by["demo.f"]["noncomputable"], str(by["demo.g"]))
        check("the manifest names the crate's Lean folder, module root and namespace",
              (m["import"], m["namespace"], m["lean_root"]) == ("Demo", "demo", "lean"))
        with open(os.path.join(tmp, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(m, f)
        names = sorted(b["lean_name"] for b in loader.load_rust_project(tmp))
        check("the loader reads it as any manifest: the functions are the units, a loop body not one",
              names == ["demo.ext", "demo.f", "demo.f_loop", "demo.g", "root_ext"], str(names))


def run_static():
    print("=== static ===")
    text = callgraph._concat_code_files(["T.lean"], {"T.lean": "import Aeneas\ndef test1 : Result Unit := ok ()\n"
                                                                "#assert (test1 == ok ())\ndef g := 1\n"})
    check("Aeneas's #assert unit tests are dropped from the crate text, every definition kept",
          "#assert" not in text and "def test1" in text and "def g := 1" in text, text)
    # the header Aeneas writes (Translate.ml: `noncomputable section` at the top of
    # the file, then the namespace), a body that closes only its namespace
    aeneas_file = ("import Aeneas\nset_option maxRecDepth 2048\n\n/- You can remove the following line by "
                   "using the CLI option `-all-computable`: -/\nnoncomputable section\n\nnamespace c\n"
                   "/-- doc\nend of a doc line\nsection inside a comment -/\ndef f (x : Nat) : Nat :=\n"
                   "  match x with\n  | _ => x\nmutual\ndef e : Nat → Bool\n  | _ => true\nend\n-- end\nend c\n")
    text = callgraph._concat_code_files(["A.lean", "B.lean"], {"A.lean": aeneas_file, "B.lean": "def g := 1\n"})
    check("a file's open `noncomputable section` is closed where the file ends, before the next file",
          text.endswith("end c\nend\nend\nsection\ndef g := 1\nend"), text)
    text = callgraph._concat_code_files(["A.lean", "B.lean"], {"A.lean": "import Aeneas\nopen Aeneas Std\ndef a := 1\n",
                                                               "B.lean": "def b := Slice\n"})
    check("each joined file is its own section, so its top-level open and options end with it",
          text == "import Aeneas\nsection\nopen Aeneas Std\ndef a := 1\nend\nsection\ndef b := Slice\nend", text)
    run_static_layout()
    run_static_manifest()
    check("scopes the file closes itself, or that only a comment opens, are not closed again",
          callgraph._open_scopes(aeneas_file.replace("noncomputable section\n", "")) == [], text)
    check("open scopes close innermost first",
          callgraph._open_scopes("noncomputable section\nnamespace a\nsection s\nmutual\n") ==
          ["end", "end s", "end a", "end"])
    check("a comment or string mark inside a line comment or a string opens no comment",
          callgraph._open_scopes("-- a/-b\nnoncomputable section\ndef s := \"/- x\"\nsection") == ["end", "end"])
    check("a dotted name is one scope per component, as Lean counts them",
          callgraph._open_scopes("namespace A\nnamespace B\nend A.B") == []
          and callgraph._open_scopes("namespace A.B") == ["end B", "end A"])
    sent = []

    class _Server:
        def check(self, code, timeout=None):
            sent.append(timeout)
            return type("R", (), {"stderr": 'warning: LSS_UNITS {"units": []}', "stdout": ""})()
    real = callgraph._lean_server.get_server
    callgraph._lean_server.get_server = lambda d: _Server()
    try:
        callgraph._run_unit_graph("import Aeneas", ["a"])
    finally:
        callgraph._lean_server.get_server = real
    check("the unit graph is sent with the crate env's own time limit, not the server's 30 s default",
          sent == [callgraph.CRATE_BUILD_TIMEOUT] and callgraph.CRATE_BUILD_TIMEOUT >= 600, str(sent))
    text, units, manifest_info = _hand_units()
    g = callgraph.CallGraph(text, units, manifest_info=manifest_info)

    multi_sccs = [s for s in g.sccs if len(s) > 1]
    check("scc {even,odd}", len(multi_sccs) == 1 and set(multi_sccs[0]) == {"even", "odd"},
          str(g.sccs))

    order = g.topo_sorted_names()
    pos = {n: i for i, n in enumerate(order)}
    check("callees before callers (leaf before loop_body)", pos["leaf"] < pos["loop_body"])
    check("loop body before loop before parent",
          pos["loop_body"] < pos["loop"] < pos["parent"], str(order))

    stable = True
    for seed in range(5):
        shuffled = units[:]
        random.Random(seed).shuffle(shuffled)
        g2 = callgraph.CallGraph(text, shuffled, manifest_info=manifest_info)
        if g2.topo_sorted_names() != order:
            stable = False
    check("order identical across 5 shuffled input orders", stable)

    check("loop_is_body copied from manifest",
          g.loop_is_body("loop_body") is True and g.loop_is_body("loop") is False)
    check("parent_lean_name copied from manifest", g.parent_lean_name("loop_body") == "parent")
    check("can_diverge copied from manifest",
          g.can_diverge("loop") is True and g.can_diverge("leaf") is False)
    check("recursive flag matches manifest (no disagreement)", g.manifest_disagreements == [])

    benches = [
        {"name": "x", "is_local": True, "kind": "function", "loop_id": None, "loop_is_body": None},
        {"name": "y", "is_local": True, "kind": "function", "loop_id": 0, "loop_is_body": True},
        {"name": "z", "is_local": True, "kind": "function", "loop_id": 0, "loop_is_body": False},
    ]
    without_loops = [b for b in benches
                      if not (b.get("loop_is_body") or b.get("loop_id") is not None)]
    check("include_loops=false drops exactly the loop functions",
          {b["name"] for b in without_loops} == {"x"}, str(without_loops))

    flat_manifest = {
        "declarations": [
            {"kind": "function", "is_local": True, "lean_name": "Demo.f", "rust_name": "demo::f",
             "loop_id": None, "loop_is_body": None, "parent_lean_name": None,
             "is_recursive": False, "can_fail": True, "can_diverge": False, "is_opaque": False,
             "lean_file": "Demo/Code/Funs.lean"},
        ]
    }
    raw_manifest = {
        "functions": [
            {"def_id": 0, "lean_name": "Demo.f", "rust_name": "demo::f", "is_local": True,
             "source": {"file": "x.rs", "begin_line": 1, "end_line": 1},
             "is_opaque": False, "can_fail": True, "can_diverge": False, "is_rec": False,
             "reducible": False, "lean_file": "Demo/Code/Funs.lean"},
        ],
    }
    nf = loader.normalize_declarations(flat_manifest)
    nr = loader.normalize_declarations(raw_manifest)
    check("both manifest shapes normalize to the same benches", nf == nr, f"{nf} != {nr}")

    # bench names collided when they were only the lean_name's last segment; they
    # must be unique per crate. a loop body is never a unit: it is proved with its loop
    def loop_decl(name, parent, body):
        return {"kind": "function", "is_local": True, "lean_name": name, "rust_name": "demo::" + parent,
                "loop_id": 0, "loop_is_body": body, "parent_lean_name": "Demo." + parent,
                "is_recursive": not body, "can_fail": True, "can_diverge": True, "is_opaque": False,
                "lean_file": "Demo/Code/Funs.lean"}
    loops_manifest = {
        "import": "Demo",
        "declarations": [loop_decl("Demo.f_loop", "f", False), loop_decl("Demo.f_loop.body", "f", True),
                         loop_decl("Demo.g_loop", "g", False), loop_decl("Demo.g_loop.body", "g", True)],
    }
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(loops_manifest, f)
        benches = loader.load_rust_project(tmp)
        bench_names = [b["name"] for b in benches]
        check("loop bench names are unique", len(bench_names) == len(set(bench_names)), str(bench_names))
        check("loop bodies are not units, their loops are",
              sorted(b["lean_name"] for b in benches) == ["Demo.f_loop", "Demo.g_loop"], str(bench_names))


FIXTURE = '''
def inc (n : Nat) : Nat := n + 1

def twice (n : Nat) : Nat := inc (inc n)

mutual
def isEv : Nat -> Bool
  | 0 => true
  | n+1 => isOd n
def isOd : Nat -> Bool
  | 0 => false
  | n+1 => isEv n
end

def structRec : Nat -> Nat
  | 0 => 0
  | n+1 => structRec n + 1

def pf (n : Nat) : Nat :=
  if n = 0 then 0 else pf (n - 1)
partial_fixpoint

def wrap {T : Type} (x : T) : T := x

structure Pair where
  a : Nat
  b : Nat

def swapPair (p : Pair) : Pair := { a := p.b, b := p.a }
'''


def run_full():
    print("=== full ===")
    import lss_config
    import lean_server

    # Lean-native code runs where every Lean-native text does: the lean-native project
    proj = lss_config.project_dir("lean-native")
    if not os.path.isdir(proj):
        check("~/lss_lean/lean-native exists", False, f"not a directory: {proj}")
        return

    server = lean_server.get_server(proj, lss_config.server_cfg())
    check("server started", server._worker is not None)

    g = callgraph.build_call_graph(FIXTURE)
    started = [os.path.abspath(p) for p in lean_server.all_stats()]
    check("a Lean-native unit graph runs in the lean-native project, never the aeneas one",
          os.path.abspath(lss_config.project_dir("aeneas")) not in started, str(started))

    check("crate_text excludes the unit-graph driver",
          "LssUnitGraph" not in g.crate_text, g.crate_text[-200:])

    check("inc callees", g.callees("inc") == set())
    check("twice callees", g.callees("twice") == {"inc"})
    check("isEv callees", g.callees("isEv") == {"isOd"})
    check("isOd callees", g.callees("isOd") == {"isEv"})
    check("swapPair callees (structure projection use)",
          g.callees("swapPair") == {"Pair.a", "Pair.b"})

    multi_sccs = [s for s in g.sccs if len(s) > 1]
    check("scc {isEv,isOd}", len(multi_sccs) == 1 and set(multi_sccs[0]) == {"isEv", "isOd"},
          str(g.sccs))

    check("structRec self-edge", "structRec" in g.callees("structRec"))
    check("structRec recursive", g.recursive("structRec"))
    check("pf (partial_fixpoint) self-edge", "pf" in g.callees("pf"))
    check("pf recursive", g.recursive("pf"))
    check("inc not recursive", not g.recursive("inc"))

    check("generic set only on wrap",
          g.generic("wrap") and not any(g.generic(n) for n in g.names if n != "wrap"))

    check("def_text(inc) matches its source line",
          (g.def_text("inc") or "").strip() == "def inc (n : Nat) : Nat := n + 1",
          repr(g.def_text("inc")))

    run_full_layout()
    lean_server.shutdown_all()
    check("no lean process left after shutdown", server._worker is None)


MINI_TYPES = """import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace demo
/-- Trait declaration: [demo::Tr] -/
structure Tr (Self : Type) where
  f : Self → Result Self
end demo
"""

MINI_FUNS = """import Aeneas
import Demo.Code.Types
import Helper.Opens
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace demo

/-- [demo::f] -/
def f (s : Slice Std.U8) : Result Std.Usize := ok 0#usize

/-- [demo::count]: loop 0:
    Source: 'src/lib.rs', lines 1:0-1:1 -/
def count_loop (i : Std.U32) (n : Std.U32) : Result Std.U32 := do
  if i < n then
    let i1 ← i + 1#u32
    count_loop i1 n
  else ok i
partial_fixpoint

/-- [demo::count] -/
def count (n : Std.U32) : Result Std.U32 := count_loop 0#u32 n

/-- [demo::ext] -/
axiom ext : Std.U32 → Result Std.U32

/-- [demo::uses_ext] -/
def uses_ext (x : Std.U32) : Result Std.U32 := ext x

/-- [demo::sum]: loop body 0:
    Source: 'src/lib.rs', lines 2:0-2:1 -/
def sum_loop.body (p : Std.U32 × Std.U32) : Result (ControlFlow (Std.U32 × Std.U32) Std.U32) := do
  let (i, n) := p
  if i < n then
    let i1 ← i + 1#u32
    ok (.cont (i1, n))
  else ok (.done i)

/-- [demo::sum]: loop 0:
    Source: 'src/lib.rs', lines 2:0-2:1 -/
def sum_loop (i n : Std.U32) : Result Std.U32 := loop sum_loop.body (i, n)

/-- [demo::sum] -/
def sum (n : Std.U32) : Result Std.U32 := sum_loop 0#u32 n

/-- [demo::K] -/
def K : Std.U32 := 3#u32

/-- Trait implementation: [demo::{impl demo::Tr for u32}] -/
@[reducible]
def U32.Insts.DemoTr : Tr Std.U32 := { f := fun x => ok x }

end demo

/-- [demo::root_ext]: an axiom at the root, as SymCrypt's FunsExternal declares them -/
axiom root_ext : Std.U32 → Result Std.U32
"""


def run_full_layout():
    """a crate in SymCrypt's shape, in small: committed with its own Lean folder and no
    manifest, its namespace not its module root, and a module it imports opening
    `Aeneas Std`, which opens Lean's own `Std` too (joined, `Slice` in the next file
    was ambiguous)."""
    import lean
    with tempfile.TemporaryDirectory() as tmp:
        lean_dir = os.path.join(tmp, "lean")
        _write(lean_dir, "Helper/Opens.lean", "import Aeneas\nopen Aeneas Std\ndef Helper.h : Nat := 1\n"
               "namespace demo\n/-- [demo::model]: a model in the crate's namespace -/\n"
               "def model (x : Aeneas.Std.U32) : Aeneas.Std.Result Aeneas.Std.U32 := .ok x\nend demo\n")
        _write(lean_dir, "Demo/Code/Types.lean", MINI_TYPES)
        _write(lean_dir, "Demo/Code/Funs.lean", MINI_FUNS)
        proj = os.path.join(tmp, "project")
        os.makedirs(proj)
        try:
            m = callgraph.manifest_from_lean(proj, "../lean", "Demo", "demo")
        except RuntimeError as e:
            m = {"declarations": [], "error": str(e)[:600]}
        by = {d["lean_name"]: d for d in m["declarations"]}
        check("a module's `open Aeneas Std` does not reach the files after it: the crate is read",
              "demo.f" in by, m.get("error", str(sorted(by))))
        check("its manifest is read off its code: functions, a constant, a trait implementation",
              {n: d["kind"] for n, d in by.items()} == {
                  "demo.f": "function", "demo.count_loop": "function", "demo.count": "function",
                  "demo.ext": "function", "demo.uses_ext": "function", "demo.K": "global",
                  "demo.U32.Insts.DemoTr": "trait_impl", "demo.sum_loop.body": "function",
                  "demo.sum_loop": "function", "demo.sum": "function", "root_ext": "function"}, str(sorted(by)))
        sl, sb = by.get("demo.sum_loop", {}), by.get("demo.sum_loop.body", {})
        check("a loop of the pinned Aeneas's shape (`loop` over a body): it can diverge, its body is a loop body",
              sl.get("can_diverge") and sl.get("loop_id") == 0 and not sl.get("loop_is_body")
              and sb.get("loop_is_body") and sb.get("parent_lean_name") == "demo.sum", str((sl, sb)))
        loop = by.get("demo.count_loop", {})
        check("a partial_fixpoint loop: its id, parent, recursion and divergence",
              loop.get("loop_id") == 0 and loop.get("parent_lean_name") == "demo.count" and loop.get("is_recursive")
              and loop.get("can_diverge") and not by.get("demo.count", {}).get("can_diverge", True), str(loop))
        check("an axiom has no body, and a function calling it cannot run",
              by.get("demo.ext", {}).get("is_opaque") and by.get("demo.uses_ext", {}).get("noncomputable")
              and not by.get("demo.count", {}).get("noncomputable", True), str(by.get("demo.uses_ext")))
        with open(os.path.join(proj, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(m, f)
        try:
            names = callgraph.for_project(proj).names
        except RuntimeError as e:
            names = str(e)[:400]
        check("with it the crate's unit graph runs", isinstance(names, set) and "demo.count_loop" in names, str(names))
        err = lean.crate_env_error(lean.LeanChecker(), proj)
        check("and its crate env builds in its own namespace", not err, str(err)[:400])


if static:
    run_static()
else:
    run_full()

if fails:
    print(f"\n{len(fails)} FAILURE(S): {fails}")
    sys.exit(1)
print("\nall pass")
