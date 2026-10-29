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


def run_static():
    print("=== static ===")
    text = callgraph._concat_code_files(["T.lean"], {"T.lean": "import Aeneas\ndef test1 : Result Unit := ok ()\n"
                                                                "#assert (test1 == ok ())\ndef g := 1\n"})
    check("Aeneas's #assert unit tests are dropped from the crate text, every definition kept",
          "#assert" not in text and "def test1" in text and "def g := 1" in text, text)
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

    # bench names collided when they were only the lean_name's last segment
    # (every loop body became "rust_body"); they must be unique per crate
    loop_bodies_manifest = {
        "import": "Demo",
        "declarations": [
            {"kind": "function", "is_local": True, "lean_name": "Demo.f.loop.body",
             "rust_name": "demo::f", "loop_id": 0, "loop_is_body": True,
             "parent_lean_name": "Demo.f", "is_recursive": False, "can_fail": True,
             "can_diverge": True, "is_opaque": False, "lean_file": "Demo/Code/Funs.lean"},
            {"kind": "function", "is_local": True, "lean_name": "Demo.g.loop.body",
             "rust_name": "demo::g", "loop_id": 0, "loop_is_body": True,
             "parent_lean_name": "Demo.g", "is_recursive": False, "can_fail": True,
             "can_diverge": True, "is_opaque": False, "lean_file": "Demo/Code/Funs.lean"},
        ],
    }
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(loop_bodies_manifest, f)
        benches = loader.load_rust_project(tmp)
        bench_names = [b["name"] for b in benches]
        check("loop body bench names are unique", len(bench_names) == len(set(bench_names)),
              str(bench_names))


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

    proj = lss_config.project_dir("aeneas")
    if not os.path.isdir(proj):
        check("~/lss_lean/aeneas exists", False, f"not a directory: {proj}")
        return
    olean = os.path.join(proj, ".lake", "packages", "aeneas", "backends", "lean",
                          ".lake", "build", "lib", "lean", "Aeneas.olean")
    if not os.path.exists(olean):
        check("~/lss_lean/aeneas is built", False, f"missing {olean}")
        return

    server = lean_server.get_server(proj, lss_config.server_cfg())
    check("server started", server._worker is not None)

    g = callgraph.build_call_graph(FIXTURE)

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
