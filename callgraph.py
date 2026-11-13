import os
import glob
import json
import hashlib
import re

import networkx as nx

import lss_config as _lss_config
import lean_server as _lean_server
import loader as _loader
from events import with_context

_DRIVER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "unit_graph.lean")

# a crate's code is elaborated whole, once for its unit graph and once for its env
# (lean._aeneas_build_env), each given this long: SymCrypt's Code.Funs alone takes
# 32 s, past the server's 30 s default for a command
CRATE_BUILD_TIMEOUT = 600

_PROJECT_CACHE = {}
_SOURCE_CACHE = {}


def _driver_text():
    with open(_DRIVER_PATH, encoding="utf-8") as f:
        return f.read()


def _names_literal(names):
    if names is None:
        return "none"
    return "(some [" + ", ".join(f"`{n}" for n in names) + "])"


@with_context(layer="unitgraph")
def _run_unit_graph(code_text, names, project="aeneas"):
    """send code_text through a pinned project's server; parse the LSS_UNITS line."""
    full = code_text + "\n" + _driver_text() + f"\n#eval LssUnitGraph.dumpUnits {_names_literal(names)}\n"
    r = _lean_server.get_server(_lss_config.project_dir(project)).check(full, timeout=CRATE_BUILD_TIMEOUT)
    for line in (r.stderr or "").splitlines():
        if "LSS_UNITS " in line:
            return json.loads(line.split("LSS_UNITS ", 1)[1])
    raise RuntimeError("unit graph: no LSS_UNITS line from lean:\n" + (r.stderr or r.stdout or "(no output)"))


# an import line as Lean 4.31 reads one: several modules, a trailing comment, and the
# module system's `public` / `private` / `meta` and `all`
_IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.*?)\s*(?:--.*)?$")


def _imports(text):
    """the modules a file's import lines name."""
    return [m for line in text.splitlines() if (i := _IMPORT.match(line))
            for m in i.group(1).split() if m != "all"]


def _crate_files(folder, root):
    """(a crate's code files, callees first, their texts, the modules they import from
    outside `folder`), as Lean builds them: its <root>/Code/*.lean files and every
    module of `folder` they import, at any depth (SymCrypt's Code files import its
    hardware models and Spec files; a crate our translation writes imports only its own
    Code files and Aeneas). Aeneas writes an `X_Template.lean` for a person to fill in
    and rename to X.lean ("This is a template file: rename it to ..."): once X.lean is
    written the template is left out (joined, its axioms would define X's names twice);
    until then it stands in for X, its holes axioms. paths are real paths, so a file
    reached two ways is joined once."""
    code_dir = os.path.join(folder, root, "Code")
    paths = sorted(os.path.realpath(p) for p in glob.glob(os.path.join(code_dir, "*.lean"))
                   if not (p.endswith("_Template.lean") and os.path.isfile(p[:-len("_Template.lean")] + ".lean")))
    texts, outside = {}, []
    prefix = f"{root}.Code."

    def stem(p):
        return os.path.splitext(os.path.basename(p))[0]

    def resolve(module):
        p = os.path.join(folder, *module.split(".")) + ".lean"
        if os.path.isfile(p):
            return os.path.realpath(p)
        if module.startswith(prefix):  # a Code file named by a prefix of its stem
            target = module[len(prefix):]
            return next((p for p in paths if stem(p).startswith(target)), None)
        if module not in outside:
            outside.append(module)
        return None

    ordered, seen = [], set()

    def visit(p):
        if p in seen:
            return
        seen.add(p)
        with open(p, encoding="utf-8") as f:
            texts[p] = f.read()
        for dep in sorted({d for d in map(resolve, _imports(texts[p])) if d is not None} - {p}):
            visit(dep)
        ordered.append(p)

    for p in paths:
        visit(p)
    return ordered, texts, outside


_SCOPE_OPEN = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:(?:public|private)\s+)?(?:noncomputable\s+)?section\b\s*([^\s-]*)"
                         r"|namespace\s+(\S+)|mutual\b")


def _open_scopes(text):
    """the `end` lines that close the scopes `text` leaves open, innermost first.
    a scope is a `namespace X`, a `[noncomputable] section [X]` or a `mutual`
    block, each opened and closed by a command at the start of a line, outside a
    comment or string. a dotted name opens one scope per component, and
    `end A.B` closes as many, as Lean counts them."""
    stack, depth = [], 0
    for line in text.splitlines():
        starts_outside, code, i, in_str = depth == 0, [], 0, False
        while i < len(line):  # the line's text outside comments and strings
            if in_str:
                in_str = line[i] != '"' or line[i - 1] == "\\"
                i += 1
            elif line.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif depth:
                depth, i = (depth - 1, i + 2) if line.startswith("-/", i) else (depth, i + 1)
            elif line.startswith("--", i):
                break
            else:
                in_str = line[i] == '"'
                code.append(line[i])
                i += 1
        if not starts_outside:
            continue
        cmd = "".join(code)
        m = _SCOPE_OPEN.match(cmd)
        if m:
            name = m.group(1) or m.group(2)
            stack += [f"end {c}" for c in name.split(".")] if name else ["end"]
        elif (e := re.match(r"end\b\s*([^\s-]*)", cmd)) and stack:
            del stack[len(stack) - min(len(stack), len(e.group(1).split(".")) if e.group(1) else 1):]
    return stack[::-1]


def _concat_code_files(ordered, texts, outside=()):
    """import Aeneas and the modules the files import from outside their folder
    (_crate_files), then each file's body with its own import lines and Aeneas's
    `#assert` unit tests stripped: a test runs code, it defines nothing a spec
    needs, and Aeneas can place one before the function it calls. a Lean file
    starts afresh and its end closes the scopes it left open; joined, the next file
    would be read inside them (Aeneas opens a `noncomputable section` it never
    closes, which made every definition after the crate noncomputable) and under
    its top-level `open`, `set_option` and `local` commands (SymCrypt's `open Aeneas
    Std` opens Lean's own `Std` too, and `Slice` in the next file was ambiguous). so
    each file is its own `section`, its open scopes closed where it ends."""
    parts = ["import " + m for m in dict.fromkeys(["Aeneas", *outside])]
    for p in ordered:
        body = "\n".join(l for l in texts[p].splitlines()
                         if not (_IMPORT.match(l) or l.strip().startswith("#assert")))
        parts.append("\n".join(["section", body] + _open_scopes(body) + ["end"]))
    return "\n".join(parts)


class CallGraph:
    def __init__(self, text, units, manifest_info=None):
        self._text = text
        self._lines = text.splitlines()
        self._manifest_info = manifest_info or {}
        self.lean_version = None
        self.aeneas_version = None
        self.charon_version = None
        self.crate: str | None = None
        self.project_path = None
        self._callees = {}
        self._generic = {}
        self._ranges = {}
        self._no_eqn = {}
        for u in units:
            n = u["name"]
            self._callees[n] = set(u["callees"])
            self._generic[n] = u["generic"]
            self._ranges[n] = tuple(u["range"]) if u.get("range") else None
            self._no_eqn[n] = u["no_eqn"]
        self._names = set(self._callees)

        g = nx.DiGraph()
        g.add_nodes_from(self._names)
        for n, cs in self._callees.items():
            for c in cs:
                if c in self._names:
                    g.add_edge(n, c)
        self._graph = g

        self._sccs = [frozenset(s) for s in nx.strongly_connected_components(g)]
        self._scc_idx = {}
        for i, scc in enumerate(self._sccs):
            for n in scc:
                self._scc_idx[n] = i

        members = [set(s) for s in self._sccs]
        cond = nx.condensation(g, scc=members)
        rev = cond.reverse(copy=False)
        key_of = {i: min(cond.nodes[i]["members"]) for i in cond.nodes}
        order = nx.lexicographical_topological_sort(rev, key=lambda i: key_of[i])
        self._topo = []
        for i in order:
            self._topo.extend(sorted(cond.nodes[i]["members"]))

        self._callers = {n: set() for n in self._names}
        for n, cs in self._callees.items():
            for c in cs:
                if c in self._callers:
                    self._callers[c].add(n)

        self.manifest_disagreements = []
        for n in self._names:
            info = self._manifest_info.get(n)
            if info is not None and "is_recursive" in info:
                if bool(info["is_recursive"]) != self.recursive(n):
                    self.manifest_disagreements.append(n)

    def _scc_size(self, name):
        i = self._scc_idx.get(name)
        return len(self._sccs[i]) if i is not None else 1

    @property
    def crate_text(self):
        """the crate code sent to lean (_concat_code_files of _crate_files), without the
        unit-graph driver that for_project appends only to compute units."""
        return self._text

    @property
    def names(self):
        return set(self._names)

    @property
    def sccs(self):
        return self._sccs

    def scc_of(self, name):
        return self._scc_idx.get(name)

    def def_text(self, name):
        rng = self._ranges.get(name)
        if rng is None:
            return None
        start, end = rng
        return "\n".join(self._lines[start - 1:end])

    def callees(self, name):
        return set(self._callees.get(name, ()))

    def callees_outside_scc(self, name):
        my_scc = self._scc_idx.get(name)
        if my_scc is None:
            return []
        return sorted(c for c in self._callees.get(name, ()) if self._scc_idx.get(c) != my_scc)

    def topo_sorted_names(self):
        return list(self._topo)

    def transitive_callees(self, name):
        visited, stack = set(), list(self._callees.get(name, ()))
        while stack:
            n = stack.pop()
            if n in visited:
                continue
            visited.add(n)
            stack.extend(self._callees.get(n, ()))
        return visited

    def callers(self, name):
        return set(self._callers.get(name, ()))

    def transitive_callers(self, name):
        visited, stack = set(), list(self.callers(name))
        while stack:
            n = stack.pop()
            if n in visited:
                continue
            visited.add(n)
            stack.extend(self.callers(n))
        return visited

    def recursive(self, name):
        return name in self._callees.get(name, ()) or self._scc_size(name) > 1

    def generic(self, name):
        return self._generic.get(name, False)

    def no_eqn(self, name):
        return self._no_eqn.get(name, False)

    def loop_id(self, name):
        info = self._manifest_info.get(name)
        return info.get("loop_id") if info else None

    def loop_is_body(self, name):
        info = self._manifest_info.get(name)
        return info.get("loop_is_body") if info else None

    def parent_lean_name(self, name):
        info = self._manifest_info.get(name)
        return info.get("parent_lean_name") if info else None

    def can_diverge(self, name):
        info = self._manifest_info.get(name)
        return bool(info.get("can_diverge", False)) if info else False

    def can_fail(self, name):
        info = self._manifest_info.get(name)
        return bool(info.get("can_fail", True)) if info else True

    def is_opaque(self, name):
        info = self._manifest_info.get(name)
        return bool(info.get("is_opaque", False)) if info else False


def for_project(project_path):
    """call graph for a Rust/Aeneas project: names from the manifest, text from
    the crate's code files (_crate_files) elaborated under import Aeneas in the
    pinned aeneas project (read-only; the crate's own lake project is never built)."""
    project_path = os.path.abspath(project_path)
    manifest = _loader.load_manifest(project_path)
    folder, root, crate = _loader.crate_layout(project_path, manifest)
    text = _concat_code_files(*_crate_files(folder, root))

    local = [d for d in _loader.normalize_declarations(manifest)
             if d.get("is_local") and d.get("kind") in ("function", "global", "trait_impl")]
    lean_names = [d["lean_name"] for d in local if d.get("lean_name")]
    names = sorted(set(lean_names))

    key = hashlib.sha256((project_path + "\0" + text + "\0" + "\0".join(names)).encode("utf-8")).hexdigest()
    cached = _PROJECT_CACHE.get(key)
    if cached is not None:
        return cached

    result = _run_unit_graph(text, names)
    manifest_info = {d["lean_name"]: d for d in local}
    g = CallGraph(text, result["units"], manifest_info=manifest_info)
    g.lean_version = result.get("lean_version")
    g.aeneas_version, g.charon_version = _loader.manifest_versions(manifest)
    g.crate = crate
    g.project_path = project_path
    _PROJECT_CACHE[key] = g
    return g


def build_call_graph(source_text):
    """call graph for inline/Lean-native code: names = every definition in source_text,
    elaborated where every Lean-native text runs, the lean-native project under
    import Mathlib (the driver itself needs only Lean.Meta)."""
    text = "import Mathlib\n" + source_text
    key = hashlib.sha256(text.encode("utf-8")).hexdigest()
    cached = _SOURCE_CACHE.get(key)
    if cached is not None:
        return cached

    result = _run_unit_graph(text, None, project="lean-native")
    g = CallGraph(text, result["units"])
    g.lean_version = result.get("lean_version")
    _SOURCE_CACHE[key] = g
    return g


def _aeneas_doc(doc):
    """(Rust name, loop id) from the doc comment Aeneas writes on a definition:
    `[crate::path]: ...`, a loop's `[crate::path]: loop 0: ...`, a trait
    implementation's `Trait implementation: [crate::{impl ...}]` (a name can hold
    brackets of its own: `{impl Foo for [u8; 4]}`)."""
    i, depth = doc.find("["), 0
    if i < 0:
        return "", None
    for j in range(i, len(doc)):
        depth += {"[": 1, "]": -1}.get(doc[j], 0)
        if depth == 0:
            m = re.match(r":\s*loop (\d+):", doc[j + 1:])
            return doc[i + 1:j], int(m.group(1)) if m else None
    return "", None


def manifest_from_lean(project_dir, lean_root, root, namespace):
    """the manifest of a crate committed without one (SymCrypt's Lean project), read off
    its Lean code: every definition Aeneas wrote in `namespace` (lean/unit_graph.lean's
    dumpDecls) as a function (it returns a Result), a constant or a trait
    implementation, with its Rust name, loop, whether it is recursive (its unit graph),
    can fail, can diverge, has no body (an axiom) or no code (noncomputable)."""
    head = {"import": root, "namespace": namespace, "lean_root": lean_root}
    folder = _loader.crate_layout(project_dir, head)[0]
    text = _concat_code_files(*_crate_files(folder, root))
    full = text + "\n" + _driver_text() + f"\n#eval LssUnitGraph.dumpDecls `{namespace}\n"
    r = _lean_server.get_server(_lss_config.project_dir("aeneas")).check(full, timeout=CRATE_BUILD_TIMEOUT)
    line = next((ln for ln in (r.stderr or "").splitlines() if "LSS_DECLS " in ln), None)
    if line is None:
        raise RuntimeError("manifest: no LSS_DECLS line from lean:\n" + (r.stderr or r.stdout or "(no output)")[:3000])
    out = json.loads(line.split("LSS_DECLS ", 1)[1])
    g = CallGraph(text, out["units"])
    docs = {d["name"]: _aeneas_doc(d["doc"]) for d in out["decls"]}
    parents = {rust: n for n, (rust, loop) in docs.items() if loop is None}
    decls = []
    for d in sorted(out["decls"], key=lambda d: d["name"]):
        n, (rust, loop) = d["name"], docs[d["name"]]
        decls.append({
            "kind": "trait_impl" if d["doc"].startswith("Trait implementation:")
            else "function" if d["returns_result"] else "global",
            "is_local": True, "lean_name": n, "rust_name": rust, "lean_file": None,
            "loop_id": loop, "loop_is_body": False, "parent_lean_name": parents.get(rust) if loop is not None else None,
            "is_recursive": g.recursive(n), "can_fail": d["returns_result"], "can_diverge": d["diverges"],
            "is_opaque": d["opaque"], "noncomputable": d["noncomputable"]})
    return {**head, "made_from": "its Lean code (callgraph.manifest_from_lean)", "declarations": decls}


def _aeneas_pin():
    """pinned aeneas rev, read from lake-manifest.json the way test_pins.py does."""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "aeneas", "lake-manifest.json")
    try:
        with open(path, encoding="utf-8") as f:
            mf = json.load(f)
    except (OSError, json.JSONDecodeError):
        return None
    for p in mf.get("packages", []):
        if p.get("name", "").strip("«»") == "aeneas":
            return p.get("rev")
    return None


def _matches_pin(aeneas_version, pin):
    if not aeneas_version or not pin:
        return True
    av = aeneas_version.strip()
    if "-" not in av:
        return True
    short = av.rsplit("-", 1)[-1]
    return pin.startswith(short) or short.startswith(pin[:len(short)])


if __name__ == "__main__":
    import sys

    paths = sys.argv[1:]
    if paths[:1] == ["--manifest"] and len(paths) == 5:
        # python callgraph.py --manifest <project dir> <its Lean folder> <module root> <namespace>
        m = manifest_from_lean(*paths[1:])
        with open(os.path.join(paths[1], "rust-spec-synthesis.json"), "w", encoding="utf-8") as f:
            json.dump(m, f, indent=1)
        kinds = [d["kind"] for d in m["declarations"]]
        print(f"{len(kinds)} definitions: " + ", ".join(f"{kinds.count(k)} {k}" for k in sorted(set(kinds)))
              + f"; {sum(d['noncomputable'] for d in m['declarations'])} cannot run")
        _lean_server.shutdown_all()
        sys.exit(0)
    if not paths:
        print("usage: python callgraph.py <project_path> [...]\n"
              "       python callgraph.py --manifest <project dir> <its Lean folder> <module root> <namespace>")
        sys.exit(1)

    pin = _aeneas_pin()
    print(f"pinned aeneas rev: {pin}")

    totals = {"functions": 0, "loop_functions": 0, "sccs": 0, "recursive_sccs": 0,
              "self_recursive": 0, "can_diverge": 0, "generic": 0, "no_eqn": 0}
    largest_scc = 0
    failures = []

    for path in paths:
        print(f"=== {path} ===")
        try:
            manifest = _loader.load_manifest(path)
        except (OSError, json.JSONDecodeError) as e:
            print(f"  FAIL: cannot load manifest: {e}")
            failures.append((path, str(e)))
            continue

        av, cv = _loader.manifest_versions(manifest)
        flag = "" if _matches_pin(av, pin) else "  ** NOT AT PIN **"
        print(f"  aeneas_version={av} charon_version={cv}{flag}")

        try:
            g = for_project(path)
        except Exception as e:
            first_err = str(e).splitlines()[0] if str(e) else repr(e)
            print(f"  FAIL: {first_err}")
            failures.append((path, first_err))
            continue

        print(f"  lean_version={g.lean_version}")
        names = g.names
        n_funcs = len(names)
        n_loop = sum(1 for n in names if g.loop_id(n) is not None)
        n_sccs = len(g.sccs)
        rec_sccs = sum(1 for scc in g.sccs if len(scc) > 1)
        n_self_rec = sum(1 for n in names
                          if n in g.callees(n) and g._scc_size(n) == 1)
        largest = max((len(scc) for scc in g.sccs), default=0)
        n_diverge = sum(1 for n in names if g.can_diverge(n))
        n_generic = sum(1 for n in names if g.generic(n))
        n_no_eqn = sum(1 for n in names if g.no_eqn(n))
        print(f"  functions={n_funcs} loop_functions={n_loop} sccs={n_sccs} "
              f"recursive_sccs={rec_sccs} self_recursive={n_self_rec} largest_scc={largest} "
              f"can_diverge={n_diverge} generic={n_generic} no_eqn={n_no_eqn}")
        if g.manifest_disagreements:
            print(f"  manifest is_recursive disagreements: {sorted(g.manifest_disagreements)}")

        totals["functions"] += n_funcs
        totals["loop_functions"] += n_loop
        totals["sccs"] += n_sccs
        totals["recursive_sccs"] += rec_sccs
        totals["self_recursive"] += n_self_rec
        totals["can_diverge"] += n_diverge
        totals["generic"] += n_generic
        totals["no_eqn"] += n_no_eqn
        largest_scc = max(largest_scc, largest)

    print("=== total ===")
    print(" ".join(f"{k}={v}" for k, v in totals.items()) + f" largest_scc={largest_scc}")
    print(f"failures={len(failures)}")
    for path, err in failures:
        print(f"  {path}: {err}")
