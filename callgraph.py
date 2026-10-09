import os
import glob
import json
import hashlib

import networkx as nx

import lss_config as _lss_config
import lean_server as _lean_server
import loader as _loader
from events import with_context

_DRIVER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "unit_graph.lean")

_PROJECT_CACHE = {}
_SOURCE_CACHE = {}


def _driver_text():
    with open(_DRIVER_PATH, encoding="utf-8") as f:
        return f.read()


def _aeneas_dir():
    return _lss_config.project_dir("aeneas")


def _names_literal(names):
    if names is None:
        return "none"
    return "(some [" + ", ".join(f"`{n}" for n in names) + "])"


@with_context(layer="unitgraph")
def _run_unit_graph(code_text, names):
    """send code_text through the pinned aeneas project's server; parse the LSS_UNITS line."""
    full = code_text + "\n" + _driver_text() + f"\n#eval LssUnitGraph.dumpUnits {_names_literal(names)}\n"
    r = _lean_server.get_server(_aeneas_dir()).check(full)
    for line in (r.stderr or "").splitlines():
        if "LSS_UNITS " in line:
            return json.loads(line.split("LSS_UNITS ", 1)[1])
    raise RuntimeError("unit graph: no LSS_UNITS line from lean:\n" + (r.stderr or r.stdout or "(no output)"))


def _topo_order_code_files(code_dir, crate):
    """order <crate>/Code/*.lean files by their own crate-local import lines
    (callees-first: a file with no crate-local deps comes before one that imports it)."""
    paths = sorted(glob.glob(os.path.join(code_dir, "*.lean")))
    texts = {p: open(p, encoding="utf-8").read() for p in paths}
    prefix = f"import {crate}.Code."

    def stem(p):
        return os.path.splitext(os.path.basename(p))[0]

    def resolve(target):
        for p in paths:
            if stem(p) == target:
                return p
        for p in paths:
            if stem(p).startswith(target):
                return p
        return None

    deps = {}
    for p, text in texts.items():
        targets = [l.strip()[len(prefix):] for l in text.splitlines() if l.strip().startswith(prefix)]
        deps[p] = sorted({resolve(t) for t in targets} - {None, p})

    ordered, seen = [], set()

    def visit(p):
        if p in seen:
            return
        seen.add(p)
        for dep in deps[p]:
            visit(dep)
        ordered.append(p)

    for p in paths:
        visit(p)
    return ordered, texts


def _concat_code_files(ordered, texts):
    """import Aeneas, then each file's body with its own import lines stripped."""
    parts = ["import Aeneas"]
    for p in ordered:
        parts.append("\n".join(l for l in texts[p].splitlines() if not l.strip().startswith("import ")))
    return "\n".join(parts)


class CallGraph:
    def __init__(self, text, units, manifest_info=None):
        self._text = text
        self._lines = text.splitlines()
        self._manifest_info = manifest_info or {}
        self.lean_version = None
        self.aeneas_version = None
        self.charon_version = None
        self.crate = None
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
    the crate's own Code/*.lean files elaborated under import Aeneas in the
    pinned aeneas project (read-only; the crate's own lake project is never built)."""
    project_path = os.path.abspath(project_path)
    manifest = _loader.load_manifest(project_path)
    crate = _loader.detect_crate(project_path, manifest)
    code_dir = os.path.join(project_path, crate, "Code")
    ordered, texts = _topo_order_code_files(code_dir, crate)
    text = _concat_code_files(ordered, texts)

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
    """call graph for inline/Lean-native code: names = every definition in source_text.
    the driver itself needs Lean/Lean.Meta, so import Aeneas is always prepended
    (harmless if source_text already imports something)."""
    text = "import Aeneas\n" + source_text
    key = hashlib.sha256(text.encode("utf-8")).hexdigest()
    cached = _SOURCE_CACHE.get(key)
    if cached is not None:
        return cached

    result = _run_unit_graph(text, None)
    g = CallGraph(text, result["units"])
    g.lean_version = result.get("lean_version")
    _SOURCE_CACHE[key] = g
    return g


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
    if not paths:
        print("usage: python callgraph.py <project_path> [...]")
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
                          if n in g.callees(n) and len(g.sccs[g.scc_of(n)]) == 1)
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
