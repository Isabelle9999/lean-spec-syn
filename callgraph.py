import re
import os
import glob


def _parse_all_defs(source_text):
    """return {name: full_def_text} for all top-level defs in source_text."""
    result = {}
    boundary = re.compile(r'\n(?=def[ \t]|@\[|theorem[ \t]|namespace[ \t]|end\b|#)')
    for m in re.finditer(r'(?:@\[.*?\]\s*)?def\s+(\S+)\b', source_text):
        name = m.group(1)
        rel = m.group(0).index('def')
        def_pos = m.start() + rel
        tail = source_text[def_pos:]
        end_m = boundary.search(tail, 1)
        def_text = (tail[:end_m.start()] if end_m else tail).strip()
        if name not in result and def_text:
            result[name] = def_text
    return result


def _refs(def_text, all_names):
    """names from all_names that appear in def_text's body (after :=)."""
    m = re.search(r':=(.*)', def_text, re.DOTALL)
    body = m.group(1) if m else def_text
    return {n for n in all_names if re.search(r'\b' + re.escape(n) + r'\b', body)}


def _tarjan(graph):
    """tarjan's SCC; returns list of frozensets in reverse topo order (callees first)."""
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in graph.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w):
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = set()
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.add(w)
                if w == v:
                    break
            sccs.append(frozenset(scc))

    for v in list(graph):
        if v not in index:
            strongconnect(v)

    return sccs


def load_project_source(lean_code, project_dir=None):
    """collect all .lean source from project_dir (excluding .lake), or fall back to lean_code."""
    if project_dir and os.path.isdir(project_dir):
        parts = []
        for path in sorted(glob.glob(os.path.join(project_dir, "**", "*.lean"), recursive=True)):
            if ".lake" in path.replace("\\", "/"):
                continue
            try:
                parts.append(open(path, encoding="utf-8").read())
            except (OSError, UnicodeDecodeError):
                continue
        if parts:
            return "\n".join(parts)
    return lean_code


class CallGraph:
    def __init__(self, source_text):
        self._defs = _parse_all_defs(source_text)
        all_names = set(self._defs)
        self._edges = {
            name: _refs(text, all_names - {name})
            for name, text in self._defs.items()
        }
        self._sccs = _tarjan(self._edges)
        self._scc_idx = {}
        for i, scc in enumerate(self._sccs):
            for name in scc:
                self._scc_idx[name] = i

    @property
    def names(self):
        return set(self._defs)

    @property
    def sccs(self):
        return self._sccs

    def scc_of(self, name):
        return self._scc_idx.get(name)

    def def_text(self, name):
        return self._defs.get(name)

    def callees(self, name):
        return set(self._edges.get(name, []))

    def callees_outside_scc(self, name):
        my_scc = self._scc_idx.get(name)
        if my_scc is None:
            return []
        return sorted(g for g in self._edges.get(name, [])
                      if self._scc_idx.get(g) != my_scc)

    def topo_sorted_names(self):
        """names in reverse topo order: callees before callers."""
        result = []
        for scc in self._sccs:
            result.extend(sorted(scc))
        return result

    def transitive_callees(self, name):
        """all names reachable from name via the call graph (excluding name itself)."""
        visited = set()
        stack = list(self._edges.get(name, []))
        while stack:
            n = stack.pop()
            if n in visited:
                continue
            visited.add(n)
            stack.extend(self._edges.get(n, []))
        return visited

    def callers(self, name):
        return {n for n, edges in self._edges.items() if name in edges}

    def transitive_callers(self, name):
        visited, stack = set(), list(self.callers(name))
        while stack:
            n = stack.pop()
            if n in visited:
                continue
            visited.add(n)
            stack.extend(self.callers(n))
        return visited


def build_call_graph(source_text):
    return CallGraph(source_text)
