import re


def detect_divergent(lean_code):
    """return set of function names emitted with partial_fixpoint (may diverge).

    Aeneas marks divergent defs by appending a bare 'partial_fixpoint' line
    after the function body, before the next top-level declaration."""
    result = set()
    boundary = re.compile(
        r'(?m)^(?=(?:@\[|def\s|structure\s|inductive\s|theorem\s|lemma\s'
        r'|namespace\s|end\b|/--|\s*$))'
    )
    positions = [m.start() for m in boundary.finditer(lean_code)] + [len(lean_code)]

    for i in range(len(positions) - 1):
        chunk = lean_code[positions[i]:positions[i + 1]]
        dm = re.match(r'(?:@\[.*?\]\s*\n)?def\s+([\w.\']+)', chunk, re.DOTALL)
        if dm and re.search(r'\bpartial_fixpoint\b', chunk):
            result.add(dm.group(1))

    return result


def mark_divergent_specs(specs, divergent_funcs, func_name):
    """tag unproved specs as blocked-by-divergence when func is divergent."""
    if func_name not in divergent_funcs:
        return specs
    for s in specs:
        if s.get('status') not in ('proved', 'validated'):
            s['blocked_by_divergence'] = True
    return specs
