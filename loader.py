import re
import json
import os
from pathlib import Path

_DEF_RE = re.compile(r'^(?:noncomputable\s+)?def\s', re.MULTILINE)
_THM_RE = re.compile(r'^(?:theorem|lemma)\s', re.MULTILINE)
_DECL_RE = re.compile(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure)\s', re.MULTILINE)


def _main_func_name(text):
    # last def before the '-- !benchmark @start code' marker (not code_aux)
    m = re.search(r'-- !benchmark @start code(?!_)', text)
    if not m:
        return None
    defs = re.findall(r'^(?:noncomputable\s+)?def\s+(\S+)', text[:m.start()], re.MULTILINE)
    return defs[-1] if defs else None


def _func_params(func_name, lean_code):
    # non-precond param names in signature order
    m = re.search(r'def\s+' + re.escape(func_name) + r'\b(.*?)(?::=|\bwhere\b)', lean_code, re.DOTALL)
    if not m:
        return []
    sig = m.group(1)
    params = []
    for grp in re.findall(r'\(([^)]+)\)', sig):
        if '_precond' in grp or re.search(r':\s*Prop\b', grp):
            continue
        names = grp.split(':')[0].strip().split()
        params.extend(names)
    return params


def _to_input_str(func_name, lean_code, inp_dict):
    params = _func_params(func_name, lean_code)
    if not params:
        return None
    parts = [str(inp_dict[p]) for p in params if p in inp_dict]
    if len(parts) != len(params):
        return None
    return ' '.join(parts)


def _def_section(text):
    """text from first def (plus any preceding @[...] annotation) to first theorem/lemma"""
    m = _DEF_RE.search(text)
    if not m:
        return ""
    # walk back to include any @[...] attribute lines immediately before this def
    start = m.start()
    lines_before = text[:start].split('\n')
    while lines_before and not lines_before[-1].strip():
        lines_before.pop()
    while lines_before and lines_before[-1].strip().startswith('@['):
        lines_before.pop()
    start = len('\n'.join(lines_before)) + 1 if lines_before else 0

    m2 = _THM_RE.search(text, m.start())
    end = m2.start() if m2 else len(text)
    return text[start:end].strip()


def _strip_proof(chunk):
    """replace proof body after := by or := with sorry"""
    m = re.search(r':=\s*by\b', chunk)
    if m:
        return chunk[:m.start()].rstrip() + ' := by\n  sorry'
    m = re.search(r':=', chunk)
    if m:
        return chunk[:m.start()].rstrip() + ' := sorry'
    return chunk.strip()


def _theorem_stmts(text):
    """all theorem/lemma statements with proofs stripped"""
    bounds = [m.start() for m in _DECL_RE.finditer(text)]
    bounds.append(len(text))
    results = []
    for i in range(len(bounds) - 1):
        chunk = text[bounds[i]:bounds[i + 1]]
        if re.match(r'(?:theorem|lemma)\s', chunk):
            results.append(_strip_proof(chunk).strip())
    return results


def load_verina(repo_path, limit=None):
    tasks_dir = Path(repo_path) / "datasets" / "verina"
    if not tasks_dir.exists():
        print(f"verina repo not found at {repo_path}")
        return []

    results = []
    for task_dir in sorted(d for d in tasks_dir.iterdir() if d.is_dir()):
        lean_file = task_dir / "task.lean"
        if not lean_file.exists():
            continue
        text = lean_file.read_text(encoding="utf-8")

        lean_code_str = _def_section(text)
        main_func = _main_func_name(text)
        test_inputs = []
        test_file = task_dir / "test.json"
        if test_file.exists():
            raw = json.loads(test_file.read_text(encoding="utf-8"))
            if main_func:
                for t in raw:
                    s = _to_input_str(main_func, lean_code_str, t.get("input", {}))
                    if s is not None:
                        test_inputs.append(s)

        precond_names = re.findall(r'def\s+(\S+_precond)\b', text)

        postcond_defs = {}
        pc_m = re.search(
            r'-- !benchmark @start postcond\n([\s\S]*?)\n\s*-- !benchmark @end postcond\b',
            text
        )
        if pc_m:
            body = pc_m.group(1).strip()
            if body:
                pre = text[:pc_m.start()]
                pcm = re.findall(r'def\s+(\S+_postcond)\b', pre)
                if pcm:
                    postcond_defs[pcm[-1]] = body

        results.append({
            "name": task_dir.name,
            "lean_code": lean_code_str,
            "func_name": main_func,
            "ground_truth": _theorem_stmts(text),
            "test_inputs": test_inputs,
            "source": "verina",
            "preconditions": precond_names,
            "postcond_defs": postcond_defs,
        })
        if limit and len(results) >= limit:
            break
    return results


def load_clever(repo_path, limit=None):
    human_eval_dir = Path(repo_path) / "src" / "lean4" / "human_eval"
    if not human_eval_dir.exists():
        print(f"clever repo not found at {repo_path}")
        return []

    results = []
    for lean_file in sorted(human_eval_dir.glob("*.lean")):
        text = lean_file.read_text(encoding="utf-8")
        results.append({
            "name": lean_file.stem,
            "lean_code": _def_section(text),
            "ground_truth": _theorem_stmts(text),
            "test_inputs": [],
            "source": "clever",
        })
        if limit and len(results) >= limit:
            break
    return results


def detect_crate(project_path, manifest):
    """detect crate name from: import field, Code/Funs.lean dir, or basename."""
    if manifest.get("import"):
        return manifest["import"]
    try:
        for entry in os.scandir(project_path):
            if entry.is_dir() and not entry.name.startswith('.'):
                if os.path.exists(os.path.join(entry.path, "Code", "Funs.lean")):
                    return entry.name
    except OSError:
        pass
    base = os.path.basename(os.path.abspath(project_path))
    return base[0].upper() + base[1:] if base else "FeatureSuite"


def manifest_versions(manifest):
    """(aeneas_version, charon_version) from either manifest shape."""
    if "aeneas_version" in manifest:
        return manifest.get("aeneas_version"), manifest.get("charon_version")
    tc = manifest.get("toolchain", {})
    av = tc.get("aeneas_version", "")
    av = av.rsplit(" ", 1)[-1] if av else av
    return av, tc.get("charon_version")


def _norm_flat(d):
    """rust-spec-synthesis.json shape: already flattened, kind given per entry."""
    return {
        "kind": d.get("kind"),
        "is_local": d.get("is_local", False),
        "lean_name": d.get("lean_name", ""),
        "rust_name": d.get("rust_name", ""),
        "lean_file": d.get("lean_file"),
        "loop_id": d.get("loop_id"),
        "loop_is_body": d.get("loop_is_body"),
        "parent_lean_name": d.get("parent_lean_name"),
        "is_recursive": d.get("is_recursive", False),
        "can_fail": d.get("can_fail", True),
        "can_diverge": d.get("can_diverge", False),
        "is_opaque": d.get("is_opaque", False),
    }


def _norm_raw(d, kind):
    """translation.json shape: raw Aeneas manifest, nested loop/is_rec on functions only."""
    loop = d.get("loop") or {}
    return {
        "kind": kind,
        "is_local": d.get("is_local", False),
        "lean_name": d.get("lean_name", ""),
        "rust_name": d.get("rust_name", ""),
        "lean_file": d.get("lean_file"),
        "loop_id": loop.get("id"),
        "loop_is_body": loop.get("is_body"),
        "parent_lean_name": d.get("parent_lean_name"),
        "is_recursive": d.get("is_rec", False),
        "can_fail": d.get("can_fail", True),
        "can_diverge": d.get("can_diverge", False),
        "is_opaque": d.get("is_opaque", False),
    }


def normalize_declarations(manifest):
    """flat list of dicts with uniform fields, from either manifest shape."""
    raw = manifest.get("declarations")
    if raw is not None:
        decls = raw.get("funs", raw) if isinstance(raw, dict) else raw
        return [_norm_flat(d) for d in decls]
    result = [_norm_raw(d, "function") for d in manifest.get("functions", [])]
    result += [_norm_raw(d, "global") for d in manifest.get("globals", [])]
    result += [_norm_raw(d, "trait_impl") for d in manifest.get("trait_impls", [])]
    return result


def load_manifest(project_path):
    """load rust-spec-synthesis.json, falling back to translation.json."""
    manifest_path = os.path.join(project_path, "rust-spec-synthesis.json")
    if not os.path.exists(manifest_path):
        manifest_path = os.path.join(project_path, "translation.json")
    with open(manifest_path, encoding="utf-8") as f:
        return json.load(f)


def load_rust_project(project_path):
    """Load Lean functions generated by rust-spec-synthesis (Aeneas output)."""
    manifest = load_manifest(project_path)
    crate = detect_crate(project_path, manifest)

    types_path = os.path.join(project_path, crate, "Code", "Types.lean")
    funs_path = os.path.join(project_path, crate, "Code", "Funs.lean")

    types_code = ""
    if os.path.exists(types_path):
        with open(types_path, encoding="utf-8") as f:
            types_code = f.read()

    funs_code = ""
    if os.path.exists(funs_path):
        with open(funs_path, encoding="utf-8") as f:
            funs_code = f.read()

    import lss_config
    include_loops = lss_config._cfg().get("units", {}).get("include_loops", True)

    benchmarks = []
    for decl in normalize_declarations(manifest):
        if not include_loops and (decl.get("loop_is_body") or decl.get("loop_id") is not None):
            continue
        if not decl.get("is_local", False):
            continue
        if decl.get("kind") != "function":
            continue

        rust_name = decl.get("rust_name", "")
        lean_name = decl.get("lean_name", "")
        ns_name = lean_name.replace(f"{crate}.", "")

        funs_body = funs_code
        funs_body = re.sub(
            r'^.*?namespace ' + re.escape(crate) + r'\n', '', funs_body, flags=re.DOTALL
        )
        funs_body = funs_body.replace(f"end {crate}", "").strip()

        lean_preamble = (
            "set_option maxHeartbeats 1000000\n"
            "set_option maxRecDepth 2048\n"
            f"open Aeneas Aeneas.Std Result ControlFlow Error\n"
            f"open {crate}\n"
        )

        benchmarks.append({
            "name": f"rust_{ns_name.replace('.', '_')}",
            "lean_code": (
                f"import Aeneas\n"
                f"import {crate}.Code.Funs\n"
                f"import {crate}.Code.Types\n"
                f"open Aeneas Aeneas.Std Result ControlFlow Error\n"
                f"open {crate}\n"
            ),
            "func_source": types_code + "\n" + funs_code,
            "func_source_all": funs_code,
            "lean_preamble": lean_preamble,
            "func_name": ns_name,
            "test_inputs": [],
            "source": "rust-aeneas",
            "is_recursive": decl.get("is_recursive", False),
            "can_fail": decl.get("can_fail", True),
            "can_diverge": decl.get("can_diverge", False),
            "rust_name": rust_name,
            "lean_name": lean_name,
            "loop_id": decl.get("loop_id"),
            "loop_is_body": decl.get("loop_is_body"),
            "parent_lean_name": decl.get("parent_lean_name"),
        })

    return benchmarks


def load_all_benchmarks(verina_path, clever_path, limit=None):
    seen = set()
    merged = []
    for item in load_verina(verina_path, limit) + load_clever(clever_path, limit):
        if item["name"] not in seen:
            seen.add(item["name"])
            merged.append(item)
    return merged


if __name__ == "__main__":
    import sys
    sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

    VERINA = r"C:\Users\User\projects\verina"
    CLEVER = r"C:\Users\User\projects\clever"

    tasks = load_verina(VERINA, limit=3)
    for t in tasks:
        print(t["name"])
        print(t["lean_code"][:100])
        print(f"{len(t['ground_truth'])} specs")
        print()
