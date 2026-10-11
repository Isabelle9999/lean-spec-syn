import os
import re
import json
import hashlib
import time
import difflib
from dataclasses import dataclass
import lss_config as _lss_config
import lean_server as _lean_server
import callgraph as _callgraph
import events
from events import with_context

TACTICS = [
    # instant closers
    "rfl",
    "trivial",
    "decide",
    "assumption",
    "contradiction",
    "constructor",
    # arithmetic
    "omega",
    "norm_num",
    "positivity",
    "ring",
    "linarith",
    "norm_cast",
    "push_neg; simp",
    # simplification
    "simp",
    "simp_all",
    "dsimp; simp",
    "dsimp; grind",
    # search
    "aesop",
    "tauto",
    "grind",
    # structure
    "ext; simp",
    "funext x; simp",
    # combinations from Burton's 15 skeletons
    "simp [*]; omega",
    "simp [*]; ring",
    "simp [*]; aesop",
    "simp_all; omega",
    "simp_all; ring",
    "constructor <;> simp [*]",
    "constructor <;> omega",
    # intro variations
    "intro x; simp [*]",
    "intro x; omega",
    "intro x; decide",
    "intro x; aesop",
    "intro x; cases x <;> simp [*]",
    "intro x; cases x <;> simp [*] <;> omega",
    "intros; simp_all",
    "intros; omega",
    "intros; tauto",
    "intros; grind",
    # multi-intro for binary/ternary functions
    "intro a b; simp [*]",
    "intro a b; omega",
    "intro a b c; simp [*]",
    # backward search with known lemma names
    "exact Nat.zero_le _",
    "exact Nat.succ_pos _",
    "exact Nat.le_refl _",
    "exact List.length_nil",
    "exact Nat.zero_lt_succ _",
    "apply Nat.le_of_lt; assumption",
    "apply Nat.lt_of_lt_of_le; assumption; assumption",
    "exact Nat.le_add_right _ _",
    "exact Nat.le_add_left _ _",
    "exact ⟨rfl, rfl⟩",
    "refine ⟨?_, ?_⟩ <;> simp [*]",
    # contradiction
    "by_contra h; simp_all",
    "by_contra h; omega",
    "by_contra h; exact absurd (by assumption) h",
]

@dataclass
class ProofResult:
    proved: bool
    method: str
    error: str
    mathlib_available: bool = True
    hammer_available: bool = True
    proof_text: str = ""

@dataclass
class PBTResult:
    passed: bool
    counterexample: str
    message: str

_lean_call_count = 0

_PROJECT_DIR = _lss_config.default_project_dir()
def get_lean_calls():
    global _lean_call_count
    c = _lean_call_count
    _lean_call_count = 0
    return c

def run_in_project(code, project_dir=None):
    """Run lean with project dependencies (Mathlib or Aeneas)."""
    global _lean_call_count
    _lean_call_count += 1
    if project_dir is None:
        project_dir = _PROJECT_DIR
    r = _lean_server.get_server(project_dir).check(code)
    return r.stdout, r.stderr, r.rc


def _errors(text):
    errs = []
    for l in text.splitlines():
        if ": error:" in l or "error(" in l or "unknown identifier" in l or "Unknown constant" in l or "type mismatch" in l:
            errs.append(l)
    return errs

# keywords that indicate the whole file failed to elaborate (not just a specific theorem)
_ENV_ERROR_KEYWORDS = (
    "object file", "does not exist", "unknown module", "unknown package", "invalid import",
)

def _is_env_error(combined, import_line_count):
    """true if the lean output indicates the file failed at the import/env level"""
    for kw in _ENV_ERROR_KEYWORDS:
        if kw in combined:
            return True
    for line in combined.splitlines():
        if ": error:" in line or "error(" in line:
            lm = re.search(r':(\d+):', line)
            if lm and int(lm.group(1)) <= import_line_count:
                return True
    return False

def _code_mask(text):
    # True = code, False = comment or string literal
    n = len(text)
    mask = [True] * n
    i = 0
    while i < n:
        if text[i:i+2] == "--":
            j = text.find("\n", i)
            end = j if j != -1 else n
            for k in range(i, end):
                mask[k] = False
            i = end
        elif text[i:i+2] == "/-":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text[j:j+2] == "/-":
                    depth += 1
                    j += 2
                elif text[j:j+2] == "-/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                mask[k] = False
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == '\\':
                    j += 2
                else:
                    j += 1
            j += 1
            for k in range(i, min(j, n)):
                mask[k] = False
            i = j
        else:
            i += 1
    return mask

def classify_function(lean_env, func_name):
    body = lean_env[lean_env.find(":="):] if ":=" in lean_env else ""
    all_defs = re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_env)
    helpers = [d for d in all_defs if d != func_name]
    return {
        "recursive": func_name in body,
        "pattern_match": bool(re.search(r'^\s*\|', body, re.MULTILINE)),
        "if_else": "if " in body and "then" in body,
        "termination_by": "termination_by" in lean_env,
        "has_list": "List" in lean_env,
        "has_array": "Array" in lean_env,
        "has_nat": "Nat" in lean_env,
        "has_option": "Option" in lean_env,
        "arity": len(re.findall(r'\([^)]+:[^)]+\)', lean_env[:lean_env.find(":=")])) if ":=" in lean_env else 1,
        "helpers": helpers,
    }


def _hammer_code(lean_env, theorem_stmt):
    code = 'import Mathlib\nimport Hammer\n' + lean_env.rstrip() + '\n'
    code += f'theorem _hammer_proof : {theorem_stmt} := by hammer {{ disableGrind := true }}'
    return code


_AENEAS_LAYER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "aeneas_layer.lean")
_aeneas_layer_cache = None


def _aeneas_layer_text():
    global _aeneas_layer_cache
    if _aeneas_layer_cache is None:
        with open(_AENEAS_LAYER_PATH, encoding="utf-8") as f:
            _aeneas_layer_cache = f.read()
    return _aeneas_layer_cache


class LeanChecker:
    def __init__(self, cache=None, project_dir=None):
        self._cache = cache
        self.lean_calls = 0
        self.project_dir = project_dir
        self._env_cache = {}  # (project_dir, requires_hammer) -> (ok, error)
        self._aeneas_env = {}  # project_dir -> {env, admitted: [(name,stmt,tactic)], restarts, ok, error}
        self._aeneas_admit_counter = {}  # project_dir -> next admitted-name index, never reused

    @with_context(layer="typecheck")
    def typecheck(self, code, project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        if self._cache:
            hit = self._cache.get(code)
            if hit is not None:
                return hit[0], hit[1]
        stdout, stderr, rc = run_in_project(code, project_dir=project_dir or _PROJECT_DIR)
        self.lean_calls += 1
        combined = stdout + "\n" + stderr
        errs = _errors(combined)
        if rc != 0 and not errs:
            for line in combined.splitlines():
                line = line.strip()
                if line and not line.startswith("info:") and len(line) > 5:
                    errs.append(line)
                    break
            if not errs:
                errs.append(f"lean exited with code {rc}")
        ok = rc == 0 and not errs
        if self._cache:
            self._cache.put(code, [ok, errs])
        return ok, errs

    def typecheck_project(self, code, project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        code_with_import = "import Mathlib.Tactic\n" + code
        stdout, stderr, rc = run_in_project(code_with_import)
        combined = (stdout or "") + "\n" + (stderr or "")
        errs = _errors(combined)
        return rc == 0 and not errs, errs

    def _precheck_env(self, project_dir, requires_hammer=False):
        """verify project_dir can elaborate the imports used by proof layers.
        result is cached per (project_dir, requires_hammer).
        returns (ok, error_string)."""
        key = (project_dir, requires_hammer)
        if key in self._env_cache:
            return self._env_cache[key]
        if requires_hammer:
            hp = _lss_config.hammer_project_dir()
            if hp and os.path.normpath(project_dir) != os.path.normpath(hp):
                result = (False,
                          f"hammer not available in this project; "
                          f"hammer project: {hp}")
                self._env_cache[key] = result
                return result
        imports = "import Mathlib\n"
        if requires_hammer:
            imports += "import Hammer\n"
        stdout, stderr, rc = run_in_project(imports + "-- env precheck\n", project_dir=project_dir)
        combined = (stdout or "") + (stderr or "")
        if rc == 0 and not _is_env_error(combined, imports.count("\n")):
            result = (True, "")
        else:
            result = (False, combined.strip()[:300])
        self._env_cache[key] = result
        return result

    def sanity_check(self, project_dir=None):
        """returns True if the checker correctly rejects a known-false statement.
        any caller can verify trust before relying on results."""
        pdir = project_dir or self.project_dir or (
            _PROJECT_DIR if os.path.isdir(_PROJECT_DIR) else None
        )
        if pdir is None:
            return True  # cannot verify; assume ok
        r = self.try_proof("", "(0 : Nat) = 1", project_dir=pdir)
        return not r.proved

    def eval_expr(self, expr, prelude="", project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        code = (prelude.rstrip() + "\n" if prelude else "") + f"#eval {expr}"
        stdout, stderr, _ = run_in_project(code, project_dir=project_dir or _PROJECT_DIR)
        self.lean_calls += 1
        # lean writes pure #eval results as info messages; check both streams
        for text in (stdout, stderr):
            lines = text.splitlines()
            for i, line in enumerate(lines):
                if ": information:" in line:
                    after = line.split(": information:", 1)[1].strip()
                    if after:
                        return after
                    if i + 1 < len(lines):
                        return lines[i + 1].strip()
        # fallback: last line that is not a warning/error/note (the actual eval result)
        combined = (stdout + stderr).strip()
        for line in reversed(combined.splitlines()):
            line = line.strip()
            if line and ': warning:' not in line and ': error:' not in line and not line.startswith('Note:'):
                return line
        return combined

    def eval_with_precond(self, func_name, input_str, lean_code):
        cache_key = f"eval_precond:{func_name}:{input_str}"
        if self._cache:
            cached = self._cache.get(cache_key)
            if cached is not None:
                return cached

        m = re.search(r'def\s+' + re.escape(func_name) + r'\b(.*?)(?::=|\n\s*\|)', lean_code, re.DOTALL)
        if not m:
            return self.eval_expr(f"{func_name} {input_str}", prelude=lean_code)
        sig = m.group(1)
        precond_params = re.findall(r'\([^)]*(?:_precond|:\s*Prop)[^)]*\)', sig)
        n = len(precond_params)
        if n == 0:
            return self.eval_expr(f"{func_name} {input_str}", prelude=lean_code)

        result = None
        for tactic in ["by decide", "by native_decide", "by simp", "by tauto", "by aesop"]:
            r = self.eval_expr(
                f"{func_name} {input_str}" + f" ({tactic})" * n,
                prelude=lean_code
            )
            if r and "error" not in r.lower():
                result = r
                break

        if not result:
            for tactic in ["by decide", "by simp", "by omega", "by exact?", "by aesop"]:
                args = f" ({tactic})" * n
                code = "import Mathlib.Tactic\n" + lean_code + f"\n#eval {func_name} {input_str}{args}"
                stdout, stderr, rc = run_in_project(code)
                combined = (stdout or "") + "\n" + (stderr or "")
                for line in reversed(combined.splitlines()):
                    line = line.strip()
                    if line and ':' not in line and len(line) < 200:
                        result = line
                        break
                if result and "error" not in result.lower():
                    break
                result = None
                if rc == 0:
                    for line in combined.splitlines():
                        line = line.strip()
                        if line and 'warning' not in line and 'error' not in line and 'info' not in line.lower():
                            result = line
                            break
                    if result:
                        break

        if self._cache and result:
            self._cache.put(cache_key, result)
        return result

    @with_context(layer="tactics")
    def try_proof_batch(self, lean_env, theorem_stmt, func_name=None,
                        allow_search_tactics=False, use_project=False, project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        pdir = project_dir if project_dir else (_PROJECT_DIR if os.path.isdir(_PROJECT_DIR) else None)
        if pdir is None:
            return ProofResult(proved=False, method="", error="no project dir for mathlib")
        mathlib_ok, _ = self._precheck_env(pdir)
        imports = "import Mathlib\n" if mathlib_ok else ""

        # layer 1: tactic portfolio
        if mathlib_ok:
            tactics = [
                "rfl", "trivial", "assumption", "decide",
                "simp", "simp_all", "omega", "norm_num", "ring", "linarith",
                "tauto", "fun_induction", "fun_cases", "bv_decide",
                "aesop", "grind", "exact?",
                "field_simp", "positivity", "gcongr", "bound", "group", "abel",
                "add_group", "noncomm_ring", "field", "finiteness", "compute_degree", "fun_prop",
                # prefix combos (hammer reconstruction shapes)
                "intro _ ; first | rfl | simp_all | omega | decide",
                "constructor <;> first | rfl | simp_all",
                "split <;> first | rfl | simp_all",
            ]
        else:
            # mathlib unavailable: core lean 4 tactics only
            tactics = [
                "rfl", "trivial", "assumption", "decide",
                "simp", "simp_all", "omega", "tauto",
                "fun_induction", "fun_cases",
                "intro _ ; first | rfl | simp_all | omega | decide",
                "constructor <;> first | rfl | simp_all",
                "split <;> first | rfl | simp_all",
            ]

        names = ""
        if func_name:
            info = classify_function(lean_env, func_name)
            helpers = info["helpers"]
            names = ", ".join([func_name] + helpers)
            helpers_only = ", ".join(helpers) if helpers else ""
            # use spec binder count when classify_function can't detect arity (e.g. lean_env has no :=)
            stmt_arity = len(_parse_forall_vars(theorem_stmt))
            eff_arity = max(info["arity"], stmt_arity)

            if info["recursive"]:
                tactics.extend([
                    f"unfold {func_name}; simp_all" + (f" [{helpers_only}]" if helpers_only else ""),
                    f"intro x; unfold {func_name}; simp_all" + (f" [{helpers_only}]" if helpers_only else ""),
                ])
                tactics.extend([
                    f"intro x; induction x <;> simp [{names}, *]",
                    f"intro x; induction x <;> simp [{names}, *] <;> omega",
                    f"intro x; induction x <;> simp_all [{names}]",
                    f"intro x y; induction x generalizing y <;> simp [{names}, *]",
                    f"intro x y; induction y generalizing x <;> simp [{names}, *]",
                ])
                if info["pattern_match"]:
                    tactics.extend([
                        f"intro x; fun_induction {func_name} x <;> simp [{names}, *]",
                        f"intro x; fun_induction {func_name} x <;> simp [{names}, *] <;> omega",
                        f"intro x y; fun_induction {func_name} x y <;> simp [{names}, *]",
                        f"intro x; fun_cases {func_name} x <;> simp [{names}, *]",
                    ])
                if info["termination_by"]:
                    tactics.extend([
                        f"induction a, b using {func_name}.induct <;> simp [{names}, *]",
                        f"induction a, b using {func_name}.induct <;> simp [{names}, *] <;> omega",
                    ])
                if info["if_else"] and not info["pattern_match"]:
                    tactics.extend([
                        f"intro x; unfold {func_name}; split <;> simp_all [{names}]",
                        f"intro x y; unfold {func_name}; split <;> simp_all [{names}]",
                    ])
            else:
                tactics.extend([
                    f"simp [{names}]",
                    f"simp [{names}]; omega",
                ])
                if mathlib_ok:
                    tactics.append(f"simp [{names}]; aesop")

            tactics.extend([
                f"intro x; simp [{names}]",
                "intro x; omega",
            ])

            if eff_arity >= 2:
                tactics.extend([f"intro a b; simp [{names}, *]", "intro a b; omega"])
            if eff_arity >= 3:
                tactics.append(f"intro a b c; simp [{names}, *]")
            if eff_arity >= 4:
                tactics.append(f"intro a b c d; simp [{names}, *]")

            intro_n = "intro " + " ".join(["_"] * max(eff_arity, 1))
            tactics.extend([
                f"grind [{names}]",
                f"intros; grind [{names}]",
                f"simp [{names}]",
                f"{intro_n}; simp [{names}, *]; omega",
                f"{intro_n}; simp [{names}, *]; ring",
                f"{intro_n}; simp [{names}, *]",
            ])

        else:
            tactics.extend([
                "intros; simp_all", "intros; omega", "intros; tauto",
                "intro x; simp [*]", "intro x; omega", "intro x; decide",
                "intro x; cases x <;> simp [*]", "intro x; cases x <;> simp [*] <;> omega",
                "intro a b; simp [*]", "intro a b; omega",
                "intro a b c; simp [*]",
                "simp [*]; omega", "simp_all; omega",
                "constructor <;> simp [*]", "constructor <;> omega",
                "by_contra h; simp_all", "by_contra h; omega",
                "exact Nat.zero_le _", "exact Nat.succ_pos _",
                "exact ⟨rfl, rfl⟩", "refine ⟨?_, ?_⟩ <;> simp [*]",
            ])
            if mathlib_ok:
                tactics.append("intros; grind")

        entries = [(f"by {t}", f"l1:{t}") for t in tactics]
        entries += [
            ("rfl", "l1:rfl"),
            ("Iff.rfl", "l1:Iff.rfl"),
            ("fun x => rfl", "l1:term:fun x=>rfl"),
            ("fun x y => rfl", "l1:term:fun x y=>rfl"),
            ("id", "l1:term:id"),
        ]
        if names:
            entries += [
                (f"fun x => by simp [{names}]", "l1:term:fun x=>simp"),
                (f"And.intro (by simp [{names}]) (by simp [{names}])", "l1:term:And.intro"),
            ]

        env_stripped = lean_env.rstrip()
        env_line_count = env_stripped.count("\n") + 1
        parts = [env_stripped]
        for i, (suffix, _) in enumerate(entries):
            parts.append(f"private theorem _p{i} : {theorem_stmt} := {suffix}")
        batch = imports + "\n".join(parts)
        cache_key = batch
        if self._cache:
            hit = self._cache.get_proof(cache_key)
            if hit is not None:
                return ProofResult(proved=hit["proved"], method=hit["method"],
                                   error=hit.get("error", ""),
                                   mathlib_available=hit.get("mathlib_available", True))

        stdout, stderr, rc = run_in_project(batch, project_dir=pdir)
        self.lean_calls += 1

        combined = stdout + stderr
        import_lines = imports.count("\n")

        if rc == 0:
            # positive confirmation: the whole file compiled
            result = ProofResult(proved=True, method=entries[0][1], error="",
                                 mathlib_available=mathlib_ok)
        else:
            # file-level failure — env error, not a theorem error
            if _is_env_error(combined, import_lines):
                return ProofResult(proved=False, method="",
                                   error=f"env error: {combined.strip()[:200]}",
                                   mathlib_available=mathlib_ok)

            # map errors to line numbers
            error_lines = set()
            for line in _errors(combined):
                lm = re.search(r':(\d+):', line)
                if lm:
                    error_lines.add(int(lm.group(1)))

            # per-theorem ranges; stmt may span multiple lines
            stmt_lines = theorem_stmt.count('\n') + 1
            base = import_lines + env_line_count
            result = ProofResult(proved=False, method="", error=combined.strip()[:200],
                                 mathlib_available=mathlib_ok)
            for i, (suffix, label) in enumerate(entries):
                start = base + 1 + i * stmt_lines
                end = base + (i + 1) * stmt_lines
                if not any(start <= el <= end for el in error_lines):
                    # isolate and confirm — never proved from absence alone
                    confirm = imports + env_stripped + f"\ntheorem _conf : {theorem_stmt} := {suffix}"
                    cout, cerr, crc = run_in_project(confirm, project_dir=pdir)
                    self.lean_calls += 1
                    ccombined = (cout or "") + (cerr or "")
                    if crc == 0 and not _errors(ccombined) and "sorry" not in ccombined:
                        result = ProofResult(proved=True, method=label, error="",
                                             mathlib_available=mathlib_ok)
                        break

        if self._cache:
            self._cache.put_proof(cache_key, {
                "proved": result.proved, "method": result.method, "error": result.error,
                "mathlib_available": result.mathlib_available,
            })
        return result

    def try_proof(self, lean_env, theorem_stmt, func_name=None,
                  allow_search_tactics=False, use_project=False, project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        return self.try_proof_batch(lean_env, theorem_stmt, func_name=func_name,
                                    allow_search_tactics=allow_search_tactics,
                                    use_project=use_project, project_dir=project_dir)

    @with_context(layer="hammer")
    def try_hammer(self, lean_env, theorem_stmt, func_name=None, project_dir=None):
        # always use the configured hammer project (aeneas); project_dir arg ignored
        pdir = _lss_config.hammer_project_dir()
        if pdir is None:
            return ProofResult(proved=False, method='', error='no hammer project configured')
        hammer_ok, hammer_err = self._precheck_env(pdir, requires_hammer=True)
        if not hammer_ok:
            return ProofResult(proved=False, method='l2:skipped (hammer unavailable)',
                               error=f'hammer unavailable: {hammer_err}', hammer_available=False)
        hammer_timeout = _lss_config.server_cfg()['hammer_timeout']
        code = _hammer_code(lean_env, theorem_stmt)
        t0 = time.time()
        r = _lean_server.get_server(pdir).check(code, timeout=hammer_timeout)
        elapsed = time.time() - t0
        global _lean_call_count
        _lean_call_count += 1
        self.lean_calls += 1
        if r.timed_out:
            return ProofResult(proved=False, method='', error=f'timeout after {hammer_timeout}s',
                               hammer_available=True)
        combined = (r.stdout or '') + (r.stderr or '')
        # filter premise-server info lines before error check
        filtered = '\n'.join(
            l for l in combined.splitlines()
            if 'unindexed premises' not in l
        )
        ok = r.rc == 0 and not _errors(filtered)
        if ok:
            return ProofResult(proved=True, method=f'l2:hammer ({elapsed:.1f}s)', error='',
                               hammer_available=True)
        return ProofResult(proved=False, method='', error=combined.strip()[:200],
                           hammer_available=True)

    def _aeneas_build_env(self, project_dir):
        """fresh env = crate text + the same options/opens the benches' own
        lean_code + lean_preamble use (so a statement elaborates the same way in
        every layer) + the aeneas layer, in the pinned aeneas project. maxHeartbeats
        is left out here on purpose: each attempt sets its own cap. printed once
        per crate since cost grows with crate size."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        server = _lean_server.get_server(aeneas_dir)
        g = _callgraph.for_project(project_dir)
        text = (g.crate_text +
                "\nset_option maxRecDepth 2048\n"
                f"open Aeneas Aeneas.Std Result ControlFlow Error\nopen {g.crate}\n" +
                _aeneas_layer_text())
        t0 = time.time()
        r = server.check(text, timeout=600)
        elapsed = time.time() - t0
        print(f"  aeneas env build: {project_dir} {elapsed:.1f}s")
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")
        ok = r.rc == 0 and r.new_env is not None
        if not ok:
            errs = _errors(combined)
            print(f"  aeneas env build failed: {(errs[0] if errs else combined.strip())[:200]}")
        state = {"env": r.new_env, "admitted": [], "restarts": server.stats()["restarts"],
                 "ok": ok, "error": combined[:300]}
        self._aeneas_env[project_dir] = state
        return state

    def _aeneas_env_for(self, project_dir):
        """the crate's current env, rebuilding (and replaying admitted specs, in
        proof order, callees-first) if the server restarted since it was built."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        server = _lean_server.get_server(aeneas_dir)
        state = self._aeneas_env.get(project_dir)
        if state is None:
            return self._aeneas_build_env(project_dir)
        if state["restarts"] != server.stats()["restarts"]:
            admitted = state["admitted"]
            state = self._aeneas_build_env(project_dir)
            if state["ok"]:
                for name, stmt, tactic in admitted:
                    self._aeneas_admit(project_dir, state, name, stmt, tactic)
        return state

    def _aeneas_admit(self, project_dir, state, name, stmt, tactic):
        """extend the crate's env once with the winning proof, @[step]-registered.
        only on success: a failing admit (lower cap, flaky tactic, ...) keeps the
        old env and is not recorded, so it can't leave a sorry-backed @[step] lemma.
        success is lss_report_attempts's ok=true (collectAxioms, no sorryAx), the
        same check the proof attempts themselves get: a plain error-message check
        can't see a tactic that silently closes the goal with sorry."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        heartbeats = _lss_config.proof_cfg()["aeneas_heartbeats"]
        server = _lean_server.get_server(aeneas_dir)
        text = (f"set_option maxHeartbeats {heartbeats} in\n"
                f"theorem {name} : {stmt} := by\n  {tactic}\n"
                f"lss_register_step {name}\nlss_report_attempts {name}")
        r = server.check(text, timeout=90, env=state["env"])
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")
        verdict = None
        for m in re.finditer(r"LSS_ATTEMPT (\{[^\n]*\})", combined):
            try:
                v = json.loads(m.group(1))
            except json.JSONDecodeError:
                continue
            if v.get("name") == name:
                verdict = v
        ok = r.rc == 0 and r.new_env is not None and verdict is not None and verdict.get("ok") is True
        if ok:
            state["env"] = r.new_env
            state["admitted"].append((name, stmt, tactic))
        else:
            errs = _errors(combined)
            print(f"  aeneas admit failed: {name}: {(errs[0] if errs else combined.strip())[:200]}")
        return r

    @with_context(layer="aeneas")
    def try_aeneas(self, candidate_stmt, func_name, rust_project_dir, candidate_id=None):
        """aeneas-tactic layer for a rust unit: unfold f; step*, then step* plus a
        closer, against the crate's growing env in the pinned aeneas project (every
        spec proved so far this run, this crate, already @[step]-registered there)."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        heartbeats = _lss_config.proof_cfg()["aeneas_heartbeats"]
        server = _lean_server.get_server(aeneas_dir)
        state = self._aeneas_env_for(rust_project_dir)
        if not state["ok"]:
            return ProofResult(proved=False, method="", error=state["error"])

        attempts = [
            ("a", f"lss_spec_form\n  unfold {func_name}\n  step*"),
            ("b", f"lss_spec_form\n  unfold {func_name}\n  "
                  "step* <;> first | scalar_tac | simp_scalar | (simp_all <;> simp_lists [*]) | grind"),
            ("c", f"lss_spec_form\n  unfold {func_name}\n  step*\n  lss_log_goals\n  all_goals sorry"),
        ]

        def entry_text(label, tactic):
            return (f"set_option maxHeartbeats {heartbeats} in\n"
                    f"theorem _aeneas_{label} : {candidate_stmt} := by\n  {tactic}")

        full = "\n".join(entry_text(label, tactic) for label, tactic in attempts)
        full += "\nlss_report_attempts _aeneas_a _aeneas_b"

        r = server.check(full, timeout=90, env=state["env"])
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")

        for m in re.finditer(r"LSS_GOALS (\{[^\n]*\})", combined):
            try:
                goal = json.loads(m.group(1))
            except json.JSONDecodeError:
                continue
            events.emit("open_goal", unit=func_name, candidate_id=candidate_id,
                        head=goal.get("head", "?"))

        verdicts = {}
        for m in re.finditer(r"LSS_ATTEMPT (\{[^\n]*\})", combined):
            try:
                v = json.loads(m.group(1))
            except json.JSONDecodeError:
                continue
            verdicts[v.get("name")] = v

        for label, tactic in attempts[:2]:
            v = verdicts.get(f"_aeneas_{label}")
            if v and v.get("ok"):
                n = self._aeneas_admit_counter.get(rust_project_dir, 0)
                self._aeneas_admit_counter[rust_project_dir] = n + 1
                name = f"lss_admitted_{n}"
                self._aeneas_admit(rust_project_dir, state, name, candidate_stmt, tactic)
                return ProofResult(proved=True, method=f"aeneas:{label}", error="",
                                   proof_text=tactic)

        return ProofResult(proved=False, method="", error=combined.strip()[:200])

    def check_specs_against_mutants_batch(self, mutant_code, specs, func_name=None):
        """check which specs hold against a mutant, all in one lean call.

        returns {spec_name: True/False} where True means spec holds against
        the mutant (spec is too weak for this mutant).
        """
        if not specs:
            return {}

        info = classify_function(mutant_code, func_name) if func_name else {}
        helpers = info.get("helpers", [])
        names = ", ".join([func_name] + helpers) if func_name else ""

        tactics_to_try = ["rfl", "simp", "omega", "aesop", "decide"]
        if func_name:
            tactics_to_try.extend([f"simp [{names}]", f"simp [{names}, *]; omega"])

        entries = []
        for i, spec in enumerate(specs):
            stmt = spec["stmt"]
            for j, tac in enumerate(tactics_to_try):
                entries.append(f"private theorem _m{i}t{j} : {stmt} := by {tac}")

        code = mutant_code.rstrip() + "\n" + "\n".join(entries)
        stdout, stderr, _ = run_in_project(code, project_dir=self.project_dir)
        self.lean_calls += 1
        combined = (stdout or "") + "\n" + (stderr or "")

        results = {}
        for i, spec in enumerate(specs):
            spec_holds = False
            for j in range(len(tactics_to_try)):
                tag = f"_m{i}t{j}"
                if tag not in combined:
                    spec_holds = True
                    break
            results[spec["name"]] = spec_holds

        return results

    def check_mutant_batch(self, mutant_codes, spec_stmt, func_name=None):
        """check one spec against multiple mutants in one lean call.

        returns list of bools: True if spec holds against that mutant (too weak).
        """
        if not mutant_codes:
            return []

        info = classify_function(mutant_codes[0], func_name) if func_name else {}
        helpers = info.get("helpers", [])
        names = ", ".join([func_name] + helpers) if func_name else ""

        tactics = ["rfl", "simp", "omega", "aesop", "decide"]
        if func_name:
            tactics.extend([f"simp [{names}]", f"simp [{names}, *]; omega"])

        entries = []
        for i, mut_code in enumerate(mutant_codes):
            entries.append(f"namespace _mut{i}")
            entries.append(mut_code)
            for j, tac in enumerate(tactics):
                entries.append(f"private theorem _t{j} : {spec_stmt} := by {tac}")
            entries.append(f"end _mut{i}")

        code = "\n".join(entries)
        stdout, stderr, _ = run_in_project(code, project_dir=self.project_dir)
        self.lean_calls += 1
        combined = (stdout or "") + "\n" + (stderr or "")

        results = []
        tac_count = len(tactics)
        for i in range(len(mutant_codes)):
            holds = False
            for j in range(tac_count):
                tag = f"_mut{i}._t{j}"
                if tag not in combined:
                    holds = True
                    break
            results.append(holds)

        return results

    def run_pbt(self, lean_code, theorem_stmt):
        if not os.path.isdir(_PROJECT_DIR):
            return PBTResult(passed=False, counterexample="", message="project not found")
        code = f"import Plausible\n\n{lean_code}\n\nexample : {theorem_stmt} := by plausible"
        stdout, stderr, _ = run_in_project(code)
        self.lean_calls += 1
        combined = stdout + stderr
        if "Unable to find a counter-example" in combined:
            return PBTResult(passed=True, counterexample="", message="no counterexample found")
        if "Found a counter-example" in combined:
            m = re.search(r'Found a counter-example!([\s\S]*?)---', combined)
            cx = m.group(1).strip() if m else "found"
            return PBTResult(passed=False, counterexample=cx, message="counterexample found")
        return PBTResult(passed=False, counterexample="", message=combined.strip()[:200])


OPERATORS = {
    " + ": [" - "],
    " - ": [" + "],
    " * ": [" + "],
    " / ": [" * "],
    " % ": [" - "],
    " < ": [" <= ", " > "],
    " <= ": [" < ", " >= "],
    " > ": [" >= ", " < "],
    " >= ": [" > ", " <= "],
    "true": ["false"],
    "false": ["true"],
    " 0": [" 1"],
    " 1": [" 0"],
    "some ": ["none "],
    "none": ["some default"],
}

SKIP_TOKENS = {"→", "←", "↔", "≠", "≤", "≥", ":=", "=>", "then", "else", "do", "let"}

_MUTANT_CAP = 30
_SECOND_ORDER_CAP = 10


def _sample_mutants(mutants, cap):
    """round-robin sample across operator classes when over cap.
    returns (sampled_list, stats_dict)."""
    n = len(mutants)
    if n <= cap:
        return mutants, {"generated": n, "sampled": n, "capped": False}
    by_class = {}
    for m in mutants:
        cls = m.get("operator", "other").split("_")[0]
        by_class.setdefault(cls, []).append(m)
    per_cls = {c: len(v) for c, v in by_class.items()}
    result = []
    queues = list(by_class.values())
    while len(result) < cap and any(queues):
        for q in queues:
            if q and len(result) < cap:
                result.append(q.pop(0))
    return result, {"generated": n, "sampled": len(result), "per_class": per_cls, "capped": True}


def _diff_patch(base, mutant):
    """find single contiguous diff; returns (lo, hi, repl) or None."""
    sm = difflib.SequenceMatcher(None, base, mutant, autojunk=False)
    blocks = [(op, i1, i2, j1, j2) for op, i1, i2, j1, j2 in sm.get_opcodes() if op != 'equal']
    if not blocks or len(blocks) > 1:
        return None
    op, i1, i2, j1, j2 = blocks[0]
    return (i1, i2, mutant[j1:j2])


def _generate_second_order(raw_mutants, base_code, cap):
    """compose pairs from different operator classes; returns list of second-order raw mutants."""
    by_class = {}
    for m in raw_mutants:
        cls = m.get("operator", "other").split("_")[0]
        by_class.setdefault(cls, []).append(m)
    if len(by_class) < 2:
        return []
    classes = list(by_class.keys())
    second = []
    for i in range(len(classes)):
        for j in range(i + 1, len(classes)):
            if len(second) >= cap:
                break
            m1, m2 = by_class[classes[i]][0], by_class[classes[j]][0]
            p1 = _diff_patch(base_code, m1["code"])
            p2 = _diff_patch(base_code, m2["code"])
            if p1 is None or p2 is None:
                continue
            lo1, hi1, repl1 = p1
            lo2, hi2, repl2 = p2
            if lo1 < hi2 and lo2 < hi1:
                continue  # overlapping sites
            if lo1 > lo2:
                lo1, hi1, repl1, lo2, hi2, repl2 = lo2, hi2, repl2, lo1, hi1, repl1
            new_code = base_code[:lo1] + repl1 + base_code[hi1:]
            delta = len(repl1) - (hi1 - lo1)
            lo2 += delta; hi2 += delta
            new_code = new_code[:lo2] + repl2 + new_code[hi2:]
            second.append({
                "code": new_code,
                "operator": f"2nd:{m1.get('operator','?')}+{m2.get('operator','?')}",
            })
        if len(second) >= cap:
            break
    return second


def _parse_forall_types(stmt):
    """extract arg types from leading ∀ quantifiers; [] if unparseable"""
    types = []
    s = stmt.strip()
    m0 = re.match(r'^∀\s*', s)
    if not m0:
        return []
    s = s[m0.end():]
    while s and s[0] == '(':
        depth = 0
        end = -1
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end == -1:
            return []
        inner = s[1:end]
        if ':' in inner:
            colon = inner.index(':')
            names = inner[:colon].strip().split()
            t = inner[colon + 1:].strip()
            types.extend([t] * len(names))
        s = s[end + 1:].strip().lstrip(',').strip()
    return types


_AENEAS_SCALAR = {
    "U8": "u8", "Std.U8": "u8", "U16": "u16", "Std.U16": "u16",
    "U32": "u32", "Std.U32": "u32", "U64": "u64", "Std.U64": "u64",
    "U128": "u128", "Std.U128": "u128", "Usize": "usize", "Std.Usize": "usize",
    "I8": "i8", "Std.I8": "i8", "I16": "i16", "Std.I16": "i16",
    "I32": "i32", "Std.I32": "i32", "I64": "i64", "Std.I64": "i64",
    "I128": "i128", "Std.I128": "i128", "Isize": "isize", "Std.Isize": "isize",
}


def _witnesses_for_type(t, struct_defs=None):
    """small witness values for a Lean type string"""
    t = t.strip()
    if t in ("Nat", "Int"):
        return ["0", "1", "2", "3", "5", "10"]
    if t in _AENEAS_SCALAR:
        s = _AENEAS_SCALAR[t]
        return [f"0#{s}", f"1#{s}", f"2#{s}", f"3#{s}", f"5#{s}", f"10#{s}"]
    if t == "Bool":
        return ["true", "false"]
    if t.startswith("List"):
        inner = t[4:].strip().strip("()")
        iw = _witnesses_for_type(inner, struct_defs) if inner else ["0"]
        a = iw[0] if iw else "0"
        b = iw[1] if len(iw) > 1 else a
        return ["[]", f"[{a}]", f"[{a}, {b}]"]
    if t.startswith("Option"):
        inner = t[6:].strip().strip("()")
        iw = _witnesses_for_type(inner, struct_defs) if inner else ["0"]
        a = iw[0] if iw else "0"
        return ["none", f"some {a}"]
    if struct_defs:
        key = t.split(".")[-1]
        if key in struct_defs:
            fields = struct_defs[key]
            field_vals = [_witnesses_for_type(ft, struct_defs) for _, ft in fields]
            if all(field_vals):
                all_combos = _cross(field_vals)
                # prioritize tuples where field values differ — needed to kill swap-like mutants
                distinct = [c for c in all_combos if len(set(c)) > 1]
                combos = (distinct if distinct else all_combos)[:3]
                return ["⟨" + ", ".join(c) + "⟩" for c in combos]
    return []


def _parse_struct_defs(source):
    """parse structure definitions; returns {name: [(field, type), ...]}"""
    defs = {}
    for m in re.finditer(
        r'\bstructure\s+(\w+)[^\n]*\bwhere\b([\s\S]*?)(?=\nstructure\b|\ndef\b|\ntheorem\b|\Z)',
        source,
    ):
        name = m.group(1)
        body = m.group(2)
        fields = []
        for fm in re.finditer(r'^\s+(\w+)\s*:\s*([^\n]+)', body, re.MULTILINE):
            fname = fm.group(1)
            ftype = fm.group(2).strip().rstrip(',')
            if ftype and fname not in ('mk', 'where'):
                fields.append((fname, ftype))
        if fields:
            defs[name] = fields
    return defs


def _find_def_in_text(text, func_name):
    """locate a top-level def in text; tries qualified name then unqualified last component.
    handles @[...] attributes and multiline signatures.
    returns (func_def_text, matched_def_name) or (None, None)."""
    last = func_name.split(".")[-1]
    # boundary: newline that starts the next top-level declaration
    boundary = re.compile(r'\n(?=def[ \t]|@\[|theorem[ \t]|namespace[ \t]|end\b|/--)')
    names = [func_name] if func_name == last else [func_name, last]
    for name in names:
        pat = re.compile(r'(?:@\[.*?\]\s*)?def\s+' + re.escape(name) + r'\b')
        m = pat.search(text)
        if not m:
            continue
        # find where 'def' keyword starts within the match
        rel = m.group(0).index('def')
        def_pos = m.start() + rel
        tail = text[def_pos:]
        end_m = boundary.search(tail, 1)
        func_def = (tail[:end_m.start()] if end_m else tail).strip()
        if func_def:
            return func_def, name
    return None, None


def _parse_forall_vars(stmt):
    """extract variable names from leading ∀ quantifiers; [] if unparseable"""
    names = []
    s = stmt.strip()
    m0 = re.match(r'^∀\s*', s)
    if not m0:
        return []
    s = s[m0.end():]
    while s and s[0] == '(':
        depth = 0
        end = -1
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end == -1:
            return []
        inner = s[1:end]
        if ':' in inner:
            colon = inner.index(':')
            names.extend(inner[:colon].strip().split())
        s = s[end + 1:].strip().lstrip(',').strip()
    return names


def _cross(lists):
    """cartesian product of lists of strings"""
    result = [()]
    for lst in lists:
        result = [r + (x,) for r in result for x in lst]
    return result


def _diverse_tuples(per_arg, cap):
    """ascending and descending cross products interleaved, then one-large-rest-small"""
    if not per_arg or any(not v for v in per_arg):
        return []
    seen = set()
    result = []

    def add(tup):
        if tup not in seen and len(result) < cap:
            seen.add(tup)
            result.append(tup)

    asc = _cross(per_arg)
    desc = _cross([list(reversed(v)) for v in per_arg])
    for a, d in zip(asc, desc):
        add(a)
        add(d)
        if len(result) >= cap:
            break
    # one argument large, rest at smallest value
    for j in range(len(per_arg)):
        tup = tuple((v[-1] if k == j else v[0]) for k, v in enumerate(per_arg))
        add(tup)
    # one argument small, rest at largest value
    for j in range(len(per_arg)):
        tup = tuple((v[0] if k == j else v[-1]) for k, v in enumerate(per_arg))
        add(tup)
    return result[:cap]


def _find_error_ctor(project_dir):
    """find a no-arg Error constructor from the Aeneas support library.
    returns e.g. 'Error.assertionFailure' or None if not found."""
    if not project_dir or not os.path.isdir(project_dir):
        return None
    import glob as _glob
    search_dirs = [project_dir]
    lake_pkg = os.path.join(project_dir, ".lake", "packages")
    if os.path.isdir(lake_pkg):
        search_dirs.append(lake_pkg)
    limit = 500
    count = 0
    for search_dir in search_dirs:
        for path in _glob.glob(os.path.join(search_dir, "**", "*.lean"), recursive=True):
            if count >= limit:
                return None
            count += 1
            try:
                src = open(path, encoding="utf-8").read()
            except (OSError, UnicodeDecodeError):
                continue
            m = re.search(r'\binductive\s+Error\b([\s\S]*?)(?=\n\S|\Z)', src)
            if not m:
                continue
            for line in m.group(0).splitlines():
                line = line.strip()
                if line.startswith('|') and '→' not in line and '->' not in line:
                    nm = re.match(r'\|\s*(\w+)', line)
                    if nm:
                        return f"Error.{nm.group(1)}"
    return None


class MutationEngine:
    def __init__(self, checker):
        self._checker = checker
        self._last_sampling_stats = None

    def generate_mutants(self, lean_code, func_name, llm=None, func_source=None, project_dir=None):
        last = func_name.split(".")[-1]

        # 1. resolve: inline in lean_code, func_source, or project search
        inline = False
        def_src = None   # source to run operators against
        def_name = None  # name as it appears in def_src
        tried_sources = []

        fd, dn = _find_def_in_text(lean_code, func_name)
        if fd:
            # inline: run operators on full lean_code so helper context is included
            inline = True
            def_src = lean_code
            def_name = func_name
            tried_sources.append("lean_code")

        if def_src is None and func_source:
            fd, dn = _find_def_in_text(func_source, func_name)
            if fd:
                def_src = fd
                def_name = dn
                tried_sources.append("func_source")

        if def_src is None and project_dir and os.path.isdir(project_dir):
            import glob as _glob
            proj_abs = os.path.abspath(project_dir)
            searched_files = []
            for path in sorted(_glob.glob(
                os.path.join(project_dir, "**", "*.lean"), recursive=True
            )):
                norm = path.replace("\\", "/")
                if ".lake" in norm:
                    continue
                if (re.match(r'tmp[a-zA-Z0-9]+\.lean$', os.path.basename(path))
                        and os.path.abspath(os.path.dirname(path)) == proj_abs):
                    continue
                searched_files.append(path)
                try:
                    text = open(path, encoding="utf-8").read()
                except (OSError, UnicodeDecodeError):
                    continue
                fd, dn = _find_def_in_text(text, func_name)
                if fd:
                    def_src = fd
                    def_name = dn
                    break
            tried_sources.append(
                f"project at {project_dir} ({len(searched_files)} files searched)"
            )

        if def_src is None:
            tried = ", ".join(tried_sources) if tried_sources else "none"
            patterns = f"'def {func_name}'" + (f", 'def {last}'" if last != func_name else "")
            return [{"code": lean_code, "operator": "no_def_found",
                     "diagnostic": (
                         f"no def of {func_name!r} found in {tried}; "
                         f"patterns tried: {patterns}"
                     )}]

        # 2. run all operators against def_src
        raw = []
        m = re.search(r':=(.*)', def_src, re.DOTALL)
        if m:
            body_start = m.start(1)
            body = def_src[body_start:]
            header = def_src[:body_start]
            mask = _code_mask(body)
            all_tokens = sorted(set(OPERATORS.keys()) | SKIP_TOKENS, key=len, reverse=True)
            pos = 0
            while pos < len(body):
                if not mask[pos]:
                    pos += 1
                    continue
                found = False
                for tok in all_tokens:
                    end = pos + len(tok)
                    if body[pos:end] == tok:
                        if tok in OPERATORS:
                            for repl in OPERATORS[tok]:
                                mutant_body = body[:pos] + repl + body[end:]
                                raw.append({"code": header + mutant_body, "operator": tok.strip(), "site": body_start + pos})
                        pos = end
                        found = True
                        break
                if not found:
                    pos += 1
        arm = self.swap_match_arms(def_src)
        if arm:
            raw.append(arm)
        ie = self.swap_if_else(def_src)
        if ie:
            raw.append(ie)
        raw.extend(self.type_directed_mutants(def_src, def_name))
        raw.extend(self._lean_specific_mutants(def_src, def_name, project_dir=project_dir))
        if llm:
            raw.extend(self.generate_llm_mutants(def_src, def_name, llm))

        # 3. dedup: pre-emit for inline (same full code = same mutation);
        #    no pre-emit dedup for non-inline (different mutant names make all post-emit codes unique)
        if inline:
            seen = set()
            deduped = []
            for mut in raw:
                if mut["code"] not in seen:
                    seen.add(mut["code"])
                    deduped.append(mut)
        else:
            seen = set()
            deduped = list(raw)

        # second-order: inline only; typecheck before emitting to avoid stillborns (Bug 4)
        if inline:
            second = _generate_second_order(deduped, def_src, _SECOND_ORDER_CAP)
            for m in second:
                if m["code"] not in seen:
                    ok, _ = self._checker.typecheck(m["code"])
                    if ok:
                        seen.add(m["code"])
                        deduped.append(m)

        # 4. emit: rename def to fresh name and append to original lean_code
        mutants = []
        for i, mut in enumerate(deduped):
            mutant_fn = f"{last}_mut{i}"
            if inline:
                src, _ = _find_def_in_text(mut["code"], def_name)
                if src is None:
                    continue
            else:
                src = mut["code"]
            renamed = re.sub(
                r'\bdef\s+' + re.escape(def_name) + r'\b',
                f'def {mutant_fn}',
                src, count=1,
            )
            if renamed == src:
                continue
            mutants.append({
                **mut,
                "code": lean_code.rstrip() + "\n" + renamed,
                "mutant_func_name": mutant_fn,
            })

        # 5. sample (Item 2)
        sampled, stats = _sample_mutants(mutants, _MUTANT_CAP)
        self._last_sampling_stats = stats
        return sampled

    def _lean_specific_mutants(self, lean_code, func_name, project_dir=None):
        """lean-specific mutation operators modeled on mutdafny's methodology."""
        mutants = []
        idx = lean_code.find(":=")
        if idx == -1:
            return mutants
        header = lean_code[:idx]
        body = lean_code[idx:]
        body_start = idx

        # category 1: match arm mutations
        arms = list(re.finditer(r'(\s*\|[^\n]*(?:\n(?!\s*\|)\s+[^\n]*)*)', body))

        # 1a: remove one arm (missing case)
        if len(arms) > 2:
            for i in range(len(arms)):
                new_body = body[:arms[i].start()] + body[arms[i].end():]
                mutants.append({"code": header + new_body, "operator": f"remove_arm_{i}"})

        # 1b: swap adjacent arms
        if len(arms) >= 2:
            for i in range(len(arms) - 1):
                a1, a2 = arms[i].group(0), arms[i+1].group(0)
                new_body = body[:arms[i].start()] + a2 + a1 + body[arms[i+1].end():]
                mutants.append({"code": header + new_body, "operator": f"swap_arms_{i}_{i+1}"})

        # 1c: duplicate first arm
        if arms:
            new_body = body[:arms[0].end()] + arms[0].group(0) + body[arms[0].end():]
            mutants.append({"code": header + new_body, "operator": "duplicate_first_arm"})

        # category 2: base case value mutations
        base_arms = [a for a in arms if func_name not in a.group(0)]
        for arm in base_arms:
            m = re.search(r'=>\s*(.+?)$', arm.group(0), re.MULTILINE)
            if m:
                result = m.group(1).strip()
                alts = {"0": ["1"], "1": ["0"], "true": ["false"], "false": ["true"],
                        "[]": ["[default]"], "none": ["some default"]}
                for alt in alts.get(result, []):
                    new_arm = arm.group(0)[:m.start(1) - arm.start()] + alt + arm.group(0)[m.end(1) - arm.start():]
                    new_body = body[:arm.start()] + new_arm + body[arm.end():]
                    mutants.append({"code": header + new_body, "operator": f"wrong_base_{result}_{alt}"})

        # category 3: arithmetic mutations
        for op, replacements in [("+", ["-", "*"]), ("-", ["+", "*"]), ("*", ["+", "-"])]:
            for m in re.finditer(re.escape(f" {op} "), body):
                for rep in replacements:
                    new_body = body[:m.start()] + f" {rep} " + body[m.end():]
                    mutants.append({"code": header + new_body, "operator": f"arith_{op}_{rep}"})

        # category 4: condition mutations
        for m in re.finditer(r'if\s+(.+?)\s+then', body):
            cond = m.group(1)
            negated = cond.replace("¬", "", 1).strip().strip("()") if "¬" in cond else f"¬({cond})"
            new_body = body[:m.start()] + f"if {negated} then" + body[m.end():]
            mutants.append({"code": header + new_body, "operator": "negate_cond"})

        for orig, repl in [("<", "≤"), (">", "≥"), ("≤", "<"), ("≥", ">")]:
            for m in re.finditer(re.escape(orig), body):
                new_body = body[:m.start()] + repl + body[m.end():]
                mutants.append({"code": header + new_body, "operator": f"boundary_{orig}_{repl}"})

        # category 5: recursive call mutations — off-by-one
        for m in re.finditer(rf'{re.escape(func_name)}\s+\(([^)]+)\)', body):
            arg = m.group(1).strip()
            for tok in ["+ 1", "- 1"]:
                if tok in arg:
                    new_arg = arg.replace(tok, "", 1).strip()
                    if new_arg:
                        new_body = body[:m.start()] + f"{func_name} ({new_arg})" + body[m.end():]
                        mutants.append({"code": header + new_body, "operator": "off_by_one_recursive"})

        # category 6: constructor mutations — swap args
        for m in re.finditer(r'(\w+)\s+(\w+)\s+(\w+)', body):
            if m.group(1) in {"Cons", "cons", "some", "mk", "Pair.mk"}:
                new_body = body[:m.start()] + f"{m.group(1)} {m.group(3)} {m.group(2)}" + body[m.end():]
                mutants.append({"code": header + new_body, "operator": "swap_constructor_args"})

        # shared mask for categories 7-14: skip comments and string literals
        _mask = _code_mask(body)
        _ic = lambda s, e: all(_mask[k] for k in range(s, e))

        # category 7: struct field value swap { f1 := v1, f2 := v2 } -> swap values / duplicate
        for m in re.finditer(
            r'\{\s*(\w+)\s*:=\s*([^,}\n]+?)\s*,\s*(\w+)\s*:=\s*([^}\n]+?)\s*\}', body
        ):
            if not _ic(m.start(), m.end()):
                continue
            f1, v1, f2, v2 = m.group(1), m.group(2).strip(), m.group(3), m.group(4).strip()
            if v1 != v2:
                nb = body[:m.start()] + f'{{ {f1} := {v2}, {f2} := {v1} }}' + body[m.end():]
                mutants.append({"code": header + nb, "operator": "struct_val_swap", "site": body_start + m.start()})
            for dup_v, op in [(v1, "struct_dup_first"), (v2, "struct_dup_second")]:
                nb = body[:m.start()] + f'{{ {f1} := {dup_v}, {f2} := {dup_v} }}' + body[m.end():]
                mutants.append({"code": header + nb, "operator": op, "site": body_start + m.start()})

        # category 8: field source swap p.a <-> p.b for same object p
        by_obj = {}
        for fa in re.finditer(r'\b(\w+)\.(\w+)\b', body):
            if _ic(fa.start(), fa.end()):
                by_obj.setdefault(fa.group(1), set()).add(fa.group(2))
        for obj, fields in by_obj.items():
            fields = sorted(fields)
            for fi in range(len(fields)):
                for fj in range(fi + 1, len(fields)):
                    fa_name, fb_name = fields[fi], fields[fj]
                    nb = re.sub(
                        r'\b' + re.escape(obj) + r'\.' + r'(' + re.escape(fa_name) + r'|' + re.escape(fb_name) + r')\b',
                        lambda m, _a=fa_name, _b=fb_name, _o=obj: f'{_o}.{_b}' if m.group(1) == _a else f'{_o}.{_a}',
                        body
                    )
                    if nb != body:
                        mutants.append({"code": header + nb, "operator": "field_src_swap", "site": body_start})

        # category 9: guard removal — replace if-condition with True or False
        for m in re.finditer(r'\bif\s+([^\n]+?)\s+then\b', body):
            if not _ic(m.start(), m.end()):
                continue
            cond = m.group(1).strip()
            if cond not in ('True', 'False', 'true', 'false'):
                for gc in ('True', 'False'):
                    nb = body[:m.start()] + f'if {gc} then' + body[m.end():]
                    mutants.append({"code": header + nb, "operator": f"guard_{gc.lower()}", "site": body_start + m.start()})

        # category 10: ok <value> -> fail <error_ctor>
        # match whole application to avoid ill-typed partial replacement
        _err_ctor = _find_error_ctor(project_dir)
        if _err_ctor:
            # match ok followed by: { ... } struct, ( ... ) tuple, or simple token
            for m in re.finditer(
                r'\bok\b(\s+(?:\{(?:[^{}]|\{[^{}]*\})*\}|\([^)]*\)|\S+))', body
            ):
                if _ic(m.start(), m.end()):
                    nb = body[:m.start()] + f'fail {_err_ctor}' + body[m.end():]
                    mutants.append({"code": header + nb, "operator": "ok_to_fail", "site": body_start + m.start()})
        # fail_to_ok omitted: cannot safely construct a value of the return type in general

        # category 11: logical operator replacement ∧ <-> ∨
        for old_l, new_l in [("∧", "∨"), ("∨", "∧")]:
            for m in re.finditer(re.escape(old_l), body):
                if _ic(m.start(), m.end()):
                    nb = body[:m.start()] + new_l + body[m.end():]
                    mutants.append({"code": header + nb, "operator": f"logic_{old_l}_to_{new_l}", "site": body_start + m.start()})

        # category 12: variable swap — swap two params from the same binder group
        for pm in re.finditer(r'\(([^)]+)\)', header):
            inner = pm.group(1).strip()
            if ':' not in inner:
                continue
            colon = inner.index(':')
            names = inner[:colon].strip().split()
            if len(names) < 2:
                continue
            for i in range(len(names)):
                for j in range(i + 1, len(names)):
                    a, b = names[i], names[j]
                    nb = re.sub(r'\b' + re.escape(a) + r'\b', '\x00', body)
                    nb = re.sub(r'\b' + re.escape(b) + r'\b', a, nb)
                    nb = nb.replace('\x00', b)
                    if nb != body:
                        mutants.append({"code": header + nb, "operator": f"var_swap_{a}_{b}", "site": body_start})

        # category 13: list operation substitution
        for old_op, new_op in [
            ("List.reverse", "id"), ("List.take", "List.drop"),
            ("List.head?", "List.getLast?"), (".reverse", ".id"),
        ]:
            if old_op in body:
                nb = body.replace(old_op, new_op, 1)
                mutants.append({"code": header + nb, "operator": f"list_op_{old_op.lstrip('.').replace('.','_')}", "site": body_start})

        # category 14: match arm body replacement — give arm i the body of arm j
        if len(arms) >= 2:
            for i in range(min(len(arms), 3)):
                for j in range(len(arms)):
                    if i == j:
                        continue
                    arm_i_text = arms[i].group(0)
                    mi = re.search(r'=>\s*(.+?)$', arm_i_text, re.MULTILINE)
                    mj = re.search(r'=>\s*(.+?)$', arms[j].group(0), re.MULTILINE)
                    if not (mi and mj):
                        continue
                    bi, bj = mi.group(1).strip(), mj.group(1).strip()
                    if bi != bj and func_name not in bj:
                        new_arm = arm_i_text[:mi.start(1)] + bj + arm_i_text[mi.end(1):]
                        nb = body[:arms[i].start()] + new_arm + body[arms[i].end():]
                        mutants.append({"code": header + nb, "operator": f"arm_body_{i}_{j}", "site": body_start + arms[i].start()})

        return mutants

    def swap_match_arms(self, lean_code):
        lines = lean_code.split("\n")
        arm_idx = [i for i, line in enumerate(lines) if re.match(r'\s*\|', line)]
        if len(arm_idx) < 2:
            return None
        i, j = arm_idx[0], arm_idx[1]
        new_lines = lines[:]
        new_lines[i], new_lines[j] = new_lines[j], new_lines[i]
        return {"code": "\n".join(new_lines), "operator": "swap_arms", "site": 0}

    def swap_if_else(self, lean_code):
        m = re.search(r'\bif\b(.*?)\bthen\b(.*?)\belse\b(.*?)$', lean_code, re.MULTILINE)
        if not m:
            return None
        start = m.start()
        new_code = lean_code[:start] + "if" + m.group(1) + "then" + m.group(3) + " else" + m.group(2) + lean_code[m.end():]
        return {"code": new_code, "operator": "swap_if_else", "site": start}

    def type_directed_mutants(self, lean_code, func_name):
        m = re.search(r':=(.*)', lean_code, re.DOTALL)
        if not m:
            return []
        body_start = m.start(1)
        body = lean_code[body_start:]
        header = lean_code[:body_start]
        mask = _code_mask(body)
        mutants = []

        def _in_code(s, e):
            return all(mask[i] for i in range(s, min(e, len(mask))))

        def _add(pattern, repl, op, flags=0):
            for hm in re.finditer(pattern, body, flags):
                if not _in_code(hm.start(), hm.end()):
                    continue
                replacement = hm.expand(repl) if isinstance(repl, str) else repl(hm)
                new_body = body[:hm.start()] + replacement + body[hm.end():]
                mutants.append({"code": header + new_body, "operator": op, "site": body_start + hm.start()})

        if re.search(r'\bList\b', header):
            # drop head: remove "word :: " leaving the tail
            _add(r'\b(\w+)\s*::\s*', '', "drop_head")
            # duplicate head: "h :: t" -> "h :: h :: t"
            _add(r'\b(\w+)\s*::\s*(\w+)\b', r'\1 :: \1 :: \2', "dup_head")
            # recursive call -> []
            _add(r'\b' + re.escape(func_name) + r'\b(?:\s+\w+)+', '[]', "empty_rec")
            # [x] -> []
            _add(r'\[\s*\w+\s*\]', '[]', "empty_singleton")

        if re.search(r'\bNat\b|\bInt\b', header):
            # n + 1 -> n
            _add(r'\b(\w+)\s*\+\s*1\b', lambda hm: hm.group(1), "off_by_one_down")
            # replace 2+ literals with 0
            _add(r'\b([2-9]\d*|[1-9]\d+)\b', '0', "lit_to_zero")

        if re.search(r'\bBool\b', header):
            _add(r'&&', '||', "and_to_or")
            _add(r'\|\|', '&&', "or_to_and")

        if re.search(r'\bOption\b', header):
            _add(r'\bsome\s+\w+\b', 'none', "some_to_none")

        return mutants

    @with_context(layer="mutation")
    def filter_compilable(self, mutants, original_code=None, func_name=None, llm=None):
        result = []
        for mut in mutants:
            if mut.get("diagnostic"):
                continue
            ok, _ = self._checker.typecheck(mut["code"])
            if ok:
                if llm and original_code and func_name:
                    if self.detect_equivalent_llm(original_code, mut["code"], func_name, llm):
                        continue
                result.append(mut)
        return result

    def generate_llm_mutants(self, lean_code, func_name, llm):
        """LLMorpheus-style mutation: placeholder-based LLM mutation combined
        with Meta's hybrid approach (whole-function rewrite)."""
        mutants = []
        body_match = re.search(r':=([\s\S]*?)(?=\ndef\s|\Z)', lean_code)
        if not body_match:
            return mutants
        body = body_match.group(1)

        # strategy 1 (LLMorpheus 4-part): match arm body placeholder
        arms = list(re.finditer(r'(\|\s*[^=]*=>)\s*(.+?)(?=\s*\||$)', body, re.MULTILINE))
        for arm in arms:
            pattern_text = arm.group(1).strip()
            result_text = arm.group(2).strip()
            if not result_text or func_name in result_text:
                continue
            placeholder_src = lean_code.replace(result_text, '<PLACEHOLDER>', 1)
            prompt = (
                f"Mutation testing checks whether a test suite detects small code changes.\n\n"
                f"Source with the selected fragment replaced by <PLACEHOLDER>:\n"
                f"```lean\n{placeholder_src}\n```\n\n"
                f"Original fragment at <PLACEHOLDER>: `{result_text}`\n\n"
                f"Write 3 replacements for <PLACEHOLDER> that CHANGE THE FUNCTION'S BEHAVIOUR. Each must:\n"
                f"- have the same return type\n"
                f"- be valid Lean 4\n"
                f"- produce a different result on at least one input\n"
                f"Suggestions: use a wrong constant, swap operands, return a pattern variable directly, "
                f"negate a condition, use a different constructor.\n\n"
                f"Return ONLY the replacement expressions, one per line, no explanation."
            )
            resp = llm._ask(prompt)
            if resp:
                for line in resp.strip().splitlines():
                    alt = line.strip().lstrip("-*").strip("`").strip()
                    if alt and alt != result_text and len(alt) < 200:
                        new_code = lean_code.replace(result_text, alt, 1)
                        mutants.append({"code": new_code, "operator": "llm_arm"})

        # strategy 2 (LLMorpheus 4-part): recursive call placeholder
        rec_calls = list(re.finditer(rf'{re.escape(func_name)}\s+(\S+(?:\s+\S+)*)', body))
        if rec_calls:
            call_text = rec_calls[0].group(0).strip()
            placeholder_src = lean_code.replace(call_text, '<PLACEHOLDER>', 1)
            prompt = (
                f"Mutation testing checks whether a test suite detects small code changes.\n\n"
                f"Source with the selected recursive call replaced by <PLACEHOLDER>:\n"
                f"```lean\n{placeholder_src}\n```\n\n"
                f"Original fragment at <PLACEHOLDER>: `{call_text}`\n\n"
                f"Write 3 replacements for <PLACEHOLDER> that CHANGE THE FUNCTION'S BEHAVIOUR. Each must:\n"
                f"- be a valid recursive call to {func_name} with the same number of arguments\n"
                f"- produce different output on at least one input\n"
                f"Suggestions: shift an argument by +1 or -1, swap two arguments, "
                f"use a constant instead of a variable, remove a -1 decrement.\n\n"
                f"Return ONLY the replacement call expressions, one per line, no explanation."
            )
            resp = llm._ask(prompt)
            if resp:
                for line in resp.strip().splitlines():
                    alt = line.strip().lstrip("-*").strip("`").strip()
                    if alt and alt != call_text and func_name in alt and len(alt) < 200:
                        new_code = lean_code.replace(call_text, alt, 1)
                        mutants.append({"code": new_code, "operator": "llm_rec"})

        # strategy 3 (LLMorpheus 4-part): if-condition placeholder
        conds = list(re.finditer(r'\bif\s+([^\n]+?)\s+then\b', body))
        if conds:
            cond_text = conds[0].group(1).strip()
            placeholder_src = lean_code.replace(cond_text, '<PLACEHOLDER>', 1)
            prompt = (
                f"Mutation testing checks whether a test suite detects small code changes.\n\n"
                f"Source with the selected condition replaced by <PLACEHOLDER>:\n"
                f"```lean\n{placeholder_src}\n```\n\n"
                f"Original fragment at <PLACEHOLDER>: `{cond_text}`\n\n"
                f"Write 3 replacements for <PLACEHOLDER> that CHANGE THE FUNCTION'S BEHAVIOUR. Each must:\n"
                f"- be a valid Lean 4 boolean expression\n"
                f"- produce a different result on at least one input\n"
                f"Suggestions: flip < to <=, flip < to >, negate the condition, swap operands, "
                f"use True or False, replace a variable with a constant.\n\n"
                f"Return ONLY the replacement condition expressions, one per line, no explanation."
            )
            resp = llm._ask(prompt)
            if resp:
                for line in resp.strip().splitlines():
                    alt = line.strip().lstrip("-*").strip("`").strip()
                    if alt and alt != cond_text and len(alt) < 200:
                        new_code = lean_code.replace(cond_text, alt, 1)
                        mutants.append({"code": new_code, "operator": "llm_cond"})

        # strategy 4: whole-function rewrite for functions without if/match patterns
        prompt4 = (
            f"Mutation testing checks whether a test suite detects small code changes.\n\n"
            f"Source:\n```lean\n{lean_code}\n```\n\n"
            f"Write 3 subtly WRONG versions with the SAME signature `def {func_name}` that:\n"
            f"- compile in Lean 4\n"
            f"- produce different output on at least one input\n"
            f"Suggestions: off-by-one, wrong base case, swapped arguments, wrong constructor, "
            f"swapped struct fields, missing negation.\n\n"
            f"Return each version as a complete def, separated by ---, no explanation."
        )
        resp4 = llm._ask(prompt4)
        if resp4:
            for chunk in resp4.split("---"):
                # strip code fences before extracting the def
                chunk = re.sub(r'```\w*', '', chunk).strip()
                m = re.search(rf'def\s+{re.escape(func_name)}[\s\S]*?(?=\ndef\s|\Z)', chunk)
                if m:
                    candidate = m.group(0).strip()
                    if candidate and candidate != lean_code.strip():
                        mutants.append({"code": candidate, "operator": "llm_rewrite"})

        return mutants

    def detect_equivalent_llm(self, original_code, mutant_code, func_name, llm):
        """Meta's LLM-as-judge approach to detect equivalent mutants.
        Pre-filter before expensive certification."""
        prompt = (
            f"Original function:\n```lean\n{original_code}\n```\n\n"
            f"Mutant function:\n```lean\n{mutant_code}\n```\n\n"
            f"Are these two functions equivalent? Do they produce the same output for ALL possible inputs?\n"
            f"Answer ONLY 'equivalent' or 'different'. Nothing else."
        )
        resp = llm._ask(prompt)
        if resp:
            return "equivalent" in resp.strip().lower()
        return False

    def certify(self, original_code, mutant_code, func_name, test_inputs):
        if isinstance(mutant_code, dict):
            mutant_fn = mutant_code.get("mutant_func_name", func_name)
            code = mutant_code["code"]
        else:
            mutant_fn = func_name
            code = mutant_code
        ok, _ = self._checker.typecheck(code)
        if not ok:
            return None
        for inp in test_inputs:
            orig = self._checker.eval_expr(f"{func_name} {inp}", prelude=original_code)
            mut = self._checker.eval_expr(f"{mutant_fn} {inp}", prelude=code)
            if orig != mut and "error" not in orig.lower() and "error" not in mut.lower():
                return {"input": inp, "original": orig, "mutant": mut}
        return None

    def certify_batch(self, original_code, mutant_codes, func_name, test_inputs):
        """Certify multiple mutants at once. Returns list of witness dicts or None per mutant."""
        if not test_inputs or not mutant_codes:
            return [None] * len(mutant_codes)

        def _eval_all(code, eval_fn):
            src = code.rstrip() + "\n"
            for inp in test_inputs:
                src += f"#eval toString ({eval_fn} {inp})\n"
            stdout, stderr, _ = run_in_project(src, project_dir=self._checker.project_dir)
            self._checker.lean_calls += 1
            combined = (stdout or "") + "\n" + (stderr or "")
            outputs = []
            pending = False
            for line in combined.splitlines():
                if ": information:" in line:
                    after = line.split(": information:", 1)[1].strip()
                    if after:
                        outputs.append(after)
                        pending = False
                    else:
                        pending = True
                elif pending and line.strip():
                    outputs.append(line.strip())
                    pending = False
            return outputs

        orig_outputs = _eval_all(original_code, func_name)
        results = [None] * len(mutant_codes)
        if len(orig_outputs) < len(test_inputs):
            return results

        for mi, m in enumerate(mutant_codes):
            mutant_fn = m.get("mutant_func_name", func_name) if isinstance(m, dict) else func_name
            code = m["code"] if isinstance(m, dict) else m
            ok, _ = self._checker.typecheck(code)
            if not ok:
                continue
            mut_outputs = _eval_all(code, mutant_fn)
            for i in range(min(len(orig_outputs), len(mut_outputs))):
                if orig_outputs[i] != mut_outputs[i]:
                    results[mi] = {
                        "input": test_inputs[i],
                        "original": orig_outputs[i],
                        "mutant": mut_outputs[i],
                    }
                    break

        return results

    @with_context(layer="mutation")
    def certify_proof(self, lean_code, mutant, func_name, spec_stmts,
                       project_dir=None, skip_equiv=False, struct_defs=None, spec_names=None):
        """classify one mutant: STILLBORN/EQUIVALENT/KILLED/SURVIVED/INCONCLUSIVE"""
        if project_dir is None:
            project_dir = self._checker.project_dir
        mutant_code = mutant.get("code", "") if isinstance(mutant, dict) else mutant
        mutant_fn = (mutant.get("mutant_func_name", func_name)
                     if isinstance(mutant, dict) else func_name)
        env = mutant_code  # fresh-name mutants already embed lean_code + mutant def

        ok, _ = self._checker.typecheck(env, project_dir=project_dir)
        if not ok:
            return {"status": "STILLBORN", "method": "typecheck"}

        def _prove(stmt):
            pr = self._checker.try_proof(env, stmt, project_dir=project_dir)
            if pr.proved:
                return pr.method
            pr2 = self._checker.try_hammer(env, stmt, project_dir=project_dir)
            return pr2.method if pr2.proved else None

        def _sub(stmt):
            """replace func_name → mutant_fn with word-boundary matching.
            returns None if the substituted statement doesn't reference mutant_fn,
            which means we cannot use it to assess this mutant."""
            if mutant_fn == func_name:
                return stmt
            s = re.sub(r'\b' + re.escape(func_name) + r'\b', mutant_fn, stmt)
            # guard: no whole-word occurrence of func_name must remain; fresh name must appear
            if re.search(r'\b' + re.escape(func_name) + r'\b', s) or mutant_fn not in s:
                return None
            return s

        # equivalence: only for fresh-name mutants where both funcs are in scope
        if mutant_fn != func_name and not skip_equiv:
            m = _prove(f"{func_name} = {mutant_fn}")
            if m is not None:
                return {"status": "EQUIVALENT", "method": m}

        # kill: diverse witnesses, each verified in its own isolated run_in_project call
        _mathlib_ok, _ = self._checker._precheck_env(project_dir) if project_dir else (True, "")
        _cert_imports = "import Mathlib\n" if _mathlib_ok else ""
        kill_pre = _cert_imports + env.rstrip() + "\n"
        kidx = 0
        kill_done = False
        for sidx, stmt in enumerate(spec_stmts):
            if kill_done:
                break
            s = _sub(stmt)
            if s is None:
                continue  # spec doesn't reference mutant_fn; skip for kill evidence
            types = _parse_forall_types(s)
            if not types:
                continue
            per_arg = [_witnesses_for_type(t, struct_defs) for t in types]
            if any(not w for w in per_arg):
                continue
            for tup in _diverse_tuples(per_arg, 12):
                if kidx >= 12:
                    kill_done = True
                    break
                witness = ", ".join(tup)
                if _mathlib_ok:
                    kill_body = (
                        f"  push Not\n"
                        f"  use {witness}\n"
                        f"  simp [{mutant_fn}]"
                    )
                else:
                    kill_body = (
                        f"  intro h\n"
                        f"  specialize h {witness}\n"
                        f"  simp [{mutant_fn}] at h"
                    )
                kcode = (
                    kill_pre
                    + f"theorem _kill_check : ¬ ({s}) := by\n"
                    + kill_body
                )
                kout, kerr, krc = run_in_project(kcode, project_dir=project_dir)
                kcombined = (kout or "") + (kerr or "")
                if krc == 0 and not _errors(kcombined) and "sorry" not in kcombined:
                    killed_by = spec_names[sidx] if spec_names else stmt
                    return {"status": "KILLED", "method": f"kill:witness({witness})",
                            "killed_by": killed_by, "witness": witness}
                kidx += 1

        # survival: try mutant-aware tactics first, then generic three-layer search
        surv_pre = _cert_imports + env.rstrip() + "\n"
        methods = []
        for stmt in spec_stmts:
            s = _sub(stmt)
            if s is None:
                return {"status": "INCONCLUSIVE",
                        "method": f"subst_failed: {func_name!r}->{mutant_fn!r} in {stmt[:60]!r}"}
            vs = " ".join(_parse_forall_vars(s)) or "_"
            surv_candidates = [
                f"simp [{mutant_fn}]",
                f"intro {vs}; simp [{mutant_fn}]; omega",
                f"intro {vs}; simp [{mutant_fn}]; split <;> omega",
                f"intro {vs}; unfold {mutant_fn}; split <;> omega",
                f"intro {vs}; simp [{mutant_fn}]; aesop",
            ]
            found = None
            for tactic in surv_candidates:
                scode = surv_pre + f"theorem _surv_check : {s} := by\n  {tactic}"
                sout, serr, src = run_in_project(scode, project_dir=project_dir)
                scombined = (sout or "") + (serr or "")
                if src == 0 and not _errors(scombined) and "sorry" not in scombined:
                    found = f"survived:{tactic}"
                    break
            if found is None:
                found = _prove(s)
            if found is None:
                return {"status": "INCONCLUSIVE", "method": ""}
            methods.append(found)

        if spec_stmts:
            return {"status": "SURVIVED", "method": methods[0],
                    "survived_spec_names": list(spec_names) if spec_names else [],
                    "diff": _diff_patch(lean_code, mutant_code)}
        return {"status": "INCONCLUSIVE", "method": "no specs"}

    def spec_accepts_mutant(self, spec_stmt, mutant_code, func_name=None):
        if isinstance(mutant_code, dict):
            mutant_fn = mutant_code.get("mutant_func_name", func_name)
            code = mutant_code["code"]
        else:
            mutant_fn = func_name
            code = mutant_code
        stmt = spec_stmt
        if func_name and mutant_fn and mutant_fn != func_name:
            stmt = re.sub(r'\b' + re.escape(func_name) + r'\b', mutant_fn, spec_stmt)
        r = self._checker.try_proof(code, stmt)
        return r.proved


class SpecMutator:
    WEAKEN = {"<": "<=", ">": ">=", "∧": "∨"}
    _SKIP = {"<=", ">=", "≤", "≥"}

    def find_unnecessarily_weak(self, specs, lean_code, lean_checker, project_dir=None):
        checks = []
        entries = []
        all_tokens = sorted(set(self.WEAKEN.keys()) | self._SKIP, key=len, reverse=True)
        for spec in specs:
            if spec["status"] != "proved":
                continue
            stmt = spec["stmt"]
            pos = 0
            while pos < len(stmt):
                found = False
                for tok in all_tokens:
                    if stmt[pos:pos+len(tok)] == tok:
                        if tok in self.WEAKEN:
                            weaker = self.WEAKEN[tok]
                            mutated = stmt[:pos] + weaker + stmt[pos+len(tok):]
                            entries.append(f"private theorem _sw{len(checks)} : {mutated} := sorry")
                            checks.append({
                                "spec_name": spec["name"],
                                "mutation": f"{tok} -> {weaker} at {pos}",
                            })
                        pos += len(tok)
                        found = True
                        break
                if not found:
                    pos += 1
        if not checks:
            return []
        env = lean_code.rstrip()
        env_lines = env.count("\n") + 1
        code = env + "\n" + "\n".join(entries)
        stdout, stderr, _ = run_in_project(code, project_dir=project_dir)
        combined = (stdout or "") + "\n" + (stderr or "")
        err_line_nums = set()
        for l in combined.splitlines():
            m = re.search(r':(\d+):', l)
            if m and (': error:' in l or 'type mismatch' in l or 'unknown identifier' in l or 'Unknown constant' in l):
                err_line_nums.add(int(m.group(1)))
        results = []
        for i, check in enumerate(checks):
            line_no = env_lines + 1 + i
            results.append({
                "spec_name": check["spec_name"],
                "mutation": check["mutation"],
                "still_holds": line_no not in err_line_nums,
            })
        return results


class ExampleStore:
    def __init__(self):
        os.makedirs(".lss", exist_ok=True)
        self._path = ".lss/examples.json"
        if os.path.exists(self._path):
            with open(self._path) as f:
                self._data = json.load(f)
        else:
            self._data = {}

    def _save(self):
        with open(self._path, "w") as f:
            json.dump(self._data, f)

    def add_negative(self, func, input_val, wrong_output, provenance="mutation"):
        self._data.setdefault(func, {"positive": [], "negative": []})
        self._data[func]["negative"].append({"in": input_val, "out": wrong_output, "source": provenance})
        self._save()

    def add_positive(self, func, input_val, correct_output):
        self._data.setdefault(func, {"positive": [], "negative": []})
        self._data[func]["positive"].append({"input": input_val, "output": correct_output})
        self._save()

    def check_examples(self, func):
        return self._data.get(func, {"positive": [], "negative": []})


class Cache:
    CACHE_VERSION = 2

    def __init__(self, path=".lss/cache.json"):
        self._path = path
        self._data = {}
        self._load()

    def _load(self):
        if os.path.exists(self._path):
            try:
                with open(self._path) as f:
                    raw = json.load(f)
                if raw.get("_v") != self.CACHE_VERSION:
                    self._data = {"_v": self.CACHE_VERSION}
                    return
                self._data = raw
            except (json.JSONDecodeError, ValueError):
                self._data = {}

    def _save(self):
        os.makedirs(os.path.dirname(self._path) or ".", exist_ok=True)
        out = {"_v": self.CACHE_VERSION, **self._data}
        tmp = self._path + ".tmp"
        try:
            with open(tmp, "w") as f:
                json.dump(out, f)
            os.replace(tmp, self._path)
        except Exception:
            try:
                with open(self._path, "w") as f:
                    json.dump(out, f)
            except Exception:
                pass

    def _key(self, code):
        return hashlib.md5(code.encode()).hexdigest()

    def get(self, code):
        return self._data.get(self._key(code))

    def put(self, code, result):
        self._data[self._key(code)] = result
        self._save()

    def _proof_key(self, code):
        return "p:" + hashlib.md5(code.encode()).hexdigest()

    def get_proof(self, code):
        return self._data.get(self._proof_key(code))

    def put_proof(self, code, result):
        self._data[self._proof_key(code)] = result
        self._save()


if __name__ == "__main__":
    c = LeanChecker()
    succ_def = "def succ (n : Nat) : Nat := n + 1"

    ok, errs = c.typecheck(succ_def)
    print(f"typecheck: ok={ok} errs={errs}")

    val = c.eval_expr("succ 5", prelude=succ_def)
    print(f"eval succ 5: {val!r}")

    # omega can't see through user-defined succ; test with plain arithmetic
    r = c.try_proof(succ_def, "∀ n : Nat, n + 1 > 0")
    print(f"proof: proved={r.proved} method={r.method!r} error={r.error!r}")

    # comment masking
    cmt = "x + y -- this is a comment with + and -"
    mask = _code_mask(cmt)
    cmt_start = cmt.index("--")
    skipped = not any(mask[cmt_start:])
    print(f"comment mask: operators in comment skipped = {skipped}")

    # mutant generation
    max_code = "def max' (a b : Nat) : Nat := if a >= b then a else b"
    engine = MutationEngine(c)
    mutants = engine.generate_mutants(max_code, "max'")
    print(f"max' mutants: {len(mutants)}")
    for mut in mutants:
        print(f"  {mut['operator']:15} {mut['code'][:70]}")

    # PBT
    succ_def = "def succ' (n : Nat) : Nat := n + 1"
    pbt = c.run_pbt(succ_def, "∀ n, succ' n > 0")
    print(f"\npbt true spec:  passed={pbt.passed} counterexample={pbt.counterexample!r}")
    pbt2 = c.run_pbt(succ_def, "∀ n, succ' n = n")
    print(f"pbt false spec: passed={pbt2.passed} counterexample={pbt2.counterexample!r}")

    # filter_compilable: max' expects all to compile
    all_max = engine.generate_mutants(max_code, "max'")
    comp_max = engine.filter_compilable(all_max)
    print(f"\nmax' filter_compilable: {len(all_max)} total, {len(comp_max)} compile")

    # type-directed mutants on insertionSort
    sort_code = """\
def insertSorted (x : Nat) (lst : List Nat) : List Nat :=
  match lst with
  | [] => [x]
  | h :: t => if x <= h then x :: h :: t else h :: insertSorted x t

def insertionSort (lst : List Nat) : List Nat :=
  match lst with
  | [] => []
  | h :: t => insertSorted h (insertionSort t)"""
    sort_mutants = engine.generate_mutants(sort_code, "insertionSort")
    sort_ops = {m["operator"] for m in sort_mutants}
    print(f"\ninsertionSort mutants: {len(sort_mutants)}, ops: {sorted(sort_ops)}")
    for op in ("drop_head", "dup_head", "empty_rec"):
        ex = next((m for m in sort_mutants if m["operator"] == op), None)
        print(f"  {op}: {'ok' if ex else 'missing'}")
        if ex:
            print(f"    {ex['code'][:100].strip()!r}")

    # filter_compilable on insertionSort: drop_head creates unbound vars, expect some filtered
    comp_sort = engine.filter_compilable(sort_mutants)
    comp_codes = {m["code"] for m in comp_sort}
    filtered = [m for m in sort_mutants if m["code"] not in comp_codes]
    print(f"\ninsertionSort filter_compilable: {len(sort_mutants)} total, {len(comp_sort)} compile, {len(filtered)} filtered")
    if filtered:
        print(f"  filtered ops: {sorted({m['operator'] for m in filtered})}")

    # try_proof_batch with func_name: simp-unfolding and induction-aware tactics
    gcd_code = """\
def gcd' (a b : Nat) : Nat :=
  if h : a = 0 then b else gcd' (b % a) a
termination_by a
decreasing_by
  apply Nat.mod_lt
  omega"""
    r = c.try_proof(gcd_code, "∀ b : Nat, gcd' 0 b = b", func_name="gcd'")
    print(f"\ngcd' base case: proved={r.proved} method={r.method!r}")

    length_code = """\
def length' : List Nat → Nat
  | [] => 0
  | _ :: t => 1 + length' t"""
    r2 = c.try_proof(length_code, "∀ l, length' l ≥ 0", func_name="length'")
    print(f"length' nonneg: proved={r2.proved} method={r2.method!r}")
    r3 = c.try_proof(length_code, "∀ l : List Nat, length' l = l.length", func_name="length'")
    print(f"length' = l.length: proved={r3.proved} method={r3.method!r}")
