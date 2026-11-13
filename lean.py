import os
import re
import json
import hashlib
import time
import textwrap
from dataclasses import dataclass, field
import lss_config as _lss_config
import lean_server as _lean_server
import callgraph as _callgraph
import loader as _loader
import events

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
    axioms: list = field(default_factory=list)  # from the proof's LSS_PROOF verdict
    # rust units: does the proof hold with every external callee replaced by a
    # variable that only satisfies the callee's spec? None when not checked
    modular: bool | None = None
    needs_callee_body: list = field(default_factory=list)  # callees the proof looks inside
    blamed_callees: list = field(default_factory=list)  # on failure: callees whose spec is too weak

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

# rust crates whose env a LeanChecker keeps: crate -> (checker, rust project dir,
# hash of the crate text). every rust unit's context imports <crate>.Code.*
# (loader.py), which the aeneas project cannot load (and the crate's own lake
# project is never built), so such a text runs as commands in the crate's env
# instead: the callee specs proved so far are there, and hammer too when
# [proof] rust_hammer is on.
_CRATE_ENVS = {}
_CRATE_IMPORT = re.compile(r"^import\s+(\S+)\.Code\.\w+\s*$", re.MULTILINE)


def _crate_of(code):
    """the crate `code` imports, when a checker keeps that crate's env; else None."""
    for m in _CRATE_IMPORT.finditer(code or ""):
        if m.group(1) in _CRATE_ENVS:
            return m.group(1)
    return None


def _crate_dirs():
    return {pdir for _, pdir, _ in _CRATE_ENVS.values()}


def _cache_tag(code):
    """prefix for cache keys: a crate-routed text is keyed by its crate's text, so a
    result cached before the crate changed (or before routing) is never reused."""
    crate = _crate_of(code)
    return f"crate:{_CRATE_ENVS[crate][2]}\n" if crate else ""


def run_routed(code, timeout=None):
    """CheckResult of `code` run in its crate's env with its import lines dropped,
    or None when `code` imports no crate a checker keeps (or that env is down)."""
    crate = _crate_of(code)
    if crate is None:
        return None
    checker, pdir, _ = _CRATE_ENVS[crate]
    state = checker._aeneas_env_for(pdir)
    if not state["ok"]:
        return None
    rest = "\n".join(line for line in code.splitlines() if not line.strip().startswith("import "))
    return _lean_server.get_server(_lss_config.project_dir("aeneas")).check(rest, timeout=timeout, env=state["env"])


def run_in_project(code, project_dir=None):
    """Run lean with project dependencies (Mathlib or Aeneas); a rust unit's text
    runs in its crate env (run_routed)."""
    global _lean_call_count
    _lean_call_count += 1
    r = run_routed(code)
    if r is None:
        r = _lean_server.get_server(project_dir or _PROJECT_DIR).check(code)
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

def classify_function(lean_env, func_name):
    """what the tactic portfolio needs to know about func_name's own definition in
    lean_env: whether it calls itself, and whether it is defined by cases at its top
    (`|` equations, or a body that is one `match`), which gives one equation lemma
    per case; a recursive definition otherwise has one equation, its whole body, so
    `simp [f]` unfolds it forever. a definition not in lean_env (a Rust unit, whose
    text only imports its crate) is neither."""
    own, name = _find_def_in_text(lean_env, func_name)
    own = own or ""
    calls = len(re.findall(r"(?<![\w.'])" + re.escape(name or func_name) + r"(?![\w'])", own))
    all_defs = re.findall(r'def\s+([a-zA-Z_][a-zA-Z0-9_\'!?]*)', lean_env)
    eq, bar = own.find(":="), re.search(r"^\s*\|", own, re.MULTILINE)
    equations = bar is not None and (eq < 0 or bar.start() < eq)  # `|` cases before any `:=`
    return {
        "recursive": calls > 1,
        "by_cases": equations or (eq >= 0 and re.match(r"\s*match\b", own[eq + 2:]) is not None),
        "helpers": [d for d in all_defs if d != func_name and d != (name or func_name)],
    }


HAMMER = "hammer { disableGrind := true }"
# the closers after step*, in Aeneas's tutorial order (tests/lean/Tutorial/Solutions.lean:
# `step*; simp; simp_lists [*]`, or `step*; agrind`); agrind and grind close the list
# goals a shifted index leaves (`(x :: l)[i] = y` from `l[i - 1]? = some y`)
AENEAS_CLOSE = ("all_goals (try simp)\n  all_goals (try simp_lists [*])\n  "
                "all_goals first | (simp_all; done) | (simp_all <;> scalar_tac; done) | (agrind; done) | grind")
# the least time worth giving one proof attempt under a shared time budget
MIN_TRY = 5


def crate_env_error(checker, project_dir):
    """None when the crate's Lean code builds, else its first error line (run.py
    stops a function on it before any LLM call; tools/bench.py check reports it)."""
    if not project_dir:
        return None
    state = checker._aeneas_env_for(project_dir)
    if state["ok"]:
        return None
    errs = [ln.strip() for ln in state["error"].splitlines() if "error" in ln]
    return (errs[0] if errs else state["error"].strip())[:200] or "no error text"


def _hammer_selector():
    """the premise-selector line hammer runs under ("" for hammer's own default)."""
    if _lss_config.proof_cfg()['premise_selector'] == 'local':
        # Hammer's own default is `Cloud.premiseSelector <|> sineQuaNonSelector...`
        # (Hammer/Tactic.lean:22); this re-sets the same local fallback alone, so
        # hammer never calls out to leanpremise.net.
        return ('set_library_suggestions open Lean.LibrarySuggestions in '
                'sineQuaNonSelector.intersperse currentFile\n')
    return ""


def _hammer_code(lean_env, theorem_stmt):
    """(context, theorem): the context sets up hammer, the theorem is checked by
    lss_check_proof."""
    code = 'import Mathlib\nimport Hammer\n' + lean_env.rstrip() + '\n' + _hammer_selector()
    return code, f'theorem _hammer_proof : {theorem_stmt} := by {HAMMER}'


_AENEAS_LAYER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "aeneas_layer.lean")
_aeneas_layer_cache = None
_PROOF_CHECK_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "proof_check.lean")
_proof_check_cache = None


def proof_check_text():
    """lean/proof_check.lean: the lss_check_proof command every proof verdict
    comes from (no Aeneas or Mathlib dependency, so both tracks send it)."""
    global _proof_check_cache
    if _proof_check_cache is None:
        with open(_PROOF_CHECK_PATH, encoding="utf-8") as f:
            _proof_check_cache = f.read()
    return _proof_check_cache


def _escape_lean_str(s):
    return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def proof_check_call(theorems, name, heartbeats=0):
    """the lss_check_proof command for `theorems` (theorem declarations only,
    `name` among them); heartbeats=0 keeps the current maxHeartbeats."""
    return f'lss_check_proof "{_escape_lean_str(theorems)}" name:{name} heartbeats:{heartbeats}'


def helpers_command(text):
    """the lss_define_helpers command (proof_check.lean) for a Rust spec's helpers
    (synth.rust_helpers' `@[simp] def lss_hp_...` blocks): Lean parses the text itself and
    defines only plain `def lss_hp_...` commands, so nothing else hidden in a block runs;
    the command adds the @[simp] the blocks carry. "" for no helpers."""
    if not (text or "").strip():
        return ""
    defs = re.sub(r"(?m)^@\[simp\] def ", "def ", text.strip())
    return f'lss_define_helpers "{_escape_lean_str(defs)}"\n'


def parse_proof_verdicts(text):
    """every LSS_PROOF verdict in `text`, keyed by theorem name: the first one for a
    name, which lss_check_proof logs ahead of anything later in the text (try_aeneas's
    goal-logging attempt c is elaborated as it is, after every verdict)."""
    out = {}
    for m in re.finditer(r"LSS_PROOF (\{[^\n]*\})", text or ""):
        try:
            v = json.loads(m.group(1))
        except json.JSONDecodeError:
            continue
        out.setdefault(v.get("name"), v)
    return out


def _no_verdict(name, r, out):
    stage = "timeout" if r.timed_out else "memory" if r.mem_killed else "no_verdict"
    return {"name": name, "ok": False, "stage": stage, "detail": out.strip()[:300], "axioms": []}


def check_proofs(context, named, project_dir=None, timeout=None, heartbeats=0):
    """kernel verdicts for several proofs in one Lean call: `named` is
    [(name, theorems)], each checked by lss_check_proof after `context` (imports
    plus definitions; `import Lean` is added when it has no import, since the
    checker needs Lean). proof_check.lean is the server prelude, elaborated once
    per import block. returns ({name: verdict}, output); a verdict's "ok" is the
    only thing that may mark a proof proved."""
    global _lean_call_count
    _lean_call_count += 1
    calls = "\n".join(proof_check_call(theorems, name, heartbeats) for name, theorems in named)
    # a rust unit's context runs in its crate env, which already holds proof_check.lean
    r = run_routed(context.rstrip() + "\n" + calls, timeout=timeout)
    if r is None:
        if not any(line.strip().startswith("import ") for line in context.splitlines()):
            context = "import Lean\n" + context
        server = _lean_server.get_server(project_dir or _PROJECT_DIR)
        r = server.check(context.rstrip() + "\n" + calls, timeout=timeout, prelude=proof_check_text())
    out = (r.stdout or "") + (r.stderr or "")
    got = parse_proof_verdicts(out)
    return {name: got.get(name) or _no_verdict(name, r, out) for name, _ in named}, out


def check_proof(context, theorems, name, project_dir=None, timeout=None, heartbeats=0):
    """one kernel verdict, see check_proofs. returns (verdict, output)."""
    verdicts, out = check_proofs(context, [(name, theorems)], project_dir, timeout, heartbeats)
    return verdicts[name], out


def _aeneas_budget(tactic):
    """(heartbeats, seconds) for an aeneas-layer proof: hammer's own budget when the
    tactic calls hammer, so its admission, replay and modularity check get the
    same budget the proof itself had."""
    if HAMMER in tactic:
        return _lss_config.proof_cfg()["hammer_heartbeats"], max(90, _lss_config.server_cfg()["hammer_timeout"])
    return _lss_config.proof_cfg()["aeneas_heartbeats"], 90


def _aeneas_layer_text():
    global _aeneas_layer_cache
    if _aeneas_layer_cache is None:
        with open(_AENEAS_LAYER_PATH, encoding="utf-8") as f:
            _aeneas_layer_cache = f.read()
    return _aeneas_layer_cache


_TYPE_DECL = re.compile(r"^(?:@\[[^\]\n]*\]\s*)?(?:structure|inductive)\s+([\w.]+)", re.MULTILINE)


def _types_named(crate_text, text):
    """the crate's structure/inductive declarations (each up to its blank line)
    that `text` names, directly or through another picked type, in crate order."""
    blocks = {}
    for m in _TYPE_DECL.finditer(crate_text):
        end = crate_text.find("\n\n", m.end())
        blocks[m.group(1)] = crate_text[m.start():end if end >= 0 else len(crate_text)].strip()
    seen, grew = set(), True
    while grew:
        grew = False
        for n, b in blocks.items():
            if n not in seen and re.search(r"(?<![\w.])" + re.escape(n) + r"(?![\w])", text):
                seen.add(n)
                text += "\n" + b
                grew = True
    return [b for n, b in blocks.items() if n in seen]


class LeanChecker:
    def __init__(self, cache=None, project_dir=None):
        self._cache = cache
        self.lean_calls = 0
        self.project_dir = project_dir
        self._env_cache = {}  # (project_dir, requires_hammer) -> (ok, error)
        # project_dir -> {env, admitted: [(name, stmt, tactic, unit)], active: {unit: step lemma},
        #                 restarts, ok, error}
        self._aeneas_env = {}
        self._aeneas_admit_counter = {}  # project_dir -> next admitted-name index, never reused
        self._modular_counter = 0

    @events.layer("typecheck")
    def typecheck(self, code, project_dir=None):
        if project_dir is None:
            project_dir = self.project_dir
        key = _cache_tag(code) + code
        if self._cache:
            hit = self._cache.get(key)
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
            self._cache.put(key, [ok, errs])
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
        if project_dir in _crate_dirs():
            # a rust crate: its texts run in the crate env (Aeneas, so Mathlib's
            # tactics; Hammer when [proof] rust_hammer is on), nothing to import
            if requires_hammer and not _lss_config.proof_cfg()["rust_hammer"]:
                return False, "hammer is off for rust crates ([proof] rust_hammer)"
            return True, ""
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

    @events.layer("tactics")
    def try_proof_batch(self, lean_env, theorem_stmt, func_name=None,
                        allow_search_tactics=False, use_project=False, project_dir=None, timeout=None):
        if project_dir is None:
            project_dir = self.project_dir
        pdir = project_dir if project_dir else (_PROJECT_DIR if os.path.isdir(_PROJECT_DIR) else None)
        if pdir is None:
            return ProofResult(proved=False, method="", error="no project dir for mathlib")
        mathlib_ok = _crate_of(lean_env) is not None or self._precheck_env(pdir)[0]
        imports = "import Mathlib\n" if mathlib_ok else ""

        # layer 1: a tactic portfolio in two Lean calls, the function-aware and core
        # tactics first, then general automation only when they prove nothing: a
        # slow failure among the second can then never cost the first their verdicts.
        # every attempt has its own heartbeat budget ([proof] tactic_heartbeats), so a
        # failing tactic stops inside Lean instead of using up the call's time.
        first = ["rfl", "trivial", "assumption", "decide", "simp", "simp_all", "omega",
                 "intros; simp_all", "intros; omega",
                 "intro _ ; first | rfl | simp_all | omega | decide",
                 "constructor <;> first | rfl | simp_all",
                 "split <;> first | rfl | simp_all"]
        rest = ["bv_decide", "grind", "intros; grind"]
        if mathlib_ok:
            rest += ["norm_num", "ring", "linarith", "tauto", "aesop", "exact?",
                     "field_simp", "positivity", "gcongr", "bound", "group", "abel",
                     "add_group", "noncomm_ring", "field", "finiteness", "compute_degree", "fun_prop"]
        names = ""
        if func_name:
            info = classify_function(lean_env, func_name)
            # `simp [f]` with a recursive f defined without cases rewrites f's one
            # equation, its whole body, forever: such an f is only unfolded once at a
            # time (unfold, fun_cases, fun_induction), never handed to simp
            loops = info["recursive"] and not info["by_cases"]
            names = ", ".join(info["helpers"] if loops else [func_name] + info["helpers"])
            sn = f" [{names}]" if names else ""
            f = func_name
            # a statement in the gate's normal form (strategies.normalize_call): its
            # hypotheses define some arguments, substituted back before the call unfolds
            first += [f"intros; subst_vars; unfold {f}; simp_all{sn}",
                      f"intros; subst_vars; unfold {f}; split <;> simp_all{sn}",
                      f"intros; subst_vars; fun_cases {f} <;> simp_all{sn}"]
            if loops:
                # after one case split the arguments are often concrete, and then
                # unfolding f again ends: the one attempt that hands f to simp
                first.append(f"intros; subst_vars; fun_cases {f} <;> simp_all [{', '.join([f] + info['helpers'])}]")
            if info["recursive"]:
                first += [f"intros; fun_induction {f} <;> simp_all{sn}",
                          f"intros; fun_induction {f} <;> simp_all{sn} <;> omega",
                          f"intro x; induction x <;> simp_all{sn}",
                          f"intro x y; induction x generalizing y <;> simp_all{sn}",
                          f"intro x y; induction y generalizing x <;> simp_all{sn}"]
                rest += [f"intros; fun_induction {f} <;> grind{sn}"]
            if names:
                first += [f"simp{sn}", f"intros; simp{sn} <;> omega", f"intros; simp_all{sn}"]
                rest += [f"grind{sn}", f"intros; grind{sn}"]
                if mathlib_ok:
                    rest += [f"intros; simp{sn} <;> ring", f"simp{sn}; aesop"]
        else:
            first += ["intro x; cases x <;> simp [*]", "intro x; cases x <;> simp [*] <;> omega",
                      "simp [*]; omega", "simp_all; omega", "constructor <;> simp [*]", "constructor <;> omega",
                      "by_contra h; simp_all", "by_contra h; omega",
                      "exact Nat.zero_le _", "exact Nat.succ_pos _",
                      "exact ⟨rfl, rfl⟩", "refine ⟨?_, ?_⟩ <;> simp [*]"]
            if mathlib_ok:
                rest.append("intros; tauto")
        terms = [("rfl", "l1:rfl"), ("Iff.rfl", "l1:Iff.rfl"), ("fun x => rfl", "l1:term:fun x=>rfl"),
                 ("fun x y => rfl", "l1:term:fun x y=>rfl"), ("id", "l1:term:id")]
        batches = [[(f"by {t}", f"l1:{t}") for t in first] + terms, [(f"by {t}", f"l1:{t}") for t in rest]]

        # a Rust unit's attempts keep its preamble's budget, Aeneas's own maxHeartbeats
        heartbeats = 0 if _crate_of(lean_env) is not None else _lss_config.proof_cfg()["tactic_heartbeats"]
        env_stripped = lean_env.rstrip()
        result = ProofResult(proved=False, method="", error="", mathlib_available=mathlib_ok)
        k = 0  # entry names run on across the batches, so each names one attempt
        for entries in batches:
            named = [(f"_lss_p{k + i}", f"theorem _lss_p{k + i} : {theorem_stmt} := {suffix}")
                     for i, (suffix, _) in enumerate(entries)]
            k += len(entries)
            cache_key = ("v:" + _cache_tag(lean_env) + imports + env_stripped + f"\nheartbeats:{heartbeats}\n"
                         + "\n".join(t for _, t in named))
            hit = self._cache.get_proof(cache_key) if self._cache else None
            if hit is not None:
                result = ProofResult(proved=hit["proved"], method=hit["method"], error=hit.get("error", ""),
                                     mathlib_available=hit.get("mathlib_available", True),
                                     axioms=hit.get("axioms", []))
            else:
                verdicts, out = check_proofs(imports + env_stripped, named, project_dir=pdir, timeout=timeout,
                                             heartbeats=heartbeats)
                self.lean_calls += 1
                result = ProofResult(proved=False, method="", error=out.strip()[:200],
                                     mathlib_available=mathlib_ok)
                # entries are in priority order: the first one the checker accepts wins
                for (name, _), (_, label) in zip(named, entries):
                    v = verdicts[name]
                    if v["ok"]:
                        result = ProofResult(proved=True, method=label, error="",
                                             mathlib_available=mathlib_ok, axioms=v["axioms"])
                        break
                # a run cut short (timeout, memory cap) says nothing about the tactics: not cached
                if self._cache and not any(v["stage"] in ("timeout", "memory") for v in verdicts.values()):
                    self._cache.put_proof(cache_key, {
                        "proved": result.proved, "method": result.method, "error": result.error,
                        "mathlib_available": result.mathlib_available, "axioms": result.axioms,
                    })
            if result.proved:
                break
        return result

    def try_proof(self, lean_env, theorem_stmt, func_name=None,
                  allow_search_tactics=False, use_project=False, project_dir=None, timeout=None):
        if project_dir is None:
            project_dir = self.project_dir
        return self.try_proof_batch(lean_env, theorem_stmt, func_name=func_name,
                                    allow_search_tactics=allow_search_tactics,
                                    use_project=use_project, project_dir=project_dir, timeout=timeout)

    @events.layer("hammer")
    def try_hammer(self, lean_env, theorem_stmt, func_name=None, project_dir=None, timeout=None):
        # a rust unit's text runs in its crate env (check_proof routes it); any
        # other text runs in the configured hammer project; project_dir arg ignored
        if _crate_of(lean_env) is not None:
            pdir = None
            if not _lss_config.proof_cfg()["rust_hammer"]:
                return ProofResult(proved=False, method='l2:skipped (hammer off for rust)',
                                   error='[proof] rust_hammer is off', hammer_available=False)
        else:
            pdir = _lss_config.hammer_project_dir()
            if pdir is None:
                return ProofResult(proved=False, method='', error='no hammer project configured')
            hammer_ok, hammer_err = self._precheck_env(pdir, requires_hammer=True)
            if not hammer_ok:
                return ProofResult(proved=False, method='l2:skipped (hammer unavailable)',
                                   error=f'hammer unavailable: {hammer_err}', hammer_available=False)
        hammer_timeout = timeout or _lss_config.server_cfg()['hammer_timeout']
        context, theorem = _hammer_code(lean_env, theorem_stmt)
        t0 = time.time()
        v, out = check_proof(context, theorem, "_hammer_proof", project_dir=pdir, timeout=hammer_timeout)
        elapsed = time.time() - t0
        self.lean_calls += 1
        if v["stage"] == "timeout":
            return ProofResult(proved=False, method='', error=f'timeout after {hammer_timeout}s',
                               hammer_available=True)
        if v["ok"]:
            return ProofResult(proved=True, method=f'l2:hammer ({elapsed:.1f}s)', error='',
                               hammer_available=True, axioms=v["axioms"])
        return ProofResult(proved=False, method='', error=out.strip()[:200],
                           hammer_available=True)

    def _aeneas_env_text(self, project_dir):
        """(the crate env's text up to the crate's namespace, the premise selector
        command to run inside it): the crate, the options and opens, LSS's own commands
        and the aeneas layer (_aeneas_build_env). the bounded check builds its own env
        from the same text in a Lean server of its own (bounded._Lean._env)."""
        g = _callgraph.for_project(project_dir)
        crate, selector = g.crate_text, ""
        if _lss_config.proof_cfg()["rust_hammer"]:
            crate = crate.replace("import Aeneas", "import Aeneas\nimport Hammer", 1)
            selector = _hammer_selector()
        # the options and opens Aeneas writes at the top of every file: a joined file's
        # own end with its section (callgraph._concat_code_files), so they are set again
        # for what follows, Aeneas's maxHeartbeats the budget a Rust unit's attempts keep
        return (crate +
                "\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\n"
                "set_option linter.unusedVariables false\n"
                f"set_option maxHeartbeats {_loader.AENEAS_HEARTBEATS}\n"
                "set_option maxRecDepth 2048\n"
                "open Aeneas Aeneas.Std Result ControlFlow Error\n" +
                proof_check_text() + "\n" + _aeneas_layer_text()), selector

    def _aeneas_build_env(self, project_dir):
        """fresh env = crate text + the options and Aeneas opens the benches' own
        lean_code + lean_preamble use + the aeneas layer, then the crate's namespace
        entered, in the pinned aeneas project (a bench's own `open <crate>` inside it
        changes nothing: the crate's names already win there). LSS's own
        commands are elaborated before the crate's namespace is entered, so a crate
        defining a name they use (a `List` of its own) cannot change them; that env
        is kept as "env0" for the gate and the bounded check, which send their own
        Lean text and enter the namespace after it. maxHeartbeats is Aeneas's own
        (_aeneas_env_text): an attempt that sets its own cap sets it with `in`.
        printed once per crate since cost grows with crate size."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        server = _lean_server.get_server(aeneas_dir)
        g = _callgraph.for_project(project_dir)
        text, selector = self._aeneas_env_text(project_dir)
        _CRATE_ENVS[g.crate] = (self, project_dir, hashlib.sha256(g.crate_text.encode("utf-8")).hexdigest()[:16])
        t0 = time.time()
        r0 = r = server.check(text, timeout=_callgraph.CRATE_BUILD_TIMEOUT)
        if r0.rc == 0 and r0.new_env is not None:
            # inside the crate's namespace, not after `open`: a name the crate defines
            # (its List, Ord, max) is then the crate's, as in its own code, where `open`
            # left it ambiguous with Lean's and the statement did not elaborate
            r = server.check(f"namespace {g.crate}\n" + selector, timeout=120, env=r0.new_env)
        elapsed = time.time() - t0
        print(f"  aeneas env build: {project_dir} {elapsed:.1f}s")
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")
        ok = r.rc == 0 and r.new_env is not None
        if not ok:
            errs = _errors(combined)
            print(f"  aeneas env build failed: {(errs[0] if errs else combined.strip())[:200]}")
        state = {"env": r.new_env, "env0": r0.new_env, "crate": g.crate, "admitted": [], "active": {}, "helpers": {},
                 "restarts": server.stats()["restarts"], "ok": ok, "error": combined[:300]}
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
        if state["restarts"] != server.restarts():
            admitted, helpers = state["admitted"], state.get("helpers", {})
            state = self._aeneas_build_env(project_dir)
            if state["ok"]:
                if helpers:
                    self.ensure_helpers(project_dir, "\n\n".join(helpers.values()), state)
                for name, stmt, tactic, unit in admitted:
                    self._aeneas_admit(project_dir, state, name, stmt, tactic, unit)
        return state

    def ensure_helpers(self, project_dir, text, state=None):
        """define a Rust spec's helpers (synth.rust_helpers: `@[simp] def lss_hp_...`
        blocks, named by their text) in the crate's env, each once: a later spec with
        the same helper finds it there, and a rebuilt env defines them again. returns
        (ok, errors)."""
        state = state or self._aeneas_env_for(project_dir)
        if not state["ok"]:
            return False, [state["error"][:200]]
        blocks = [b for b in re.split(r"\n(?=@\[simp\] def )", text.strip()) if b.strip()]
        new = []
        for b in blocks:
            m = re.match(r"@\[simp\] def ([^\s:({\[]+)", b)
            if m and m.group(1) not in state["helpers"]:
                new.append((m.group(1), b.strip()))
        if not new:
            return True, []
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        r = server.check(helpers_command("\n\n".join(b for _, b in new)), timeout=120, env=state["env"])
        self.lean_calls += 1
        errs = _errors((r.stdout or "") + (r.stderr or ""))
        if r.rc != 0 or r.new_env is None or errs:
            return False, errs or [((r.stderr or "") + (r.stdout or "")).strip()[:200]]
        state["env"] = r.new_env
        state["helpers"].update(new)
        return True, []

    def known_helpers(self, project_dir, text):
        """the helpers already in the crate's env (ensure_helpers) that `text` uses,
        with the helpers they use, in the order they were defined: a statement that
        reuses a helper a callee's proved spec shows needs it in every layer."""
        known = (self._aeneas_env.get(project_dir) or {}).get("helpers", {})
        used, todo = set(), [text]
        while todo:
            t = todo.pop()
            for h, body in known.items():
                if h not in used and re.search(rf"(?<![\w.']){re.escape(h)}(?![\w'])", t):
                    used.add(h)
                    todo.append(body)
        return "\n\n".join(body for h, body in known.items() if h in used)

    @staticmethod
    def _own_step(state, unit):
        """(hide, restore) commands around a proof of a spec of `unit`: the unit's own
        step lemma is taken off while the proof runs, so step* goes through the
        recursive call by the theorem being proved (Aeneas's tutorial pattern,
        Tutorial/Solutions.lean) and not by a spec proved earlier for the same function
        (a zero-index list_nth_mut spec left `tl = Cons ?x ?tl` open on every later
        list_nth_mut spec). put back before a proved spec is registered, so
        lss_register_step combines or keeps exactly as it would."""
        own = state["active"].get(unit)
        return (f"attribute [-step] {own}\n", f"\nattribute [step] {own}") if own else ("", "")

    def _aeneas_admit(self, project_dir, state, name, stmt, tactic, unit):
        """extend the crate's env once with the winning proof, @[step]-registered.
        only on success: a failing admit (lower cap, flaky tactic, ...) keeps the
        old env and is not recorded, so it can't leave a sorry-backed @[step] lemma.
        success is the theorem's own LSS_PROOF verdict (kernel-checked, axioms
        audited), the same check the proof attempts themselves get. the unit's
        active step lemma (LSS_STEP's "active") is recorded for the modularity check."""
        aeneas_dir = _lss_config.project_dir("aeneas")
        heartbeats, timeout = _aeneas_budget(tactic)
        server = _lean_server.get_server(aeneas_dir)
        hide, restore = self._own_step(state, unit)
        text = (hide + proof_check_call(f"theorem {name} : {stmt} := by\n  {tactic}", name, heartbeats) +
                restore + f"\nlss_register_step {name}")
        r = server.check(text, timeout=timeout, env=state["env"])
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")
        verdict = parse_proof_verdicts(combined).get(name)
        ok = r.rc == 0 and r.new_env is not None and verdict is not None and verdict.get("ok") is True
        if ok:
            state["env"] = r.new_env
            state["admitted"].append((name, stmt, tactic, unit))
            for m in re.finditer(r"LSS_STEP (\{[^\n]*\})", combined):
                try:
                    step = json.loads(m.group(1))
                except json.JSONDecodeError:
                    continue
                if step.get("call") == name and step.get("active"):
                    state["active"][unit] = step["active"]
        else:
            errs = _errors(combined)
            print(f"  aeneas admit failed: {name}: {(errs[0] if errs else combined.strip())[:200]}")
        return r

    @events.layer("aeneas")
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

        g = _callgraph.for_project(rust_project_dir)
        unit = func_name if func_name in g.names else f"{g.crate}.{func_name}"
        # subst_vars: a statement in the gate's normal form (strategies.normalize_call)
        # defines an argument by a hypothesis `lss_a0 = List.Cons x tl`; substituted
        # back, the call is on the constructor again and `unfold` reaches its case
        start = f"lss_spec_form\n  try subst_vars\n  unfold {func_name}"
        attempts = [
            ("a", f"{start}\n  step*"),
            ("b", f"{start}\n  "
                  "step* <;> first | scalar_tac | simp_scalar | (simp_all <;> simp_lists [*]) | grind"),
            # Aeneas's tutorial order (tests/lean/Tutorial/Solutions.lean): step* does the
            # recursion through the theorem being proved, and what is left closes with simp
            # (a helper is a simp lemma), then simp_lists [*], then the closers
            ("p", f"{start}\n  step*\n  {AENEAS_CLOSE}"),
        ]
        if f"{unit}.body" in g.names:
            # a loop (Aeneas's `loop` combinator, never recursive itself) opened once: what
            # holds when the loop stops at once (Std/Primitives.lean's `loop` equation)
            attempts.append(("e", f"{start}\n  rw [Aeneas.Std.loop]\n  unfold {func_name}.body\n  step*\n  {AENEAS_CLOSE}"))
        proofs = attempts
        attempts = attempts + [("c", f"{start}\n  step*\n  lss_log_goals\n  all_goals sorry")]

        # every attempt but c is a proof, each checked by lss_check_proof; c only logs
        # the goals step* leaves open (closed by sorry, never a verdict)
        full = "\n".join(proof_check_call(f"theorem _aeneas_{label} : {candidate_stmt} := by\n  {tactic}",
                                           f"_aeneas_{label}", heartbeats)
                         for label, tactic in proofs)
        label_c, tactic_c = attempts[-1]
        full += (f"\nset_option maxHeartbeats {heartbeats} in\n"
                 f"theorem _aeneas_{label_c} : {candidate_stmt} := by\n  {tactic_c}")

        hide, _ = self._own_step(state, unit)
        r = server.check(hide + full, timeout=90 + 30 * (len(proofs) - 2), env=state["env"])
        self.lean_calls += 1
        combined = (r.stdout or "") + (r.stderr or "")

        goals = []
        for m in re.finditer(r"LSS_GOALS (\{[^\n]*\})", combined):
            try:
                goal = json.loads(m.group(1))
            except json.JSONDecodeError:
                continue
            goals.append(goal)
            events.emit("open_goal", unit=func_name, candidate_id=candidate_id,
                        head=goal.get("head", "?"))

        verdicts = parse_proof_verdicts(combined)

        for label, tactic in proofs:
            v = verdicts.get(f"_aeneas_{label}")
            if v and v.get("ok"):
                return self._aeneas_proved(rust_project_dir, g, unit, candidate_stmt, label, tactic, v)

        # h: b's closers, then hammer on each goal they leave; a call of its own,
        # with hammer's time and heartbeats, made only when a and b failed
        if _lss_config.proof_cfg()["rust_hammer"]:
            tactic_h = attempts[1][1] + f" | {HAMMER}"
            hb, timeout = _aeneas_budget(tactic_h)
            r = server.check(hide + proof_check_call(f"theorem _aeneas_h : {candidate_stmt} := by\n  {tactic_h}",
                                                     "_aeneas_h", hb), timeout=timeout, env=state["env"])
            self.lean_calls += 1
            v = parse_proof_verdicts((r.stdout or "") + (r.stderr or "")).get("_aeneas_h")
            if v and v.get("ok"):
                return self._aeneas_proved(rust_project_dir, g, unit, candidate_stmt, "h", tactic_h, v)
            state = self._aeneas_env_for(rust_project_dir)  # a hammer timeout restarts the server

        blamed = self._blame(g, state, unit, candidate_stmt, attempts[1][1])
        # what step* left, not the last closer's complaint about it
        error = ("open goal: " + goals[0].get("text", "")[:300]) if goals else combined.strip()[:200]
        return ProofResult(proved=False, method="", error=error, blamed_callees=blamed)

    @events.layer("aeneas")
    def try_loop(self, candidate_stmt, func_name, rust_project_dir, measure, invariant, candidate_id=None):
        """a loop unit's spec by Aeneas's loop pattern (documentation/proof-strategies.md
        Pattern B, Std/WP.lean `loop.spec_decr_nat`): `measure` (a Nat that drops on
        every iteration) and `invariant` (what holds at every iteration) are terms in
        the loop's state `s` and the statement's own variables; the body's goals close
        with step* and the closers. a ⦄div spec follows from the ⦃ ⦄ one (WP.spec_dspec)."""
        g = _callgraph.for_project(rust_project_dir)
        unit = func_name if func_name in g.names else f"{g.crate}.{func_name}"
        sigma = loop_state_type(g.def_text(unit) or "")
        if sigma is None or f"{unit}.body" not in g.names:
            return ProofResult(proved=False, method="", error="not a loop whose state this can name")
        state = self._aeneas_env_for(rust_project_dir)
        if not state["ok"]:
            return ProofResult(proved=False, method="", error=state["error"])

        def term(t, codomain):
            """the LLM's function of the state, typed at it: `fun s => e` (or a bare `e` in
            `s`) as the probe ran it, `(fun (s : σ) => e)`; any other shape
            (`fun (x, i) => e`) by ascription."""
            t = t.strip()
            m = re.match(r"^(?:fun|λ)\s+s\s*=>", t)
            if m or not re.match(r"^(?:fun|λ)\b", t):
                return f"(fun (s : {sigma}) => {t[m.end():].strip() if m else t})"
            return f"(({t}) : {sigma} → {codomain})"
        names = stmt_binder_names(candidate_stmt)  # `_` keeps an anonymous binder's place
        intro = (f"intro {' '.join(names)}\n  " if names else "") + "intros\n  "
        dspec = "apply Aeneas.Std.WP.spec_dspec\n  " if re.search(r"⦄\s*div", candidate_stmt) else ""
        tactic = (f"{intro}{dspec}unfold {func_name}\n  "
                  f"apply Aeneas.Std.loop.spec_decr_nat {term(measure, 'Nat')} {term(invariant, 'Prop')}\n  "
                  f"· intro s hs\n    try simp only\n    unfold {func_name}.body\n    step*\n    "
                  + AENEAS_CLOSE.replace("\n  ", "\n    ") + "\n  · first | rfl | simp | simp_all")
        heartbeats = _lss_config.proof_cfg()["aeneas_heartbeats"]
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        r = server.check(self._own_step(state, unit)[0] +
                         proof_check_call(f"theorem _aeneas_loop : {candidate_stmt} := by\n  {tactic}", "_aeneas_loop",
                                          heartbeats), timeout=120, env=state["env"])
        self.lean_calls += 1
        out = (r.stdout or "") + (r.stderr or "")
        v = parse_proof_verdicts(out).get("_aeneas_loop")
        if v and v.get("ok"):
            return self._aeneas_proved(rust_project_dir, g, unit, candidate_stmt, "loop", tactic, v)
        return ProofResult(proved=False, method="", error=((v or {}).get("detail") or out.strip())[:300])

    def _aeneas_proved(self, project_dir, g, unit, stmt, label, tactic, verdict):
        """a winning aeneas-layer attempt: check modularity, admit it, report it."""
        state = self._aeneas_env_for(project_dir)
        modular, body = self._modularity(g, state, unit, stmt, tactic)
        n = self._aeneas_admit_counter.get(project_dir, 0)
        self._aeneas_admit_counter[project_dir] = n + 1
        self._aeneas_admit(project_dir, state, f"lss_admitted_{n}", stmt, tactic, unit)
        return ProofResult(proved=True, method=f"aeneas:{label}", error="", proof_text=tactic,
                           axioms=verdict.get("axioms", []), modular=modular, needs_callee_body=body)

    def unit_context(self, project_dir, unit):
        """the Lean text a prompt about a rust unit gets, in place of the crate's
        whole Types.lean and Funs.lean: the types its definitions name, each
        external callee's specs proved so far this run (its definition while it
        has none), the rest of its recursion group, and its own definition."""
        g = _callgraph.for_project(project_dir)
        name = unit if unit in g.names else f"{g.crate}.{unit}"
        proved = {}
        state = self._aeneas_env.get(project_dir) or {"admitted": [], "helpers": {}}
        for _, stmt, _, u in state["admitted"]:
            proved.setdefault(u, []).append(stmt)
        helpers = state.get("helpers", {})
        parts = []
        for c in g.callees_outside_scc(name):
            if proved.get(c):
                # a proved spec that states its property through a helper shows the helper
                used = [h for h in helpers if any(re.search(rf"\b{re.escape(h)}\b", st) for st in proved[c])]
                parts.append("".join(helpers[h] + "\n" for h in used)
                             + f"-- proved specs of {c}:\n" + "\n".join(f"--   {st}" for st in proved[c]))
            else:
                parts.append(g.def_text(c) or "")
        i = g.scc_of(name)
        group = sorted(g.sccs[i] - {name}) if i is not None else []
        parts += [g.def_text(m) or "" for m in group] + [g.def_text(name) or ""]
        body = "\n\n".join(p for p in parts if p)
        return "\n\n".join(_types_named(g.crate_text, body) + [body])

    def _modular_check(self, state, unit, stmt, tactic, abstract, inline):
        """one ∀-abstraction variant (lss_modular): `abstract` is [(callee, spec
        lemma or None)], `inline` the callees replaced by their bodies. the env is
        never kept. returns the LSS_PROOF verdict."""
        server = _lean_server.get_server(_lss_config.project_dir("aeneas"))
        heartbeats, timeout = _aeneas_budget(tactic)
        tag = f"lss_mod_{self._modular_counter}"
        self._modular_counter += 1
        # the proof's lines go into one tactic block, so they must share one indentation
        first, _, rest = tactic.partition("\n")
        flat = first.strip() + ("\n" + textwrap.dedent(rest) if rest else "")
        abs_txt = ", ".join(f"{c} {lemma or '_'}" for c, lemma in abstract)
        text = (self._own_step(state, unit)[0] + f'lss_modular {tag} unit:{unit} stmt:"{_escape_lean_str(stmt)}" '
                f'tactic:"{_escape_lean_str(flat)}" abstract:[{abs_txt}] inline:[{", ".join(inline)}] '
                f'heartbeats:{heartbeats}')
        r = server.check(text, timeout=timeout, env=state["env"])
        self.lean_calls += 1
        out = (r.stdout or "") + (r.stderr or "")
        v = parse_proof_verdicts(out).get(f"{tag}.proof") or _no_verdict(f"{tag}.proof", r, out)
        events.emit("modular", unit=unit, ok=v["ok"], stage=v["stage"],
                    abstract=[c for c, _ in abstract], inline=list(inline))
        return v

    def _modularity(self, g, state, unit, stmt, tactic):
        """(modular, needs_callee_body) for a proof that just passed: re-run it with
        every external callee (outside the unit's own SCC) replaced by a variable
        that satisfies only that callee's active spec. when that fails, each callee
        is left concrete in turn; the ones that make it pass are the callees whose
        body the proof needs. recursive units are not checked (None)."""
        if g.recursive(unit):
            return None, []
        # a loop's body is part of its loop (loader.py: never a unit of its own), not a callee
        callees = [(c, state["active"].get(c)) for c in g.callees_outside_scc(unit) if c != f"{unit}.body"]
        if not callees:
            return True, []
        if self._modular_check(state, unit, stmt, tactic, callees, [])["ok"]:
            return True, []
        body = [c for c, _ in callees
                if self._modular_check(state, unit, stmt, tactic, [x for x in callees if x[0] != c], [])["ok"]]
        return False, body

    def _blame(self, g, state, unit, stmt, tactic):
        """callees whose spec is too weak for a proof that failed: with one
        callee's body inlined (the others keep their step lemmas) the proof goes
        through. recursive units are not checked."""
        if g.recursive(unit):
            return []
        blamed = [c for c in g.callees_outside_scc(unit) if c != f"{unit}.body"
                  and self._modular_check(state, unit, stmt, tactic, [], [c])["ok"]]
        for c in blamed:
            events.emit("blame", unit=unit, callee=c)
        return blamed

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


_OPEN, _CLOSE = "({[⦃", ")}]⦄"


def _group_end(text, i):
    """the index after the bracket group that starts at text[i]."""
    depth = 0
    for j in range(i, len(text)):
        if text[j] in _OPEN:
            depth += 1
        elif text[j] in _CLOSE:
            depth -= 1
            if depth == 0:
                return j + 1
    raise ValueError("unbalanced brackets")


def binder_groups(text):
    """(names, type) of each binder group at the start of `text` (`(a b : T) {U : Type}
    [inst : C]`; an anonymous instance `[C]` binds `_`), and the rest of the text."""
    out, i = [], 0
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text) or text[i] not in _OPEN:
            return out, text[i:]
        j = _group_end(text, i)
        inner = text[i + 1:j - 1]
        depth, colon = 0, -1
        for k, c in enumerate(inner):
            depth += (c in _OPEN) - (c in _CLOSE)
            if c == ":" and depth == 0 and not inner.startswith(":=", k):
                colon = k
                break
        out.append((inner[:colon].split() or ["_"], inner[colon + 1:].strip()) if colon >= 0 else (["_"], inner.strip()))
        i = j


def stmt_binder_names(stmt):
    """the names a statement's leading ∀ binders bind, in order, over every `∀ ... ,`."""
    names, rest = [], stmt.strip()
    while rest.startswith("∀") or rest.startswith("forall"):
        rest = rest[1:] if rest.startswith("∀") else rest[len("forall"):]
        groups, rest = binder_groups(rest)
        if not groups:  # `∀ x y, ...` or `∀ x y : T, ...` without brackets
            m = re.match(r"\s*([^,(]+),", rest)
            if not m:
                break
            names += m.group(1).split(":", 1)[0].split()
            rest = rest[m.end():].strip()
            continue
        names += [n for ns, _ in groups for n in ns]
        rest = rest.lstrip()
        if not rest.startswith(","):
            break
        rest = rest[1:].strip()
    return names


def loop_state_type(def_text):
    """the Lean type of a loop function's state, the tuple Aeneas passes to `loop`
    (`def f (a : A) (b : B) : Result R := loop (fun x => f.body x.1 x.2) (a, b)` gives
    `A × B`), or None when the state is not a tuple of the function's own binders."""
    m = re.search(r"\bdef\s+\S+", def_text or "")
    if not m:
        return None
    try:
        groups, _ = binder_groups(def_text[m.end():])
        types = {n: t for ns, t in groups for n in ns}
        k = re.search(r"\bloop\s*\(", def_text)
        if not k:
            return None
        after = def_text[_group_end(def_text, k.end() - 1):].lstrip()
        if after.startswith("("):
            state = after[1:_group_end(after, 0) - 1]
        else:
            state = re.match(r"[^\s)]+", after).group(0)  # type: ignore[union-attr]
    except (ValueError, AttributeError):
        return None
    parts, depth, cur = [], 0, ""
    for c in state:
        depth += (c in _OPEN) - (c in _CLOSE)
        if c == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += c
    parts.append(cur.strip())
    if not all(p in types for p in parts):
        return None
    return " × ".join(f"({types[p]})" for p in parts)


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
        pat = re.compile(r'(?:@\[.*?\]\s*)?def\s+' + re.escape(name) + r"(?![\w']|\.(?!\{))")
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


class Cache:
    CACHE_VERSION = 3  # 3: proof results come from LSS_PROOF verdicts

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

