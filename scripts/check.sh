#!/usr/bin/env bash
# the merge check, run locally exactly as the GitHub workflow ran it (it was
# replaced by this script in e3da018; the jobs below are its jobs):
#   - what is checked is the commit: a clean clone of HEAD, never the working
#     tree, so an uncommitted or untracked file cannot make it pass;
#   - lint, types, drift and the static tests run in fresh Python 3.12
#     environments with requirements.txt installed from scratch (ruff at its
#     latest release, pyright==1.1.391), the static tests with no Lean in sight;
#   - the Lean tests run with $LSS_PYTHON on this machine (the self-hosted
#     runner's setup), followed by a leftover-process check.
#   bash scripts/check.sh          everything (the merge criterion)
#   bash scripts/check.sh static   lint, types, drift and static tests only (no Lean)
# Python 3.12 is $LSS_CI_PYTHON, else python3.12 on PATH. the last line is
# CHECK PASS or CHECK FAIL.
set -u
cd "$(dirname "$0")/.." || exit 1
repo=$(pwd)
mode="${1:-full}"
fail=()

run() {  # run <label> <command...>
  local label=$1; shift
  echo "== $label"
  if "$@"; then echo "   ok: $label"; else echo "   FAILED: $label"; fail+=("$label"); fi
}
finish() {
  echo
  if [ ${#fail[@]} -eq 0 ]; then echo "CHECK PASS"; exit 0; fi
  echo "failed: ${fail[*]}"
  echo "CHECK FAIL"
  exit 1
}

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# the commit, cloned clean (the workflow's actions/checkout)
head=$(git -C "$repo" rev-parse HEAD) || { fail+=("not a git repository"); finish; }
echo "== checking commit $head"
if [ -n "$(git -C "$repo" status --porcelain)" ]; then
  echo "   note: uncommitted changes are not part of this check:"
  git -C "$repo" status --porcelain | head -10 | sed 's/^/     /'
fi
git clone -q "$repo" "$work/src" && git -C "$work/src" checkout -q --detach "$head" \
  || { fail+=("clean clone of $head"); finish; }
cd "$work/src" || exit 1

# fresh Python 3.12 environments, one per kind of job (the workflow's setup-python 3.12)
ci_py="${LSS_CI_PYTHON:-$(command -v python3.12)}"
if [ -z "$ci_py" ] || ! "$ci_py" -c 'import sys; sys.exit(sys.version_info[:2] != (3, 12))' 2>/dev/null; then
  fail+=("Python 3.12 (set LSS_CI_PYTHON to a python3.12, or put python3.12 on PATH)")
  finish
fi
venv() {  # venv <dir> <extra packages...>
  local d=$1; shift
  "$ci_py" -m venv "$d" && "$d/bin/python" -m pip install -q --upgrade pip \
    && "$d/bin/python" -m pip install -q -r requirements.txt "$@"
}
run "environment: lint and types" venv "$work/tools" ruff pyright==1.1.391
run "environment: static tests" venv "$work/tests"
TOOLS="$work/tools/bin/python"
PY="$work/tests/bin/python"

# the static part sees no Lean at all: an empty HOME hides ~/lss_lean, ~/.elan
# and ~/rust_benchmarks, and PATH loses every elan entry.
bare_home=$(mktemp -d)
bare_path=$(printf '%s' "$PATH" | tr ':' '\n' | grep -v '\.elan' | paste -sd: -)
bare() { HOME="$bare_home" PATH="$bare_path" "$PY" "$@"; }

run "lint" "$TOOLS" -m ruff check .
run "types" "$TOOLS" -m pyright
run "pins (static)" bare tests/test_pins.py --static
run "manifest" bare scripts/derive_manifest.py --check
run "compile" bare -m compileall -q .
run "imports" bare -c "import lean, synth, strategies, metrics, benchmarks, loader, run, callgraph, incremental, traits, divergence, gate, bounded"
run "unit graph (static)" bare tests/test_unitgraph.py --static
run "aeneas layer (static)" bare tests/test_aeneas_layer.py --static
run "spec gate (static)" bare tests/test_spec_gate.py --static
run "events and pricing" bare tests/test_events.py
run "translation check (static)" bare tests/test_translation_check.py --static
run "proof trust (static)" bare tests/test_proof_trust.py --static
run "bounded check (static)" bare tests/test_bounded.py --static
run "speed and cost (static)" bare tests/test_cost.py --static
run "harness (static)" bare tests/test_bench.py --static
rm -rf "$bare_home"

if [ "$mode" != "static" ]; then
  LPY="${LSS_PYTHON:-$(command -v python3)}"
  # every Lean process these tests start carries this id in its environment,
  # so the leftover check never looks at another project's processes.
  export LSS_CHECK_ID="check-$$-$(date +%s%N)"
  for d in "$HOME/.elan/bin" "$HOME/.cargo/bin"; do
    [ -d "$d" ] && PATH="$d:$PATH"
  done
  run "pins" "$LPY" tests/test_pins.py
  run "server" "$LPY" tests/test_server.py
  run "unit graph" "$LPY" tests/test_unitgraph.py
  run "aeneas layer" "$LPY" tests/test_aeneas_layer.py
  run "spec gate" "$LPY" tests/test_spec_gate.py
  run "translation check" "$LPY" tests/test_translation_check.py
  run "proof trust" "$LPY" tests/test_proof_trust.py
  run "bounded check" "$LPY" tests/test_bounded.py
  run "speed and cost" "$LPY" tests/test_cost.py
  run "harness" "$LPY" tests/test_bench.py

  leftover() {
    for p in /proc/[0-9]*; do
      case "$(basename "$(readlink "$p/exe" 2>/dev/null)")" in
        lean|lake|repl) ;;
        *) continue ;;
      esac
      tr '\0' '\n' < "$p/environ" 2>/dev/null | grep -qx "LSS_CHECK_ID=$LSS_CHECK_ID" && echo "${p#/proc/}"
    done
  }
  left=$(leftover)
  for _ in $(seq 10); do [ -z "$left" ] && break; sleep 1; left=$(leftover); done
  echo "== no leftover lean/lake/repl"
  if [ -n "$left" ]; then
    for pid in $left; do echo "   leftover pid=$pid $(tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null)"; done
    fail+=("leftover lean processes")
  else
    echo "   ok: none"
  fi
fi

finish
