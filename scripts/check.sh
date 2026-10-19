#!/usr/bin/env bash
# the merge check, run locally: lint, types, drift, the static tests the way a
# machine without Lean runs them, then the Lean tests and a leftover-process check.
#   bash scripts/check.sh          everything (the merge criterion)
#   bash scripts/check.sh static   lint, types, drift and static tests only (no Lean)
# python is $LSS_PYTHON, else python3; ruff and pyright==1.1.391 are pip packages
# in that python. the last line is CHECK PASS or CHECK FAIL.
set -u
cd "$(dirname "$0")/.." || exit 1
PY="${LSS_PYTHON:-$(command -v python3)}"
mode="${1:-full}"
fail=()

run() {  # run <label> <command...>
  local label=$1; shift
  echo "== $label"
  if "$@"; then echo "   ok: $label"; else echo "   FAILED: $label"; fail+=("$label"); fi
}

# the static part sees no Lean at all: an empty HOME hides ~/lss_lean, ~/.elan
# and ~/rust_benchmarks, and PATH loses every elan entry.
bare_home=$(mktemp -d)
bare_path=$(printf '%s' "$PATH" | tr ':' '\n' | grep -v '\.elan' | paste -sd: -)
bare() { HOME="$bare_home" PATH="$bare_path" "$PY" "$@"; }

run "lint" "$PY" -m ruff check .
run "types" "$PY" -m pyright
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
  # every Lean process these tests start carries this id in its environment,
  # so the leftover check never looks at another project's processes.
  export LSS_CHECK_ID="check-$$-$(date +%s%N)"
  for d in "$HOME/.elan/bin" "$HOME/.cargo/bin"; do
    [ -d "$d" ] && PATH="$d:$PATH"
  done
  run "pins" "$PY" tests/test_pins.py
  run "server" "$PY" tests/test_server.py
  run "unit graph" "$PY" tests/test_unitgraph.py
  run "aeneas layer" "$PY" tests/test_aeneas_layer.py
  run "spec gate" "$PY" tests/test_spec_gate.py
  run "translation check" "$PY" tests/test_translation_check.py
  run "proof trust" "$PY" tests/test_proof_trust.py
  run "bounded check" "$PY" tests/test_bounded.py
  run "speed and cost" "$PY" tests/test_cost.py
  run "harness" "$PY" tests/test_bench.py

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

echo
if [ ${#fail[@]} -eq 0 ]; then echo "CHECK PASS"; exit 0; fi
echo "failed: ${fail[*]}"
echo "CHECK FAIL"
exit 1
