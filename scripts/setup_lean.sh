#!/usr/bin/env bash
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
LOG_DIR="$REPO/.lss/setup"
mkdir -p "$LOG_DIR"

get_build_dir() {
    python3 -c "
import sys
sys.path.insert(0, '$REPO')
import lss_config
print(lss_config.project_dir('$1'))
"
}

build_one() {
    local name="$1"
    local pin="$REPO/lean/$name"
    local dir
    dir=$(get_build_dir "$name")
    local log="$LOG_DIR/$name.log"

    echo "=== $name: $dir ===" | tee "$log"
    mkdir -p "$dir"

    cp "$pin/lakefile.toml"  "$dir/lakefile.toml"
    cp "$pin/lean-toolchain" "$dir/lean-toolchain"

    if [ -f "$pin/lake-manifest.json" ]; then
        cp "$pin/lake-manifest.json" "$dir/lake-manifest.json"
        echo "pinned manifest copied" | tee -a "$log"
    else
        echo "running lake update..." | tee -a "$log"
        (cd "$dir" && lake update 2>&1 | tee -a "$log")
        cp "$dir/lake-manifest.json" "$pin/lake-manifest.json"
        echo "manifest saved to $pin/lake-manifest.json" | tee -a "$log"
    fi

    if python3 -c "
import json, sys
with open('$dir/lake-manifest.json') as f:
    d = json.load(f)
names = {p['name'] for p in d.get('packages', [])}
sys.exit(0 if 'mathlib' in names else 1)
" 2>/dev/null; then
        echo "running lake exe cache get..." | tee -a "$log"
        (cd "$dir" && lake exe cache get 2>&1 | tee -a "$log") || echo "cache get failed (non-fatal)" | tee -a "$log"
    fi

    echo "running lake build..." | tee -a "$log"
    (cd "$dir" && lake build --allow-empty 2>&1 | tee -a "$log")
    echo "=== $name done ===" | tee -a "$log"
}

case "${1:-}" in
    all)
        build_one aeneas
        build_one lean-native
        ;;
    "")
        echo "usage: $0 <name>|all" >&2
        exit 1
        ;;
    *)
        build_one "$1"
        ;;
esac
