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

    # seed shared packages from aeneas before cache get
    if [ "$name" != "aeneas" ]; then
        python3 - "$dir" "$REPO" <<'PYEOF' | tee -a "$log"
import json, os, sys, shutil
proj_dir, repo = sys.argv[1], sys.argv[2]
sys.path.insert(0, repo)
import lss_config
aeneas_dir = lss_config.project_dir('aeneas')
aeneas_manifest = os.path.join(aeneas_dir, 'lake-manifest.json')
proj_manifest = os.path.join(proj_dir, 'lake-manifest.json')
if not os.path.exists(aeneas_manifest) or not os.path.exists(proj_manifest):
    sys.exit(0)
with open(aeneas_manifest) as f:
    a = json.load(f)
with open(proj_manifest) as f:
    p = json.load(f)
aeneas_pkgs = {(x['url'], x['rev']): x['name'] for x in a.get('packages', [])}
pkg_base = os.path.join(proj_dir, '.lake/packages')
for pkg in p.get('packages', []):
    key = (pkg['url'], pkg['rev'])
    if key not in aeneas_pkgs:
        continue
    name = pkg['name']
    dir_name = name.strip('«»')  # strip « and »
    src = os.path.join(aeneas_dir, '.lake/packages', dir_name)
    dst = os.path.join(pkg_base, dir_name)
    if not os.path.isdir(src) or os.path.exists(dst):
        continue
    os.makedirs(pkg_base, exist_ok=True)
    shutil.copytree(src, dst, symlinks=True)
    print(f'seeded {name}')
PYEOF
    fi

    if python3 -c "
import json, sys
with open('$dir/lake-manifest.json') as f:
    d = json.load(f)
names = {p['name'] for p in d.get('packages', [])}
sys.exit(0 if 'mathlib' in names else 1)
" 2>/dev/null; then
        echo "running lake cache get..." | tee -a "$log"
        (cd "$dir" && lake cache get 2>&1 | tee -a "$log") || echo "lake cache get failed (non-fatal)" | tee -a "$log"
    fi

    echo "running lake build..." | tee -a "$log"
    (cd "$dir" && lake build --allow-empty 2>&1 | tee -a "$log")

    if [ "$name" = "aeneas" ]; then
        echo "running lake build Aeneas..." | tee -a "$log"
        (cd "$dir" && lake build Aeneas 2>&1 | tee -a "$log")
    fi

    if python3 -c "
import sys, tomllib
sys.path.insert(0, '$REPO')
import lss_config as c
p = c._cfg()['projects'].get('$name', {})
sys.exit(0 if p.get('has_hammer') else 1)
" 2>/dev/null; then
        echo "running lake build Hammer..." | tee -a "$log"
        (cd "$dir" && lake build Hammer 2>&1 | tee -a "$log")
    fi

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
