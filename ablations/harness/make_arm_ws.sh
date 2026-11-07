#!/usr/bin/env bash
# Clone the pristine S0 snapshot into a per-arm workspace.
# Usage: make_arm_ws.sh armA|armB|armC
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
S0=$ROOT/workspaces/S0_korenblum
ARM=${1:?usage: make_arm_ws.sh armA|armB|armC}
DST=$ROOT/workspaces/$ARM

[ -d "$S0" ] || { echo "S0 missing; run harness/make_s0.sh"; exit 1; }

echo "[make_arm_ws] $S0 -> $DST"
rm -rf "$DST"; mkdir -p "$DST"
rsync -a --exclude='.lake' --exclude='.uv-cache' --exclude='.venv' "$S0"/ "$DST"/
cp -al "$S0"/.lake     "$DST"/.lake       # hardlink prebuilt Mathlib
cp -al "$S0"/.uv-cache "$DST"/.uv-cache
cp -a  "$S0"/.venv     "$DST"/.venv
echo "[make_arm_ws] done: $(du -sh --apparent-size "$DST" | cut -f1) apparent"
