#!/usr/bin/env bash
# Clone the pristine S0^16 snapshot into a per-arm workspace (sect. 13.3).
# Usage: make_arm_ws_groth16.sh groth16_armA|groth16_armB|groth16_armC
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
S0=$ROOT/workspaces/S0_grothendieck016
ARM=${1:?usage: make_arm_ws_groth16.sh groth16_armA|groth16_armB|groth16_armC}
DST=$ROOT/workspaces/$ARM

[ -d "$S0" ] || { echo "S0^16 missing; run harness/make_s0_grothendieck016.sh"; exit 1; }

echo "[make_arm_ws_groth16] $S0 -> $DST"
rm -rf "$DST"; mkdir -p "$DST"
rsync -a --exclude='.lake' --exclude='.venv' "$S0"/ "$DST"/
cp -al "$S0"/.lake "$DST"/.lake      # hardlink prebuilt Mathlib + build cache
cp -a  "$S0"/.venv "$DST"/.venv      # bit-for-bit env copy (agents may mutate)

# Re-point the venv's editable-install .pth at this arm's root.
PTH="$DST/.venv/lib/python3.13/site-packages/grothendieck.pth"
rm -f "$PTH"
printf '%s\n' "$DST" > "$PTH"

echo "[make_arm_ws_groth16] done: $(du -sh --apparent-size "$DST" | cut -f1) apparent"
