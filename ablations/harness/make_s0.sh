#!/usr/bin/env bash
# Rebuild S0 from scratch, reproducibly.  Never mutates the korenblum/ source tree.
set -euo pipefail

SRC="${KORENBLUM_SRC:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../korenblum" && pwd)}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DST=$ROOT/workspaces/S0_korenblum

echo "[make_s0] fresh copy of $SRC -> $DST"
rm -rf "$DST"
mkdir -p "$DST"
rsync -a --exclude='.lake' --exclude='.uv-cache' --exclude='.venv' \
         --exclude='.git' "$SRC"/ "$DST"/
cp -al "$SRC"/.lake      "$DST"/.lake        # hardlink: 7.8G of prebuilt Mathlib
[ -d "$SRC"/.uv-cache ] && cp -al "$SRC"/.uv-cache  "$DST"/.uv-cache
[ -d "$SRC"/.venv ]     && cp -a  "$SRC"/.venv      "$DST"/.venv

echo "[make_s0] reconstructing sprint-083 state"
python3 "$ROOT/harness/reconstruct_s0.py" "$DST"

# The workspace's .claude/settings.local.json enables the `lean-lsp` and
# `lean-explore` MCP servers (the planner/generator agent definitions grant 31
# MCP tools between them), but the .mcp.json that DEFINES them was never in the
# korenblum tree -- it lives in the sibling grothendieck workspace. Without it
# Arm A would run with 31 fewer tools than the original run had, understating
# the framework. Restore it verbatim.
# The public release ships a template without the lean-explore API key;
# add your own key there if you want that server available.
cp "$ROOT"/harness/mcp.template.json "$DST"/.mcp.json
echo "[make_s0] installed .mcp.json from harness/mcp.template.json"

echo "[make_s0] done."
