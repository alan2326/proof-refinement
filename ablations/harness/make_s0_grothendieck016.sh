#!/usr/bin/env bash
# Build S0_grothendieck016 reproducibly. Never mutates the grothendieck/ source tree.
#
# Sprint-016 structural ablation (design doc sect. 13). Same commit-based
# construction as make_s0_grothendieck.sh (sect. 12.2), re-pinned:
#   S0^16 = 5db00044 (2026-04-30T07:40:56Z): after verdict_015 landed
#   (07:40:33, V11 accepted at Cr_val = 1), before the sprint-016 planner's
#   first artifact (07:43:08). Everything post-anchor (sprint_016+ contracts /
#   verdicts, V12+, u_zz.py, h_u_zz_oracle, docs/HARNESS_OPERATOR_TIPS.md,
#   all later Bulletin/Experience rows) is absent by construction.
#
# Verified 2026-07-29: lean-toolchain / lakefile.toml / lake-manifest.json have
# zero drift 5db00044 -> live, so the 40 GB .lake hardlink is valid; agent and
# skill definitions at 5db00044 are byte-identical to e86a00f0, so every
# sect. 12 harness-surface gate result carries over.
set -euo pipefail

SRC="${GROTHENDIECK_SRC:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../grothendieck" && pwd)}"
S0_COMMIT=5db00044
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DST=$ROOT/workspaces/S0_grothendieck016

echo "[make_s0_groth16] materializing $S0_COMMIT -> $DST"
rm -rf "$DST"
mkdir -p "$DST"

# 1. Tracked tree exactly as of S0^16. git archive, not worktree/clone: the
#    workspace must carry no .git that exposes post-anchor history.
git -C "$SRC" archive "$S0_COMMIT" | tar -x -C "$DST"

# 2. Build cache: hardlink (toolchain drift = zero, verified above).
rm -rf "$DST/.lake"
cp -al "$SRC/.lake" "$DST/.lake"

# 3. Python env for Evaluator.py oracles. Same deviation as sect. 12.2 (the
#    S0-era env is unrecoverable; current uv venv, bit-for-bit copy).
cp -a "$SRC/.venv" "$DST/.venv"
cp "$SRC/pyproject.toml" "$SRC/uv.lock" "$DST/"
PTH="$DST/.venv/lib/python3.13/site-packages/grothendieck.pth"
rm -f "$PTH"
printf '%s\n' "$DST" > "$PTH"   # re-point editable install: leak + skew fix

# 4. MCP servers + local settings (untracked, so not in the archive). Same
#    known deviation as sect. 12.2 (post-anchor deny rules, uniform across
#    agentic arms; left in place rather than edited mid-study).
cp "$SRC/.mcp.json" "$DST/.mcp.json"
mkdir -p "$DST/.claude"
cp "$SRC/.claude/settings.local.json" "$DST/.claude/settings.local.json"

# 4b. The certified b-series cache (gitignored *.json; every oracle loads it
#     via _phi_loader). Byte-identical to a pre-anchor 2026-04-30T01:33
#     snapshot (mtime 2026-02-19) -- pre-dates S0^16 (07:40:56) too, so it
#     carries no post-anchor information.
mkdir -p "$DST/outputs"
cp "$SRC"/grothendieck/proof/certified/b_series_eta0p01_K250_dps100.json \
   "$DST/outputs/"

# 5. Reconstruct Refinement_Log/log.jsonl from verdict-embedded rows. At
#    5db00044 the tree carries verdicts <= 015 only, so the reconstruction is
#    automatically pre-anchor.
python3 "$ROOT/harness/reconstruct_log_groth.py" "$DST/ProofRefinement/Lemma54"

# 6. Fresh single-commit repo: nothing post-anchor reachable.
printf '\n# ablation workspace\n.lake/\n.venv/\n.uv-cache/\n' >> "$DST/.gitignore"
git -C "$DST" init -q -b main
git -C "$DST" add -A
git -C "$DST" -c user.name=ablation -c user.email=ablation@local \
  commit -qm "S0^16 snapshot (grothendieck $S0_COMMIT, post-sprint-015)"

echo "[make_s0_groth16] done: $(du -sh "$DST" | cut -f1) real, $(du -sh --apparent-size "$DST" | cut -f1) apparent"
