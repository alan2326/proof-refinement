#!/usr/bin/env bash
# Reset the loop's mutable state back to the V0 baseline.
#
# DESTRUCTIVE. Deletes every candidate above V0, every sprint contract, every
# verdict, the log, and the scratch space. The trusted surface, the harness, and
# V0 itself are untouched. Requires an explicit --yes.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
WS="$ROOT/ProofRefinement/PolygonPi"
cd "$ROOT"

if [[ "${1:-}" != "--yes" ]]; then
  cat >&2 <<EOF
This deletes all loop state above the V0 baseline:

  $WS/Candidates/        everything except V0.lean
  $WS/Sprint_Contracts/  everything except TEMPLATE.md
  $WS/Refinement_Log/    log.jsonl and all verdicts
  $WS/Scratch/           everything
  $WS/Proposals/         everything except README.md and TEMPLATE.md
  $WS/Experience.md      restored from seed/
  $WS/Bulletin.md        restored from seed/

The trusted surface (PolygonCore/, Proof/), the harness (Evaluator.py,
lemma.toml, scripts/) and Candidates/V0.lean are NOT touched.

Restoring Experience.md and Bulletin.md is not optional bookkeeping: they carry
the previous run's Mathlib findings, structural conclusions, and frontier. A
reset that left them in place would hand the next run its predecessor's answers
and make any run-to-run comparison meaningless.

Re-run with --yes to proceed.
EOF
  exit 2
fi

find "$WS/Candidates" -mindepth 1 -not -name 'V0.lean' -delete 2>/dev/null || true
find "$WS/Sprint_Contracts" -mindepth 1 -not -name 'TEMPLATE.md' -delete 2>/dev/null || true
find "$WS/Refinement_Log" -mindepth 1 -delete 2>/dev/null || true
find "$WS/Scratch" -mindepth 1 -delete 2>/dev/null || true
find "$WS/Proposals" -mindepth 1 -not -name 'README.md' -not -name 'TEMPLATE.md' -delete 2>/dev/null || true

# stale candidate build artifacts, so a deleted candidate cannot still be imported
find "$ROOT/.lake/build" -path '*ProofRefinement/PolygonPi/Candidates*' \
     -not -name 'V0.*' -delete 2>/dev/null || true

# the append-only notebook and the frontier must go back to their seed state too
for f in Experience.md Bulletin.md; do
  if [[ -f "$WS/seed/$f" ]]; then
    cp "$WS/seed/$f" "$WS/$f"
    echo "restored $f from seed/"
  else
    echo "WARNING: $WS/seed/$f missing — $f still carries the previous run's content" >&2
  fi
done

echo "reset done. Re-seeding the log with a fresh V0 evaluation:"
"$WS/scripts/polygonpi_eval_candidate.sh" V0
