#!/usr/bin/env bash
# Run the full evaluator on one candidate.
# Usage: polygonpi_eval_candidate.sh V3 [--no-log] [--skip-compile]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

if [[ $# -lt 1 ]]; then
  echo "usage: $(basename "$0") <candidate-name> [evaluator flags]" >&2
  exit 2
fi
NAME="${1%.lean}"
NAME="$(basename "$NAME")"
shift

exec env UV_CACHE_DIR="$ROOT/.uv-cache" uv run \
  ProofRefinement/PolygonPi/Evaluator.py \
  --file "ProofRefinement/PolygonPi/Candidates/${NAME}.lean" "$@"
