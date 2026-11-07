#!/usr/bin/env bash
# Build one candidate module. Usage: polygonpi_lake_build.sh V3
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

if [[ $# -lt 1 ]]; then
  echo "usage: $(basename "$0") <candidate-name>   e.g. V0" >&2
  exit 2
fi
NAME="${1%.lean}"
NAME="$(basename "$NAME")"

exec lake build "ProofRefinement.PolygonPi.Candidates.${NAME}"
