#!/bin/bash
# Run the Korenblum evaluator on one candidate (default: the final candidate V68).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
CAND="${1:-ProofRefinement/Korenblum/Candidates/V68.lean}"
uv run ProofRefinement/Korenblum/Evaluator.py --file "$CAND"
