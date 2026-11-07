#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: bash scripts/korenblum_lake_build.sh <candidate-path-or-module>"
    exit 2
fi

WORKSPACE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(cd "$WORKSPACE_DIR/../.." && pwd)"  # the Lean project root (where lakefile.toml lives)
TARGET="$1"

case "$TARGET" in
    Candidates/*.lean)
        STEM="${TARGET#Candidates/}"
        STEM="${STEM%.lean}"
        TARGET="ProofRefinement.Korenblum.Candidates.${STEM}"
        ;;
esac

cd "$REPO_ROOT"
lake build "$TARGET"
