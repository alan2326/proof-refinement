#!/usr/bin/env bash
# Create one scoped checkpoint commit for the Korenblum harness if there are
# in-scope changes. This intentionally avoids sweeping in unrelated repo edits.

set -euo pipefail

WORKSPACE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(cd "$WORKSPACE_DIR/../.." && pwd)"  # the Lean project root (where lakefile.toml lives)
cd "$REPO_ROOT"

if [[ $# -gt 0 ]]; then
    PATHS=("$@")
else
    PATHS=("ProofRefinement/Korenblum")
fi

if [[ -n "$(git diff --name-only --diff-filter=U -- "${PATHS[@]}")" ]]; then
    echo "checkpoint: skipped because there are unresolved conflicts in scope"
    exit 1
fi

if [[ -z "$(git status --porcelain -- "${PATHS[@]}")" ]]; then
    echo "checkpoint: no in-scope changes"
    exit 0
fi

git add -A -- "${PATHS[@]}"

if git diff --cached --quiet -- "${PATHS[@]}"; then
    echo "checkpoint: nothing staged in scope"
    exit 0
fi

STAMP="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
git commit -m "checkpoint(korenblum): ${STAMP}" -- "${PATHS[@]}"
echo "checkpoint: committed ${STAMP}"
