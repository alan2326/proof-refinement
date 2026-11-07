#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "usage: bash scripts/korenblum_eval_candidate.sh <candidate-path> [extra evaluator args ...]"
    exit 2
fi

WORKSPACE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(git -C "$WORKSPACE_DIR" rev-parse --show-toplevel)"
CANDIDATE="$1"
shift

case "$CANDIDATE" in
    /*) ;;
    *) CANDIDATE="$WORKSPACE_DIR/$CANDIDATE" ;;
esac

cd "$REPO_ROOT"
env UV_CACHE_DIR="$REPO_ROOT/.uv-cache" \
  uv run "$WORKSPACE_DIR/Evaluator.py" --file "$CANDIDATE" "$@"
