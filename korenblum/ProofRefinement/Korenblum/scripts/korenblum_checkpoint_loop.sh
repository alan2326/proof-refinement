#!/usr/bin/env bash
# Run periodic scoped checkpoint commits for the Korenblum harness.
#
# Usage:
#   bash scripts/korenblum_checkpoint_loop.sh
#   bash scripts/korenblum_checkpoint_loop.sh 300
#   bash scripts/korenblum_checkpoint_loop.sh 300 ProofRefinement/Korenblum

set -euo pipefail

INTERVAL_SECONDS="${1:-300}"
shift || true

if ! [[ "$INTERVAL_SECONDS" =~ ^[0-9]+$ ]] || [[ "$INTERVAL_SECONDS" -le 0 ]]; then
    echo "usage: bash scripts/korenblum_checkpoint_loop.sh [interval-seconds] [path ...]"
    exit 2
fi

if [[ $# -gt 0 ]]; then
    PATHS=("$@")
else
    PATHS=("ProofRefinement/Korenblum")
fi

echo "checkpoint loop: interval=${INTERVAL_SECONDS}s scope=${PATHS[*]}"

while true; do
    bash "$(dirname "$0")/korenblum_checkpoint_once.sh" "${PATHS[@]}" || true
    sleep "$INTERVAL_SECONDS"
done
