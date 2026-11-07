#!/usr/bin/env bash
# Periodic checkpoint commits, for use alongside a long autonomous run.
# Usage: polygonpi_checkpoint_loop.sh [interval-seconds]   (default 1800)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
INTERVAL="${1:-1800}"

echo "checkpointing every ${INTERVAL}s; Ctrl-C to stop"
while true; do
  sleep "$INTERVAL"
  "$ROOT/ProofRefinement/PolygonPi/scripts/polygonpi_checkpoint_once.sh" || true
done
