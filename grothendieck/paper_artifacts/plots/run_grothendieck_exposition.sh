#!/usr/bin/env bash
# Run the Grothendieck exposition figure generator via uv.
#
# Output always lands in paper_artifacts/plots/grothendieck_figures/ unless
# overridden by passing --outdir explicitly.
#
# Usage:
#   ./run_grothendieck_exposition.sh                       # writes to plots/grothendieck_figures/
#   ./run_grothendieck_exposition.sh --solve               # recompute 2D vector relaxation
#   ./run_grothendieck_exposition.sh --outdir /tmp/figs    # override output dir
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTDIR_DEFAULT="$SCRIPT_DIR/grothendieck_figures"

uv run \
  --with numpy \
  --with matplotlib \
  --with scipy \
  python "$SCRIPT_DIR/grothendieck_exposition.py" --outdir "$OUTDIR_DEFAULT" "$@"
