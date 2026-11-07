#!/usr/bin/env bash
# Launch the Korenblum × ShinkaEvolve ablation, fresh.
#
# Why a script: when launched inline, the shell wrapper's PID got
# captured into evo.pid instead of the python process PID, and the
# runner auto-resumed from a stale `evolution_db.sqlite`. This script
# does both correctly: clears stale state, launches python, captures
# the python PID after a short settle, prints status.
#
# Usage:
#     bash launch.sh              # fresh run
#     bash launch.sh --resume     # keep existing results dir / db (resume)

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOG="$HERE/evo.log"
PIDFILE="$HERE/evo.pid"
RESULTS="$HERE/results"
DB="$HERE/evolution_db.sqlite"
VENV="${SHINKA_VENV:?set SHINKA_VENV to a virtualenv with ShinkaEvolve installed}"

if [[ "${1-}" != "--resume" ]]; then
    if [[ -d "$RESULTS" || -f "$DB" || -f "$LOG" ]]; then
        echo "Clearing prior run state: $RESULTS, $DB, $LOG" >&2
        rm -rf "$RESULTS" "$DB" "$LOG"
    fi
fi

if [[ -f "$PIDFILE" ]] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    echo "A run is already in progress (PID $(cat "$PIDFILE")). Refusing to start another." >&2
    exit 1
fi

if [[ -z "${ANTHROPIC_API_KEY:-}" ]]; then
    echo "ANTHROPIC_API_KEY is not set. Aborting." >&2
    exit 1
fi

# shellcheck source=/dev/null
source "$VENV/bin/activate"

cd "$HERE"
nohup python -u run_evo.py > "$LOG" 2>&1 &
disown
PID=$!

# Brief settle so the python process is fully alive.
sleep 2

if ! kill -0 "$PID" 2>/dev/null; then
    echo "Python process died immediately. See $LOG." >&2
    tail -50 "$LOG" >&2 || true
    exit 1
fi

echo "$PID" > "$PIDFILE"
echo "Launched run_evo.py at PID $PID."
echo "Tail the log with:    tail -f $LOG"
echo "Stop the run with:    kill \$(cat $PIDFILE)"
