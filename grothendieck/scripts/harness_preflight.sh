#!/usr/bin/env bash
# scripts/harness_preflight.sh — pre-flight gate for /run-next-sprint.
#
# The harness is candidates-only: the Generator never edits production,
# so production-regression checks happen out-of-loop. The pre-flight's
# only job is to halt when the Planner is stuck (3+ consecutive FAILs
# on the same goal).
#
# Exit codes:
#   0 — OK to proceed; spawn the Planner.
#   1 — Halt: same goal failed 3+ consecutive times.
#   2 — Halt: log file is malformed or unreadable.
#
# Reads:
#   ProofRefinement/Lemma54/Refinement_Log/log.jsonl
#
# Writes nothing. Prints a single halt-reason line to stdout if it
# exits non-zero.

set -euo pipefail

LOG="ProofRefinement/Lemma54/Refinement_Log/log.jsonl"

if [[ ! -f "$LOG" ]]; then
    echo "preflight: log empty (first run); proceed"
    exit 0
fi

# Same-goal-3-fails check: last 3 entries have the same sprint title and all FAIL.
recent=$(tail -n 3 "$LOG" 2>/dev/null || echo "")
n_lines=$(echo "$recent" | grep -c '^{' || echo 0)
if [[ "$n_lines" -eq 3 ]]; then
    n_fails=$(echo "$recent" | uv run python -c "
import json, sys
titles = []
fails = 0
for line in sys.stdin:
    line = line.strip()
    if not line: continue
    try:
        d = json.loads(line)
    except Exception:
        sys.exit(2)
    titles.append(d.get('title', ''))
    if d.get('outcome') == 'FAIL':
        fails += 1
all_same = (len(set(titles)) == 1 and titles[0])
print(fails if all_same else 0)
")
    if [[ "$n_fails" -ge 3 ]]; then
        echo "preflight HALT: last 3 sprints failed on the same title; needs human review"
        exit 1
    fi
fi

echo "preflight: OK"
exit 0
