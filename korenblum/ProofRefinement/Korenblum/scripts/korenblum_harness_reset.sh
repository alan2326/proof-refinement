#!/usr/bin/env bash
# Reset the Korenblum harness to a V0-centered state.

set -euo pipefail

DRY_RUN=0
if [[ "${1:-}" == "--dry-run" ]]; then
    DRY_RUN=1
fi

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

run() {
    if [[ $DRY_RUN -eq 1 ]]; then
        echo "DRY-RUN: $*"
    else
        eval "$@"
    fi
}

echo "==> korenblum_harness_reset starting"

shopt -s nullglob

for f in Candidates/V*.lean; do
    [[ "$(basename "$f")" == "V0.lean" ]] && continue
    run "rm -f \"$f\""
    echo "  removed candidate: $(basename "$f")"
done

for f in Sprint_Contracts/sprint_*.md; do
    run "rm -f \"$f\""
    echo "  removed sprint contract: $(basename "$f")"
done

for f in Refinement_Log/verdict_*.md; do
    run "rm -f \"$f\""
    echo "  removed verdict: $(basename "$f")"
done

if [[ $DRY_RUN -eq 0 && -f "Refinement_Log/log.jsonl" ]]; then
    python3 - "Refinement_Log/log.jsonl" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
baseline = None
for line in path.read_text().splitlines():
    line = line.strip()
    if not line:
        continue
    try:
        record = json.loads(line)
    except Exception:
        continue
    if record.get("candidate") == "Candidates/V0.lean" and record.get("pass") is True:
        baseline = line

if baseline is None:
    path.write_text("")
else:
    path.write_text(baseline + "\n")
PY
    echo "  log reset to latest successful V0 baseline"
fi

if [[ $DRY_RUN -eq 0 ]]; then
    cat > "Bulletin.md" <<'EOF'
# Bulletin — Korenblum refinement loop

Volatile signaling between sprints. The historical record is
`Refinement_Log/log.jsonl`.

Format:

```text
sprint_<NNN> queued: <title> [direction: <axis>]
sprint_<NNN> PASS: <title>
sprint_<NNN> FAIL: <title> [gate: <id>]
note: <human note>
```

## Current priority

> Lift the paper-faithful seed `c = 0.3554` while keeping the final theorem
> statement unchanged.

## Recent events
EOF
    echo "  Bulletin.md reset"

    cat > "Experience.md" <<'EOF'
# Experience — Korenblum refinement notebook

Append-only narrative notes from generators and planners.

Conventions:

- `### YYYY-MM-DD sprint_<NNN>`
- one short paragraph per entry
- describe changes and observations, not pass/fail

## Entries
EOF
    echo "  Experience.md reset"
fi

echo "==> korenblum_harness_reset complete"
