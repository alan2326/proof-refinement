#!/usr/bin/env bash
# Append a sprint boundary marker for results/telemetry.py.
# Usage: mark.sh <sprint> <sprint_start|sprint_end> [outcome] [note]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPRINT="${1:?sprint id}"; EVENT="${2:?event}"; OUTCOME="${3:-}"; NOTE="${4:-}"
python3 - "$ROOT/results/sprint_markers.jsonl" "$SPRINT" "$EVENT" "$OUTCOME" "$NOTE" <<'PY'
import json, sys
from datetime import datetime, timezone
path, sprint, event, outcome, note = sys.argv[1:6]
rec = {"sprint": sprint, "event": event,
       "ts": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")}
if outcome: rec["outcome"] = outcome
if note: rec["note"] = note
with open(path, "a") as f:
    f.write(json.dumps(rec, sort_keys=True) + "\n")
print(f"{event} {sprint} @ {rec['ts']}")
PY
