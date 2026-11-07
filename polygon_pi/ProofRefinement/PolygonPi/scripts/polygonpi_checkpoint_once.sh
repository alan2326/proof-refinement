#!/usr/bin/env bash
# Commit the current state of the workspace as a checkpoint.
# Usage: polygonpi_checkpoint_once.sh ["message"]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

MSG="${1:-}"
if [[ -z "$MSG" ]]; then
  BEST=$(python3 - <<'PY'
import json
from fractions import Fraction
from pathlib import Path
p = Path("ProofRefinement/PolygonPi/Refinement_Log/log.jsonl")
if not p.exists():
    print("no-log"); raise SystemExit
def frac(s):
    s = str(s)
    return Fraction(*(int(x) for x in s.split("/"))) if "/" in s else Fraction(int(s))
best, name = None, "none"
for line in p.read_text().splitlines():
    if not line.strip(): continue
    try: r = json.loads(line)
    except json.JSONDecodeError: continue
    if r.get("pass") and "score" in r:
        v = frac(r["score"])
        if best is None or v < best:
            best, name = v, Path(r["candidate"]).stem
print(f"{name} score={best}")
PY
)
  MSG="checkpoint: $BEST"
fi

if git diff --quiet && git diff --cached --quiet && [[ -z "$(git status --porcelain)" ]]; then
  echo "nothing to checkpoint"
  exit 0
fi

git add -A
git commit -q -m "$MSG"
git log --oneline -1
