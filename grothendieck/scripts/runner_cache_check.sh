#!/usr/bin/env bash
# scripts/runner_cache_check.sh — short-circuit G8 (--run-all) when
# the certified-arb pipeline's inputs are byte-identical to a previous
# successful certificate.
#
# The runner outputs only depend on these inputs:
#   ProofGraph/nodes/_index.toml
#   ProofGraph/Effective/Lemma54Effective.lean
#   ProofGraph/Effective/Theorem51AtPExplicit.lean
#   ProofGraph/Effective/Theorem51Effective.lean
#
# We compute a sha256 of the four files concatenated and look for a
# matching ProofGraph/runs/<ts>/certificate.json with all
# cross_validation checks passing.
#
# Exit codes:
#   0 + stdout "CACHED <runs-path>" — match found; safe to skip --run-all.
#   1 + stdout "MISS"               — no matching prior cert; run live.

set -euo pipefail

INPUT_FILES=(
    "ProofGraph/nodes/_index.toml"
    "ProofGraph/Effective/Lemma54Effective.lean"
    "ProofGraph/Effective/Theorem51AtPExplicit.lean"
    "ProofGraph/Effective/Theorem51Effective.lean"
)

for f in "${INPUT_FILES[@]}"; do
    if [[ ! -f "$f" ]]; then
        echo "MISS: missing input $f"
        exit 1
    fi
done

current_hash=$(cat "${INPUT_FILES[@]}" | sha256sum | awk '{print $1}')

RUNS_DIR="ProofGraph/runs"
if [[ ! -d "$RUNS_DIR" ]]; then
    echo "MISS: no runs directory"
    exit 1
fi

# Walk runs in reverse chronological order.
for d in $(ls -1 "$RUNS_DIR" 2>/dev/null | sort -r); do
    cert="$RUNS_DIR/$d/certificate.json"
    [[ -f "$cert" ]] || continue
    # Compute hash recorded with that cert (if any), or recompute from
    # the cert's recorded constants. For now we use the simpler check:
    # require an `inputs_sha256` field that matches.
    recorded_hash=$(uv run python -c "
import json, sys
try:
    with open('$cert') as f:
        c = json.load(f)
    print(c.get('inputs_sha256', ''))
except Exception:
    print('')
")
    if [[ "$recorded_hash" == "$current_hash" ]]; then
        # Also confirm the cached run was fully passing.
        passing=$(uv run python -c "
import json
with open('$cert') as f:
    c = json.load(f)
cv = c.get('cross_validation', {})
print('YES' if cv.get('passing') == cv.get('total') and cv.get('total', 0) > 0 else 'NO')
")
        if [[ "$passing" == "YES" ]]; then
            echo "CACHED $RUNS_DIR/$d"
            exit 0
        fi
    fi
done

echo "MISS"
exit 1
