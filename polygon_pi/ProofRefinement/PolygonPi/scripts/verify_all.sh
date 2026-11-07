#!/usr/bin/env bash
# One-command replay of the whole artifact (runbook §14.1).
#
# Rebuilds the trusted surface, rebuilds and re-evaluates every candidate in the
# log, re-checks the isolation properties, and prints the axiom closure of the
# best candidate. Read-only with respect to the log (every evaluation uses
# --no-log).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
WS="$ROOT/ProofRefinement/PolygonPi"
cd "$ROOT"

FAIL=0
hdr() { printf '\n== %s ==\n' "$*"; }

hdr "environment"
lean --version
lake --version
echo "mathlib: $(git -C .lake/packages/mathlib rev-parse HEAD)"
echo "project: $(git rev-parse HEAD 2>/dev/null || echo '(not a git repo)')"

hdr "isolation"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
printf 'import Mathlib\n' > "$TMP/mega.lean"
if lake env lean "$TMP/mega.lean" >/dev/null 2>&1; then
  echo "FAIL: bare 'import Mathlib' resolved; the mega-import should be broken."
  FAIL=1
else
  echo "ok: bare 'import Mathlib' does not resolve"
fi
printf 'import Mathlib.Analysis.Real.Pi.Bounds\n' > "$TMP/pib.lean"
if lake env lean "$TMP/pib.lean" >/dev/null 2>&1; then
  echo "FAIL: Mathlib.Analysis.Real.Pi.Bounds resolved; it should be deleted."
  FAIL=1
else
  echo "ok: Mathlib.Analysis.Real.Pi.Bounds does not resolve"
fi
if compgen -G "$WS/Candidates/reference_*" > /dev/null; then
  echo "FAIL: a private reference candidate is present in the workspace."
  FAIL=1
else
  echo "ok: no reference candidates in the workspace"
fi

hdr "trusted surface"
if lake build PolygonCore ProofRefinement.PolygonPi.Proof.Main; then
  echo "ok"
else
  echo "FAIL: trusted surface does not build"
  FAIL=1
fi
if grep -rn "sorry\|admit\b\|native_decide\|^axiom \|opaque \|unsafe " \
     PolygonCore ProofRefinement/PolygonPi/Proof >/dev/null 2>&1; then
  echo "FAIL: forbidden construct in the trusted surface"
  FAIL=1
else
  echo "ok: trusted surface is free of sorry/axiom/native_decide"
fi

hdr "candidates"
for f in "$WS"/Candidates/*.lean; do
  [[ -e "$f" ]] || continue
  NAME="$(basename "$f" .lean)"
  printf -- '-- %s\n' "$NAME"
  if ! "$WS/scripts/polygonpi_eval_candidate.sh" "$NAME" --no-log \
       2>&1 | grep -E '^(11 score|   interval width|status)'; then
    echo "   FAIL: $NAME did not pass"
    FAIL=1
  fi
done

hdr "axiom closure of the best candidate"
BEST=$(python3 - <<'PY'
import json
from fractions import Fraction
from pathlib import Path
p = Path("ProofRefinement/PolygonPi/Refinement_Log/log.jsonl")
if not p.exists():
    print("V0"); raise SystemExit
def frac(s):
    s = str(s)
    return Fraction(*(int(x) for x in s.split("/"))) if "/" in s else Fraction(int(s))
best, name = None, "V0"
for line in p.read_text().splitlines():
    if not line.strip(): continue
    try: r = json.loads(line)
    except json.JSONDecodeError: continue
    if r.get("pass") and "score" in r:
        v = frac(r["score"])
        if best is None or v < best:
            best, name = v, Path(r["candidate"]).stem
print(name)
PY
)
cat > "$TMP/ax.lean" <<EOF
import ProofRefinement.PolygonPi.Candidates.$BEST
#print axioms ProofRefinement.PolygonPi.Candidates.$BEST.polygon_pi_constant_search
EOF
lake env lean "$TMP/ax.lean" 2>&1 | grep -v '^warning: mathlib'

printf '\n'
if [[ $FAIL -ne 0 ]]; then
  echo "VERIFY_ALL: FAIL"
  exit 1
fi
echo "VERIFY_ALL: OK"
