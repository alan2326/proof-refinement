#!/usr/bin/env bash
# Preflight: decide whether the harness is healthy enough to run another sprint.
#
# Exit 0  = OK, run the sprint.
# Exit 1  = HALT. Do not run a sprint; report the reason to the human.
#
# Halt conditions (harness plan §9.3, §10):
#   1. a workspace import-policy violation, including the transitive closure
#   2. the last 3 candidate evaluations all failed
#   3. saturation — the last 5 passing candidates each improved the score by
#      less than a relative 1e-3
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
WS="$ROOT/ProofRefinement/PolygonPi"
cd "$ROOT"

FAIL=0
say() { printf '%s\n' "$*"; }

say "== polygonpi preflight =="

# ── 1. trusted surface intact ────────────────────────────────────────────────
say "-- trusted surface"
if ! git -C "$ROOT" diff --quiet -- PolygonCore ProofRefinement/PolygonPi/Proof \
      ProofRefinement/PolygonPi/Evaluator.py ProofRefinement/PolygonPi/lemma.toml \
      ProofRefinement/PolygonPi/scripts 2>/dev/null; then
  say "   HALT: uncommitted changes to the trusted surface / harness."
  git -C "$ROOT" diff --stat -- PolygonCore ProofRefinement/PolygonPi/Proof \
      ProofRefinement/PolygonPi/Evaluator.py ProofRefinement/PolygonPi/lemma.toml \
      ProofRefinement/PolygonPi/scripts | sed 's/^/     /'
  FAIL=1
else
  say "   ok (no local modifications)"
fi

# ── 2. the answer key must not have leaked into the workspace ────────────────
say "-- answer-key isolation"
if compgen -G "$WS/Candidates/reference_*" > /dev/null; then
  say "   HALT: a reference candidate is present in Candidates/."
  FAIL=1
elif compgen -G "$ROOT/.lake/build/lib/lean/ProofRefinement/PolygonPi/Candidates/reference_*" > /dev/null; then
  say "   HALT: stale reference build artifacts are importable."
  FAIL=1
else
  say "   ok"
fi

# ── 3. import policy, direct and transitive ──────────────────────────────────
say "-- import policy (workspace, transitive)"
MODS=$(cd "$ROOT" && find PolygonCore ProofRefinement -name '*.lean' \
        | sed 's/\.lean$//' | tr '/' '.' | sort)
# shellcheck disable=SC2086
CLOSURE_OUT=$(python3 "$WS/scripts/polygonpi_import_closure.py" $MODS \
      --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi 2>&1)
CLOSURE_RC=$?
if [[ $CLOSURE_RC -ne 0 ]]; then
  say "   HALT: blocked module reachable from the workspace."
  printf '%s\n' "$CLOSURE_OUT" | grep -E 'BLOCK|BLOCKED' | sed 's/^/     /'
  FAIL=1
else
  say "   ok ($(printf '%s\n' "$CLOSURE_OUT" | wc -l) modules checked, all clean)"
fi

# ── 4. log-based health: recent failures and saturation ──────────────────────
say "-- log health"
python3 - "$WS/Refinement_Log/log.jsonl" <<'PY'
import json, sys
from fractions import Fraction
from pathlib import Path

path = Path(sys.argv[1])
if not path.exists():
    print("   no log yet — first sprint, ok")
    raise SystemExit(0)

recs = []
for line in path.read_text().splitlines():
    line = line.strip()
    if line:
        try:
            recs.append(json.loads(line))
        except json.JSONDecodeError:
            pass

if not recs:
    print("   empty log — ok")
    raise SystemExit(0)

# condition 2: last three evaluations all failed
last3 = recs[-3:]
if len(last3) == 3 and not any(r.get("pass") for r in last3):
    print("   HALT: the last 3 candidate evaluations all failed.")
    for r in last3:
        print(f"     {r.get('candidate')}: {r.get('reason')}")
    raise SystemExit(1)

# condition 3: saturation over the last five passing candidates
passing = [r for r in recs if r.get("pass") and "score" in r]
def frac(s):
    s = str(s)
    return Fraction(*(int(p) for p in s.split("/"))) if "/" in s else Fraction(int(s))

scores = [frac(r["score"]) for r in passing]
if len(scores) >= 6:
    tail = scores[-6:]
    rel = []
    for prev, cur in zip(tail, tail[1:]):
        rel.append(0.0 if prev == 0 else float((prev - cur) / prev))
    if all(r < 1e-3 for r in rel):
        print("   HALT: saturation — last 5 passing candidates each improved "
              "the score by < 0.1% relative.")
        print("     relative improvements: " +
              ", ".join(f"{r:.2e}" for r in rel))
        raise SystemExit(1)

best = min(scores) if scores else None
print(f"   {len(recs)} records, {len(passing)} passing, best score {best}")
PY
if [[ $? -ne 0 ]]; then FAIL=1; fi

# ── 5. incumbent still builds and still passes ────────────────────────────────
say "-- incumbent rebuild"
BEST=$(python3 - "$WS/Refinement_Log/log.jsonl" <<'PY'
import json, sys
from fractions import Fraction
from pathlib import Path
p = Path(sys.argv[1])
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
if lake build "ProofRefinement.PolygonPi.Candidates.${BEST}" >/dev/null 2>&1; then
  say "   ok ($BEST builds)"
else
  say "   HALT: incumbent $BEST does not build."
  FAIL=1
fi

say
if [[ $FAIL -ne 0 ]]; then
  say "PREFLIGHT: HALT"
  exit 1
fi
say "PREFLIGHT: OK"
exit 0
