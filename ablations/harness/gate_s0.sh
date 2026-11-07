#!/usr/bin/env bash
# Acceptance gate for the reconstructed S0 snapshot.
# See docs/2026-07-27-ablation-design.md sect. 2.3.
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"

WS=${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/workspaces/S0_korenblum}
cd "$WS"
FAIL=0
pass() { printf "  \033[32mPASS\033[0m  %s\n" "$1"; }
fail() { printf "  \033[31mFAIL\033[0m  %s\n" "$1"; FAIL=1; }

echo "=== GATE 1: V64 builds ==="
if lake build ProofRefinement.Korenblum.Candidates.V64 2>&1 | tail -3 \
     | grep -q "Build completed successfully"; then
  pass "lake build ProofRefinement.Korenblum.Candidates.V64"
else
  fail "lake build V64"
fi

echo "=== GATE 2: evaluator accepts V64 at the anchor parent score ==="
OUT=$(env UV_CACHE_DIR="$WS/.uv-cache" uv run ProofRefinement/Korenblum/Evaluator.py \
        --file ProofRefinement/Korenblum/Candidates/V64.lean --no-log 2>&1)
echo "$OUT" | grep -q "^status: PASS"                  && pass "status: PASS"        || fail "evaluator status"
echo "$OUT" | grep -q "score (maximize): 17823/50000"  && pass "score 17823/50000"   || fail "score mismatch"
echo "$OUT" | grep -q "oracle audit:  PASS"            && pass "oracle audit PASS"   || fail "oracle audit"
echo "$OUT" | grep -q "sorryAx"                        && fail "sorryAx present"     || pass "no sorryAx"

echo "=== GATE 3: no anchor-answer leakage outside .lake ==="
LEAK=0
for t in 356562 356564 356565 seven_window sevenWindow SevenWindow \
         EightWindow ElevenWindow Branch1Integrability mixedKernel \
         v66CValue v67CValue v68CValue; do
  n=$(grep -rl "$t" --include='*.md' --include='*.lean' --include='*.py' \
        --include='*.toml' --include='*.txt' . 2>/dev/null | grep -v '^./.lake' | wc -l)
  [ "$n" -eq 0 ] || { fail "leak: '$t' in $n file(s)"; LEAK=1; }
done
[ "$LEAK" -eq 0 ] && pass "no answer-term leakage (13 terms checked)"
# Sprint numbers >083 must not appear as authored-at labels. Forward-looking
# mentions ("deferred to sprint 084+") ARE legitimate at S0 -- sprint 083 wrote
# them -- and are confined to these three files.
ALLOWED_FWD='Sprint_Contracts/sprint_083|Experience.md|Bulletin.md'
n=$(grep -rlE "[Ss]print[ _]0(8[4-9]|9[0-9]|10[0-2])" --include='*.md' --include='*.lean' \
      --include='*.py' --include='*.toml' . 2>/dev/null \
      | grep -v '^./.lake' | grep -vE "$ALLOWED_FWD" | wc -l)
[ "$n" -eq 0 ] && pass "no post-anchor sprint labels outside forward-looking notes" \
                || fail "post-anchor sprint labels in $n file(s)"
# ...and the forward-looking ones must not name a c beyond the S0 roadmap value.
n=$(grep -rhoE "35(6[5-9][0-9]{3}|65[6-9][0-9]{2})" --include='*.md' . 2>/dev/null \
      | grep -v '^./.lake' | sort -u | grep -v '^356401$' | wc -l)
[ "$n" -eq 0 ] && pass "no c-value beyond the S0 roadmap target (356401)" \
                || fail "$n c-value(s) beyond roadmap present"

echo "=== GATE 4: whole workspace builds ==="
if lake build 2>&1 | tail -3 | grep -q "Build completed successfully"; then
  pass "lake build (all targets)"
else
  fail "lake build (all targets)"
fi

echo "=== GATE 5: workspace state is sprint-083-consistent ==="
LAST=$(python3 -c "
import json,sys
rows=[json.loads(l) for l in open('ProofRefinement/Korenblum/Refinement_Log/log.jsonl')]
r=rows[-1]; print(r['candidate'], r['score'], r['timestamp_utc'][:19])")
[ "$LAST" = "Candidates/V64.lean 17823/50000 2026-05-05T03:51:33" ] \
  && pass "log.jsonl ends at V64 (sprint 083)" || fail "log tail: $LAST"
LASTSPRINT=$(ls ProofRefinement/Korenblum/Sprint_Contracts/ | grep -oE '^sprint_[0-9]{3}' | sort | tail -1)
[ "$LASTSPRINT" = "sprint_083" ] && pass "last contract is sprint_083" || fail "last contract: $LASTSPRINT"
[ -d ProofRefinement/Korenblum/Candidates/V65 ] && fail "V65 dir present" || pass "no V65+ candidates"
ls ProofRefinement/Korenblum/Candidates/V6[5-8].lean >/dev/null 2>&1 \
  && fail "V65-V68 .lean present" || pass "no V65-V68 .lean"

echo
[ "$FAIL" -eq 0 ] && echo "GATE RESULT: ALL PASS" || echo "GATE RESULT: FAILURES PRESENT"
exit $FAIL
