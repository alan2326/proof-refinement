#!/usr/bin/env bash
# Acceptance gate for S0_grothendieck016 (hard, blocking) -- sect. 13.3.
# G1  lake build of the parent candidate V11 succeeds
# G2  Evaluator.py on V11: terminal PASS, exit 0, score Cr_val = 1
#     (cold run prewarms Numerical_Library/.cache at the era's resolutions)
# G3  no post-anchor artifacts: no sprint_016+ contracts/verdicts, no V12+,
#     no u_zz.py / compute_u_zz_bound / h_u_zz_oracle / u_zz_bound_val /
#     Cr_phi_uzz_direct anywhere, no docs/HARNESS_OPERATOR_TIPS.md, the
#     sprint-016 answer values (1/32, u_zz sup 1.55 / 1.394, the 224x/289x/
#     321x tightening figures) absent from Lemma54
# G4  memory tails: Bulletin/Experience end at sprint_015; log.jsonl last
#     accepted row is V11
# G5  workspace git history is exactly 1 commit
set -uo pipefail

WS=${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/workspaces/S0_grothendieck016}
L54=$WS/ProofRefinement/Lemma54
fails=0
say() { printf '%s\n' "$*"; }
gate() { # gate <name> <0-ok-flag> <detail>
  if [ "$2" -eq 0 ]; then say "  PASS  $1  $3"; else say "  FAIL  $1  $3"; fails=$((fails+1)); fi
}

say "[gate_s016] G1: lake build V11"
( cd "$WS" && lake build ProofRefinement.Lemma54.Candidates.V11 ) >/tmp/gate16_g1.log 2>&1
gate G1 $? "lake build ProofRefinement.Lemma54.Candidates.V11 (log /tmp/gate16_g1.log)"

say "[gate_s016] G2: Evaluator.py V11 (cold oracles; prewarms .cache)"
( cd "$WS" && .venv/bin/python ProofRefinement/Lemma54/Evaluator.py \
    --file ProofRefinement/Lemma54/Candidates/V11.lean --no-log ) >/tmp/gate16_g2.log 2>&1
rc=$?
tail -1 /tmp/gate16_g2.log | grep -qx 'PASS'; okpass=$?
grep -qE 'Cr_val: 1(/1)? ' /tmp/gate16_g2.log; okscore=$?
gate G2 $((rc != 0 || okpass != 0 || okscore != 0)) \
  "exit=$rc terminal-PASS=$([ $okpass -eq 0 ] && echo yes || echo no) score-1=$([ $okscore -eq 0 ] && echo yes || echo no) (log /tmp/gate16_g2.log)"

say "[gate_s016] G3: post-anchor artifacts absent"
bad=0; detail=""
for f in "$L54"/Sprint_Contracts/sprint_01[6-9].md "$L54"/Sprint_Contracts/sprint_0[2-9]*.md \
         "$L54"/Refinement_Log/verdict_01[6-9].md "$L54"/Refinement_Log/verdict_0[2-9]*.md \
         "$L54"/Candidates/V1[2-9].lean "$L54"/Candidates/V[2-9][0-9].lean \
         "$L54"/Numerical_Library/u_zz.py "$WS"/docs/HARNESS_OPERATOR_TIPS.md; do
  [ -e "$f" ] && { bad=1; detail="$detail $f"; }
done
# the sprint-016 oracle/theorem names must not exist anywhere in Lemma54
g=$(grep -rl "compute_u_zz_bound\|h_u_zz_oracle\|u_zz_bound_val\|Cr_phi_uzz_direct\|uzz_direct" "$L54" 2>/dev/null | head -3)
[ -n "$g" ] && { bad=1; detail="$detail names:$g"; }
# the sprint-016 answer values must be absent (Cr=1/32 and the quotient-sup
# figures; "1/32" is specific enough to grep bare across the Lemma54 tree)
g=$(grep -rl "1/32\|1\.3939\|321\.86\|224x\|289x" "$L54" 2>/dev/null | head -3)
[ -n "$g" ] && { bad=1; detail="$detail answer:$g"; }
gate G3 $bad "${detail:-clean}"

say "[gate_s016] G4: memory tails at sprint_015"
okb=1; oke=1
grep -q "sprint_015 PASS" "$L54/Bulletin.md" && ! grep -q "sprint_016" "$L54/Bulletin.md" && okb=0
grep -q "sprint 015\|sprint_015" "$L54/Experience.md" && ! grep -q "sprint_016\|sprint 016" "$L54/Experience.md" && oke=0
nlog=$(wc -l < "$L54/Refinement_Log/log.jsonl")
lastok=$(python3 - "$L54/Refinement_Log/log.jsonl" <<'EOF'
import json, sys
last = ""
for line in open(sys.argv[1]):
    try:
        r = json.loads(line)
    except Exception:
        continue
    if r.get("status") == "ok":
        last = r.get("candidate", "")
print(last.rsplit("/", 1)[-1])
EOF
)
gate G4 $([ "$okb" -eq 0 ] && [ "$oke" -eq 0 ] && [ "$nlog" -ge 8 ] && [ "$lastok" = "V11.lean" ]; echo $?) \
  "bulletin-tail-ok=$okb experience-tail-ok=$oke log_rows=$nlog last_accepted=$lastok"

say "[gate_s016] G5: git history = 1 commit"
n=$(git -C "$WS" log --oneline 2>/dev/null | wc -l)
gate G5 $([ "$n" -eq 1 ]; echo $?) "commits=$n"

if [ "$fails" -eq 0 ]; then say "[gate_s016] ALL PASS"; else say "[gate_s016] $fails FAILURE(S)"; exit 1; fi
