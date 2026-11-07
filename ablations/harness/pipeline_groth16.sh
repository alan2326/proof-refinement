#!/usr/bin/env bash
# Sprint-016 arms, concurrent matched-window protocol (user decision
# 2026-07-29): launch A, B, C together; when A finishes, B and C stop at
# wall > T_ref = max(T_armA, 2360 s). Time gates; tokens recorded.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

rm -f runs/groth16_deadline.json
date +%s > runs/groth16_start_epoch

echo "[pipeline16] $(date -Is) launching Arm A, B'', C'' concurrently"
nohup python3 -u harness/run_arm_a_groth16.py \
      > runs/groth16_armA.console.log 2>&1 &
A=$!
nohup python3 -u harness/run_arm_b_groth16.py \
      > runs/groth16_armB.console.log 2>&1 &
B=$!
nohup python3 -u harness/run_arm_c_groth16.py \
      > runs/groth16_armC.console.log 2>&1 &
C=$!
echo "[pipeline16] pids A=$A B=$B C=$C"

wait "$A"; rcA=$?
echo "[pipeline16] $(date -Is) Arm A exited rc=$rcA"

if [ ! -f runs/reference_budget_groth16.json ]; then
  echo "[pipeline16] FATAL: Arm A wrote no reference budget; killing B/C."
  kill "$B" "$C" 2>/dev/null
  exit 1
fi

python3 harness/fix_reference_budget_groth16.py || {
  echo "[pipeline16] FATAL: budget correction failed; killing B/C."
  kill "$B" "$C" 2>/dev/null
  exit 1
}
TREF=$(python3 -c "import json; print(int(float(json.load(open('runs/reference_budget_groth16.json'))['T_ref_s'])))")
python3 -c "import json,time; json.dump({'t_ref_s': $TREF, 'written_at': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}, open('runs/groth16_deadline.json','w'))"
echo "[pipeline16] $(date -Is) deadline written: T_ref=${TREF}s (matched window)"

START=$(cat runs/groth16_start_epoch)
DEADLINE=$((START + TREF))
GRACE=180
NOW=$(date +%s)
SLEEP=$((DEADLINE + GRACE - NOW))
if [ "$SLEEP" -gt 0 ]; then
  echo "[pipeline16] window still open; sleeping ${SLEEP}s to deadline+grace"
  sleep "$SLEEP"
fi

for pid in "$B" "$C"; do
  if kill -0 "$pid" 2>/dev/null; then
    echo "[pipeline16] $(date -Is) SIGTERM runner $pid (window closed)"
    kill "$pid" 2>/dev/null
  fi
done
sleep 90
for pid in "$B" "$C"; do
  if kill -0 "$pid" 2>/dev/null; then
    echo "[pipeline16] $(date -Is) SIGKILL runner $pid"
    kill -9 "$pid" 2>/dev/null
  fi
done
wait "$B" 2>/dev/null; echo "[pipeline16] Arm B'' exited rc=$?"
wait "$C" 2>/dev/null; echo "[pipeline16] Arm C'' exited rc=$?"

# Orphaned headless `claude -p` children (PPID=1 only -- never touches
# interactive sessions).
python3 -c "import sys; sys.path.insert(0,'harness'); from groth_common import reap_orphaned_claude as r; print('[pipeline16] reaped', r(), 'orphaned claude proc(s)')"

# Post-hoc summaries for anything SIGKILLed before self-finalizing.
python3 harness/finalize_groth16.py grothendieck016-armB-01 grothendieck016-armC-01

echo "[pipeline16] $(date -Is) ALL ARMS COMPLETE"
for f in runs/grothendieck016-arm*-01/summary.json; do
  echo "--- $f"; cat "$f"
done
