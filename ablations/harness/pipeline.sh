#!/usr/bin/env bash
# Wait for Arm A (which defines the budget), then run Arms B and C in parallel.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "[pipeline] $(date -Is) waiting for Arm A to finish..."
while pgrep -f "run_arm_a.py --run-id korenblum-armA-01" >/dev/null; do sleep 60; done
echo "[pipeline] $(date -Is) Arm A process exited"

if [ ! -f runs/reference_budget.json ]; then
  echo "[pipeline] FATAL: runs/reference_budget.json missing -- Arm A did not"
  echo "[pipeline] complete cleanly. Not launching B/C (budget undefined)."
  exit 1
fi
echo "[pipeline] reference budget:"; cat runs/reference_budget.json

# Both ablation arms run concurrently. Each does its own `lake build`; the box
# has 128 threads so two concurrent Lean builds are comfortable.
echo "[pipeline] $(date -Is) launching Arm B and Arm C in parallel"
nohup python3 -u harness/run_arm_b.py --run-id korenblum-armB-01 --budget-mult 3.0 \
      > runs/armB.console.log 2>&1 &
B=$!
nohup python3 -u harness/run_arm_c.py --run-id korenblum-armC-01 --budget-mult 3.0 \
      > runs/armC.console.log 2>&1 &
C=$!
echo "[pipeline] armB pid=$B  armC pid=$C"

wait $B; echo "[pipeline] $(date -Is) Arm B exited rc=$?"
wait $C; echo "[pipeline] $(date -Is) Arm C exited rc=$?"
echo "[pipeline] $(date -Is) ALL ARMS COMPLETE"
for f in runs/korenblum-arm*-01/summary.json; do
  echo "--- $f"; cat "$f"
done
