---
name: run-next-polygonpi-sprint
description: Run one complete Polygon-π refinement sprint - preflight, planner, generator, evaluator, bulletin update. Use when asked to run the next sprint, continue the polygon-pi refinement loop, or advance the pi bound frontier.
---

# Run the next Polygon-π refinement sprint

One sprint, five steps, in order. Do not skip a step and do not reorder them.

## 1. Preflight

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_harness_preflight.sh
```

If this exits non-zero, **stop**. Do not run a sprint. Report the halt reason to
the human verbatim and end your turn. The halt conditions are there to stop a
stuck or saturated loop from producing work that looks healthy, so treating a
halt as something to work around defeats the purpose.

## 2. Planner

Dispatch the `polygonpi-refinement-planner` subagent. It writes exactly one new
sprint contract under `ProofRefinement/PolygonPi/Sprint_Contracts/`.

Expect `STATUS=CONTRACT_READY <path>`. If it returns anything else, stop and
report.

## 3. Generator

Dispatch the `polygonpi-refinement-generator` subagent with the contract path
from step 2.

Possible outcomes:

- `STATUS=READY_FOR_EVALUATION` → continue to step 4.
- `STATUS=BLOCKED` → skip step 4. The sprint still counts: the obstruction note
  in `Experience.md` is the artefact. Go to step 5.
- `STATUS=BLOCKED_NEEDS_HUMAN` → skip step 4, go to step 5, and surface the
  request prominently in your summary.

## 4. Evaluator

Only if the generator returned `READY_FOR_EVALUATION`. Dispatch the
`polygonpi-refinement-evaluator` subagent with the same contract path.

Expect `STATUS=VERDICT_PASS` or `STATUS=VERDICT_FAIL`. Either is a valid sprint
outcome. Do not re-run the generator to try to turn a FAIL into a PASS — that is
next sprint's decision, made by the planner with the verdict in front of it.

## 5. Bulletin line

Append one line to the sprint log table at the bottom of
`ProofRefinement/PolygonPi/Bulletin.md`:

```
| sprint_<NNN> | <slug> | <rung type> | <side> | <outcome> | score <s> | <one clause on what changed> |
```

If the sprint improved the frontier, also update the **Frontier** table at the
top of `Bulletin.md` — incumbent candidate, `kappa`, `lambda`, score, interval
width, and the sprint count.

## 6. Report

Return one paragraph to the human: what the sprint attempted, what happened, the
new score and interval width if it moved, and the single most useful thing the
next sprint could do. Be concrete and do not pad it.

## Autonomous mode

The loop is **self-paced**: `/loop /run-next-polygonpi-sprint` with no interval,
so the next sprint starts as soon as this one returns rather than on a wall clock.
This task's sprints are short — a single-file candidate and a compile measured in
seconds — so a fixed timer would mostly idle.

Because there is no timer, this skill must return promptly and the preflight halt
conditions do all the throttling. A stuck loop is supposed to stop at step 1
rather than be rate-limited into looking healthy.
