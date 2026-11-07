# Grothendieck ablation summary (for rebuttal use)

Source data: `runs/grothendieck016-arm{A,B,C}-0*`, `analysis/classification_groth16.json`,
`runs/reference_budget_groth16.json`. Design: `docs/2026-07-27-ablation-design.md` §13.

## Problem

Reviewers Ss1D and KcCs noted that our ablations were run only on the Korenblum
case, and that the baseline failures were reported as DNF outcomes without
budget detail. Ss1D (Q2) asked whether the baselines used the same foundation
model, computational budget, literature resources, access to Lean/Arb tooling,
and stopping criteria, and asked for the specific failure mode of each baseline.
Ss1D (W3) and Uspn asked for hardware, wall-clock time, model calls, token
counts, and failed attempts. KcCs (Q3) asked which results were agent-only
versus human-in-the-loop.

This document summarizes a structural ablation on the Grothendieck case that
addresses these points. It isolates the two components of the framework:
the agentic system (planner/generator/evaluator loop) and the partial Lean
formalization (the blueprint).

## Setup

Anchor: the sprint-016 state of the Lemma 5.4 workspace (Braverman et al.
2011), with parent candidate V11 certifying the inverse-expansion constant at
C_r = 1. All arms start from a byte-identical frozen snapshot of this
workspace and use the same foundation model (claude-opus-5 for all generative
work; A and C use a claude-sonnet-5 subagent for evaluation plumbing). No
human touched any arm while it ran; the only human actions were starting the
runs, restarting them after a provider usage limit interrupted all arms
mid-run (stalled time is excluded from every clock below), and setting budgets.

**Arms.**

- **A (full framework).** The unmodified system: agentic sprint loop over the
  Lean blueprint. Defines the reference budget.
- **B (agentic system removed).** The same workspace, model, literature
  (including the Braverman paper text and all pre-anchor analysis scripts),
  and verification backend, but the model is a bare LLM loop: no tools, no
  file access, no subagents. It emits whole files as text; a harness writes
  them, runs `lake build` and the unmodified evaluator, and returns verbatim
  output. We confirmed the ablation held by scanning all session transcripts:
  zero tool invocations.
- **C (formalization removed).** The full agentic system, but pointed at the
  outermost statement (K_G itself) with only an exact-real seed axiom for
  Krivine's bound, instead of the partially formalized proof chain. Same
  driver, same tools.

**Success criteria, fixed before the runs.** For A and B: an
evaluator-accepted candidate with C_r ≤ 1/6400. This bar was derived from a
pre-run measurement of the "no-Lean envelope" (the best value reachable by
tightening declared numerical values on the frozen Lean surface, without any
new mathematics: 3.87e-4); the bar is half that, so declared-value shaving
cannot cross it. Accepted candidates above the bar count as progress, not
success. For C, whose statement level has no such envelope: success requires
an accepted rational value strictly below Krivine's constant, decided against
a 50-digit certified interval.

**Budgets.** Arm A ran to its stopping rule and defined the reference budget:
8,652 s wall clock and 544,294 output tokens. B and C ran concurrently with A
and were then extended until each met or exceeded A on *both* axes — wall
clock and output tokens. Neither ablation was stopped short of the full
framework's consumption on either measure.

## Results

| Arm | Best accepted | Improvement over start | Success (bar) | Wall clock | Output tokens | Cost |
|---|---|---|---|---|---|---|
| A (full) | C_r = 1/400000 | 400,000× | **yes** (62× below bar) | 8,652 s | 544,294 | $35.59 |
| B (no agent) | C_r = 1/250 | 250× | no (26× above bar) | 11,379 s | 567,988 | $54.70 |
| C (no Lean) | K = 1.782213978231 | removed 99.8% of seed slack | no (never below Krivine) | 10,093 s | 738,266 | $44.06 |

A reached the bar in 4 sprints. Its decisive moves were (1) replacing the
product-of-independent-sups bound on the second derivative with a single
fused oracle over the exact closed form, and (2) changing the sup domain from
the certified rectangle to a lens in arcsin coordinates, which cuts the
dominant corner contributions. Both moves required new proved Lean and new
certified numerics, produced and verified inside the loop.

B, given equal time and tokens, produced four accepted candidates
(1 → 9/100 → 3/250 → 1113/100000 → 1/250) but never approached the bar. At
the time-matched checkpoint its best was 1113/100000; the final 1/250 came
from the token-parity extension.

C produced one accepted candidate: a re-certification of the Krivine
frontier to within 4e-11, shaving 99.8% of the slack its seed allowed but
never going below the published bound — which is unreachable from its seed by
construction. This is the predicted failure mode when the formalized chain is
removed: the system can only grind declared values toward a frontier it has
no structure to cross.

## Failure modes (Ss1D Q2)

The three arms fail in three different ways, and none of the failures is
"could not produce certified output":

- **B's failure is not conceptual.** In its extension, B independently
  invented the same fused-oracle idea as A — same exact identity, same
  cancellation argument — with no trace of the idea anywhere in its context
  (we grepped its full prompt corpus). It first wrote the idea as a new Lean
  library module, which failed to compile on a Mathlib style linter; unable
  to iterate cheaply, it rebuilt the argument inside the candidate file two
  calls later: 287 lines of new proof, textually 11% similar to the nearest
  frozen theorem, which compiled and passed the unmodified evaluator. What B
  never found was the domain-change move, and each of its build failures cost
  it a full 15–45-minute round trip. The remaining 1600× gap to A is the
  price of having no ability to run, test, and repair.
- **C's failure is structural.** With the proof chain gone, no amount of
  search can certify anything below the seed's frontier; C's agentic system
  worked correctly and produced exactly what the setup permits: slack
  removal.
- **A had no failure**; it crossed the pre-registered bar inside its budget,
  with fewer output tokens and lower cost than either ablation.

## Discussion

The two components ablate cleanly. Removing the formalization (C) caps what
can be achieved at all: certified progress reduces to numerics against a
frontier the system cannot cross. Removing the agency (B) leaves the ceiling
in place but removes the ability to reach it: B matched A's key mathematical
insight but could not land and then build on it, because every compile-fix
cycle costs a full model call and there is no incremental tooling. The
framework's contribution in this experiment is therefore not "the model has
ideas the bare model lacks" — it demonstrably does not — but that the loop
converts ideas into verified artifacts fast enough to chain them: A landed
the fused bound and found the lens domain in its next sprint.

The bar construction also matters for interpreting baselines: without it, B's
250× improvement would look like near-success. Measuring the no-Lean envelope
first showed that large multiplicative improvements are available by
declared-value tightening alone, which is why success is defined as crossing
a bar that such tightening cannot reach.

## Cost and reproducibility detail (Ss1D W3/Q1, Uspn)

Hardware: 2× Intel Xeon Platinum 8352Y (64 cores / 128 threads), 503 GB RAM;
no GPU used. Lean 4.28.0, pinned Mathlib; evaluation by the workspace's
unmodified evaluator (Arb/mpmath interval numerics). Model calls: A 52 turns
across 4 sprints; B 7 completed calls (plus one 45-minute timeout); C 80
turns across 6 sprints. Failed attempts: A 5 (rejected or aborted sprint
steps), B 2 build failures (both on the same linter issue), C 0 failed
evaluator runs. Every number above is from a single run per arm (n=1);
we report event logs, transcripts, and per-call token accounting in the run
archives rather than claiming variance estimates.

Integrity audits run post-hoc on all arms: byte-comparison of the frozen
Lean surface, oracle-parameter diff scan, scan for conclusion-shaped axioms,
and transcript scan for leakage of study files. No violations. Two additive
changes were flagged and inspected: A appended new proved theorems to
existing library files (509 added lines, zero deletions, zero new axioms),
and both A and B added the import lines required to register their new
oracle modules.

## Caveats

- B runs inside the agent CLI with tools disabled rather than as a raw API
  call, so the agentic system prompt is present. This biases in the
  ablation's favor (documented in the design, §10d).
- The token totals count recorded output tokens; B's one timed-out call
  generated tokens that were never returned and are not counted for it.
- All runs were interrupted once by a provider usage limit and resumed;
  stall time is excluded from all clocks, and the interruption is recorded
  in each run's manifest.
- Independent numerical cross-checks of the two new oracle modules B
  introduced (its tightened M_pp bound and its fused bound) beyond the
  evaluator's own re-verification are planned but not yet run; A's result
  does not depend on them.
