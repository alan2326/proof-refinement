# Ablating the partial formalization and the agentic system

**Date:** 2026-07-30. Covers runs `grothendieck016-*`. Full design and
execution record: `2026-07-27-ablation-design.md` §13.

## Problem

Our framework improves certified upper bounds on analytic constants by
refining proofs inside a Lean 4 + Mathlib workspace. Two of its components
could each be responsible for the results:

1. **The partial formalization.** The Lean reduction chain, the locked
   trust surface, and the evaluator gate. It turns "improve the constant"
   into a machine-checkable target that admits partial credit.
2. **The agentic system.** The planner/generator/evaluator sprint loop,
   with tools, persistent memory, and multi-step plans.

We ablate each in turn and measure how much of the original improvement
survives.

The test problem is the sprint-016 iteration of the Grothendieck case
study (Lemma 5.4 of Braverman et al. 2011). At the starting snapshot the
workspace certifies Cr = 1; the original run improved this to 1/32 in a
single 2,360 s iteration, by a representational change to the proof rather
than by re-tuning numerical parameters. Every ablation starts from the
identical snapshot and receives the same budget the full framework used:
8,652 s of wall clock and 544,294 output tokens.

## Setup

Four configurations:

* **Full framework** (reference): the unmodified system.
* **No partial formalization**: the same agentic system, but with the
  formalization removed the only checkable statement left is the published
  constant itself. The task is restated accordingly: certify a rational
  below Krivine's bound, starting from the published frontier.
* **Basic agent**: formalization kept; the agentic system is replaced by a
  minimal loop. One tool-less model call per step; a harness writes the
  emitted files, runs the build and the evaluator, and returns the
  verbatim output; the model sees a three-step history, and the workspace
  retains its files between steps.
* **No agent**: formalization kept; no loop at all. Independent one-shot
  samples from an identical prompt — one response, no feedback, workspace
  reset between samples — drawn until the time and token budgets are both
  spent, keeping the best sample.

The basic-agent and no-agent configurations receive byte-identical
starting context: the entire partial formalization, the source paper, and
the workspace notes. We test the no-agent configuration because the basic
agent, though minimal, is still agentic in function — it retains its
previous attempts and iterates on its own best candidate — so it does not
by itself isolate the contribution of the underlying model.

## Results

| Configuration | Best certified Cr | Improvement over start |
|---|---|---|
| Full framework | 1/400,000 = 2.5e-6 | 400,000× |
| Basic agent | 1/250 = 4.0e-3 | 250× |
| No agent | 1/14 = 7.1e-2 | 14× |
| No partial formalization | none below the published bound | — |

For reference, the original run's improvement at this iteration was 32×.

**No partial formalization.** No certified value below Krivine's bound was
ever produced. The budget went to reconstructing supporting definitions
and re-certifying values marginally above the published bound (best:
4×10⁻¹¹ above it). This is the expected failure mode: with the
formalization removed there is no sequence of checkable intermediate
claims, so the only available target is the published frontier itself.

**No agent.** Six samples, each ~130k output tokens. One emitted no usable
file, one compiled but failed verification, and four were accepted, at
1/14, 1/10, 2/25, and 8143/100000. All four accepted samples contain the
same idea: replacing a loose triangle-inequality split in the M_pp oracle
with a decomposition around H₀ plus a Cauchy estimate on the O(η)
difference. The one-shot output distribution concentrates on this single
idea, with scores confined to 0.07–0.1; additional samples would most
likely have drawn it again.

**Basic agent.** Begins with that same idea, then improves it across four
accepted candidates (V12–V15), ending at 4.0e-3, a factor of 18 below the
no-agent result. It also independently conceived the merged-oracle route
the full framework used — the same algebraic identity and the same
cancellation. Its first Lean attempt, a separate library module, failed to
compile on a style linter; two calls were spent routing around the failure
rather than diagnosing it, and a version of the route was completed only
inside the final accepted candidate. The first three accepted candidates
are numerical refinements of the initial route, and nothing was built on
top of the completed structural change.

**Full framework.** Chained four sprints: it formalized the merged-oracle
route in Lean, then added a change of domain (lens/arcsin) on top, each
sprint building on the previous sprint's accepted artifact. The result is
a further factor of 1,600 beyond the basic agent.

## Discussion

**Ablating the partial formalization shows it is essential.** With the
formalization removed, the same agentic system made no measurable
progress: it spent its budget re-deriving known results at the published
frontier. The partial formalization is what converts an open problem into
a sequence of locally checkable improvements; every configuration that
had it made progress, and the one that lacked it made none.

**Ablating the agentic system shows a graded contribution.** The outcomes
order cleanly: no agent 14×, basic agent 250×, full framework 400,000×.
Removing the agent entirely still recovers real progress — the model's
single-response output already contains a genuine analytic improvement —
so part of the original result is attributable to the underlying model
rather than to the system around it. But one-shot sampling saturates at
its first idea. Adding feedback and memory (the basic agent) is worth a
further factor of 18: the system can now iterate past its first idea,
but slowly — every build failure costs a full model call to repair, so
the one structural change it conceived was completed only at the end of
its budget, with nothing composed on top of it. The
full framework accounts for the remaining factor of 1,600, and the
mechanism is visible in the transcripts: it completed structural changes
in Lean and composed successive changes across iterations. Each layer's
contribution is thus identifiable — the base model supplies the first
idea, iteration refines it, and the full agentic system enables structural
change and composition.

**Caveats.** The no-agent stopping rule (sample until time and tokens are
both exhausted) allowed a 44% overrun of the token budget — more than the
basic agent actually consumed — so its budget was generous; this only
reinforces the comparison's direction. The basic-agent extension and the
no-agent run executed without concurrent load, unlike the reference run.
The tool-less configurations ran inside Claude Code with tools blocked but
still visible, a bias in the ablations' favour. The best no-agent and
basic-agent candidates rest on the same new numerical oracle, whose
values await a planned dense-sampling soundness cross-check. Each
configuration was run once (N=1); the factors of 18 and 1,600 are point
estimates.

## Artifacts

Run directories (internal names: A = full framework, B = basic agent,
Bos = no agent, C = no partial formalization):

* Full framework: `runs/grothendieck016-armA-{01,02}`
* Basic agent: `runs/grothendieck016-armB-{01,02,03}` (03 is the
  token-parity extension that produced 4.0e-3; the time-matched best was
  1.1e-2)
* No agent: `runs/grothendieck016-armBos-01`, runner
  `harness/run_arm_b_groth16_oneshot.py`, per-sample responses, files, and
  evaluator output under `attempt_*`
* No partial formalization: `runs/grothendieck016-armC-{01,02}`
