# Sprint <NNN>: <one-line title>

**Created**: <YYYY-MM-DD HH:MM> by Planner
**Parent candidate**: <`Candidates/V<K>.lean` for any K < N — most often V<N-1> (linear chain), but use V0 when starting fresh, or any earlier V<K> when reviving a property the trajectory lost. State the reason briefly if K ≠ N-1.>
**Target file**: <Candidates/V<N>.lean | production file path>
**Direction**: <formula-change | identity-refine | contour-change | uses-approved-proposal_<NNN> | other-theoretical>  <!-- axiom-prove and parameter-only directions are not permitted in the current regime; see Bulletin.md "Current priority" -->
**Tier**: <`ambitious` (default in current regime — substantial Lean writing, hard proof, ≤3 hours), or `cheap` only if the sprint is genuinely surgical (one-line lemma, ≤30 min)>

## Goal (one sentence)

<Single declarative sentence: what mathematical change is being
made and to what end-state. Be decisive — pick the move, not an
arbitrary intermediate.>

## Mathematical insight (required, ≤ 5 sentences)

<Describe the *math* being attempted, not just the edit. What
inequality, identity, or proof-method shift powers this sprint?
Why is the new bound/proof tighter or more elegant than what's
currently in the candidate? Cite the relevant section of
`Proof/Lib/Lemma54_Paper*.lean` (and, where relevant, of the paper)
that this sprint replaces or proves. A sprint whose insight reads
"lower M_val from X to Y" is forbidden in the current regime
(see Bulletin's REGIME directive); the insight must be a structural
move (formula-change / identity-refine / contour-change) or one
that consumes a freshly-approved proposal's new infrastructure.
Axiom-prove (turning an existing trusted axiom into a Lean
theorem) is also forbidden — `Cr_val` doesn't move, so the
engineering hours are not justified.>

## Why (≤ 3 sentences, must include numerical evidence)

<Cite the Scratch/ exploration that justifies the choice. Include
the specific output of the Python script you ran — typically a
`Scratch/sprint_<NNN>_planner_<topic>.py` showing the proposed
alternative bound is materially tighter than the current `Cr_val`,
or evidence that an approved proposal's new infrastructure is now
in place and ready to use.>

## Concrete edits expected

- <File path>: <minimal change description>.
- <File path>: <minimal change description>.

## Acceptance criteria

1. <Mechanically checkable check #1 — typically a `lake env lean`
   exit code or `Evaluator.py` exit code.>
2. <Mechanically checkable check #2 — typically an inequality on a
   parsed log field, e.g. `Cr_val < <previous>`.>
3. <Mechanically checkable check #3.>

(All three must be parseable as `bash` commands or `grep`-able log
fields.)

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration.
- Modify <list specific paths the Generator must not touch>.
- Refactor unrelated code.

## Time budget

≤ <minutes> minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" →
  `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) →
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap
  exceeded; please re-scope".
