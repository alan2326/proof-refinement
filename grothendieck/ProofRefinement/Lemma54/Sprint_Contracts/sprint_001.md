# Sprint 001: Tighten `M_val` from 4000 to 3700 (harness shakedown)

**Created**: 2026-04-29 by hand (harness shakedown)
**Parent candidate**: `ProofRefinement/Lemma54/Candidates/V0.lean`
**Target file**: `ProofRefinement/Lemma54/Candidates/V1.lean`
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V1.lean` as a copy of `V0.lean` with the single edit
`def M_val : ℝ := 4000` → `def M_val : ℝ := 3700`, and verify the
per-candidate Evaluator passes (oracle accepts, score drops).

## Why (≤ 2 sentences)

The certified `compute_M_bound_production` returns ~3600.44 on the
production rectangle `Ω(57/1000, 293/250)`. V0's `M_val = 4000`
inherits production's conservative buffer; tightening to `3700`
keeps a healthy 100-point margin above the certified value while
cutting the score `Cr_val ∝ M²` by `(3700/4000)² ≈ 0.86×`.

## Concrete edits expected

- **Create** `ProofRefinement/Lemma54/Candidates/V1.lean` as a
  byte-identical copy of `Candidates/V0.lean` with three changes:
  1. The header comment block updated to reference V1 / sprint_001
     and to declare `-- @parent Candidates/V0.lean`.
  2. `def M_val : ℝ := 4000` changed to `def M_val : ℝ := 3700`.
  3. Nothing else.
- **Append** a one-paragraph entry to
  `ProofRefinement/Lemma54/Experience.md` summarising the change
  (no claims about whether checks pass — just describe the change).

## Acceptance criteria

1. `ls ProofRefinement/Lemma54/Candidates/V1.lean` succeeds.
2. The change set (`git status --porcelain`) shows exactly one new
   file under `Candidates/V1.lean` plus optional appends to
   `Experience.md` / `Bulletin.md`. No other path appears.
3. `uv run ProofRefinement/Lemma54/Evaluator.py --file
   ProofRefinement/Lemma54/Candidates/V1.lean` exits 0 and reports
   `pass: true`. The audit shows the oracle line
   `pass Braverman.PaperV0.h_M_oracle: declared M_val=3700 ≥ oracle …`.
4. The new `Cr_val` score (the rational upper bound emitted by the
   Evaluator) is strictly smaller than V0's
   `1600821631885818724352/1953125 ≈ 8.196·10¹⁴`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration.
- Modify `V0.lean` or any other pre-existing file.
- Modify `Proof/`, `LeanProof/`, `ProofGraph/`, `lemma.toml`,
  `Evaluator.py`, or any helper script.
- Refactor or rewrite anything beyond the `M_val` numeric change and
  the header-comment update.

## Time budget

≤ 15 minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" →
  `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) →
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded;
  please re-scope".
