# Sprint 001: Add a `(12)+(13)` integrated bypass reduction that avoids `eq14_combined`

**Created**: 2026-05-02 07:30 by Planner
**Parent candidate**: `Candidates/V0.lean`
**Target file**: `Candidates/V1.lean`
**Direction**: section2-proof

## Goal

Ship a *new generic Lean reduction theorem*

```text
valid_of_eq12_eq13 :
    0 < c → c < 1 →
    (∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} (paper : Section2Assumptions a b K c),
        annulusLeftExcess paper.circleGap c + annulusRightExcess paper.circleGap c
          ≤ annulusExcess paper.circleGap c) →
    (∀ {K : ℝ → ℝ → ℝ},
        1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c)) →
    ValidKorenblumBound c
```

in `Proof/Reduction.lean`, whose proof routes through
`paper.eq12_branch1_integrated + paper.eq13_branch2_integrated` and **does not
use** `paper.eq14_combined`. Then ship a `Candidates/V1.lean` at the same
`c = 0.3554` that compiles, scores `≥` V0, and *materializes* the new chain by
using `valid_of_eq12_eq13` somewhere in its closure — even if V1 ultimately
falls back to `valid_of_eq15` for the final theorem (e.g. as a verified side
lemma that exercises the new reduction on the seed paper context).

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

## Why

The current seed closure rides exclusively on `eq14_combined + (15)`. The
bulletin asks for a *new analytical chain through `Section2Assumptions`* even at
the same `c`. Equations `(12)` and `(13)` are the *unintegrated paper form* of
`(14)`: their masses are exactly the two summands of
`Korenblum.scalarCriterion`. Building the bypass reduction now:

- removes the `eq14_combined` dependency from a candidate's critical path,
- exposes branch-asymmetric mass control (`M1` from `(12)` and `M2` from `(13)`
  become independently addressable), which is the natural setup for a *future*
  sprint that proves a strictly stronger sufficient condition by re-weighting
  the two branches,
- does not require any new axioms, oracles, or Mathlib lemmas — only
  `paper.eq12`, `paper.eq13`, the existing `annulusExcess_nonneg` argument from
  `Reduction.lean`, and elementary inequality manipulation,
- gives us a runnable V1 that scores `≥` V0 immediately while the next sprint
  can attack the adjacency hypothesis (`annulusLeftExcess + annulusRightExcess
  ≤ annulusExcess`) as a separately certified Lean lemma.

The adjacency premise is intentionally *exposed as a hypothesis* of the new
reduction. Section2Assumptions does not currently expose integrability of
`2ρ · circleGap a b ρ` on `[c, 1]`, so deriving the adjacency in-house would
balloon this sprint. Keeping it as an explicit hypothesis keeps the sprint
bounded and frames a clean follow-up.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add new generic theorem `valid_of_eq12_eq13` matching the shape above.
  - The proof must:
    1. Use `paper.eq12_branch1_integrated` to get
       `M1 * diskExcess ≤ annulusLeftExcess` where
       `M1 = ∫ ρ in c..branchSplit c, Korenblum.scalarIntegrand1 c (paperLambda K c) ρ`.
    2. Use `paper.eq13_branch2_integrated` symmetrically for the right branch.
    3. Add the two inequalities to get `(M1 + M2) * diskExcess ≤
       annulusLeftExcess + annulusRightExcess`, then apply the adjacency
       hypothesis.
    4. Use `M1 + M2 = Korenblum.scalarCriterion c (paperLambda K c) ≥ 1` and
       case-split on `0 ≤ diskExcess` vs `diskExcess < 0`, mirroring the
       existing `eq15_implies_disk_le_annulus` proof.
    5. Reuse the existing `annulusExcess_nonneg` private lemma for the
       negative-disk case.
  - Must NOT mention `paper.eq14_combined` in the new theorem.
- `ProofRefinement/Korenblum/Candidates/V1.lean`:
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0).
  - Reuse the seed axiom `hEq15_seed_3554` (rename or re-declare locally;
    keep the seed-axiom name in `lemma.toml:[seed_axioms].allowed`).
  - Prove the final theorem via `valid_of_eq15` (so the score doesn't regress).
  - Additionally, prove a *verifying* side lemma
    ```
    theorem v1_eq12_eq13_chain_compiles
        (h_adjacency : ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
              annulusLeftExcess paper.circleGap c_value
                + annulusRightExcess paper.circleGap c_value
                ≤ annulusExcess paper.circleGap c_value) :
        ValidKorenblumBound c_value :=
      valid_of_eq12_eq13 c_value_pos c_value_lt_one h_adjacency
        (fun {K} => by
          have := hEq15_seed_3554 K
          simpa [ProblemAxioms.Eq15ScalarBound, PaperAxioms.Eq15ScalarBound]
            using this)
    ```
    so the new chain is exercised at the seed paper context but the candidate
    contract is still discharged via `valid_of_eq15`.
- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `KorenblumPaper/*`, no edits to `lemma.toml`.

## Acceptance criteria

1. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V1.lean` succeeds.
2. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V1.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V1 scores `≥` V0 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V1.hEq15_seed_3554}` (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits them) — no new free-floating axioms.
5. `grep -n 'eq14_combined' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean` shows the substring still present only in `eq15_implies_disk_le_annulus`, and the new `valid_of_eq12_eq13` proof body does not mention `eq14_combined`.
6. `grep -n 'valid_of_eq12_eq13' korenblum/ProofRefinement/Korenblum/Candidates/V1.lean` returns at least one match (V1 actually invokes the new bridge in its body, even if only inside `v1_eq12_eq13_chain_compiles`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean` or any file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Trying to discharge the adjacency hypothesis
  `annulusLeftExcess + annulusRightExcess ≤ annulusExcess` inside this sprint.
  That is the explicit subject of the **next** sprint and must remain a
  hypothesis on `valid_of_eq12_eq13` here.
- Attempting a strictly larger `c_value` in this sprint — the goal is the
  structural new chain, not a numerical push.
- Adding any new Wang-paper axioms or oracle entries.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Generator finds the new reduction provable but the V1 wiring fails for a
  *naming or namespace* reason inside the workspace: try one repair pass, then
  `STATUS=READY_FOR_EVALUATION` (or `STATUS=BLOCKED` with a precise diagnosis).
- The new `valid_of_eq12_eq13` proof requires a non-trivial algebraic identity
  the Generator cannot close in one session (e.g. an unexpected mismatch
  between the integrand definitions in `PaperAxioms` and `Korenblum`):
  `STATUS=BLOCKED` with the exact unprovable subgoal copied into the report.
- The proof would require a new `Mathlib` lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
- Any of acceptance criteria 4, 5, or 6 cannot be satisfied without weakening
  the contract: `STATUS=BLOCKED`.
