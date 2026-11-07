# Sprint 004: Lift sprint 003's closed-form `diskExcess` upper bound into a brand-new `(2)+(3)+(4)`-only sufficient condition for `ValidKorenblumBound`

**Created**: 2026-05-02 09:30 by Planner
**Parent candidate**: `Candidates/V3.lean`
**Target file**: `Candidates/V4.lean`
**Direction**: section2-proof

## Goal

Ship a *new generic Lean theorem*

```text
valid_of_eq2_eq3_eq4_annulus_budget :
    {c : ℝ} →
    0 < c → c < 1 →
    (∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ : ℝ, c < ρ ∧ ρ < 1 ∧
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
          (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b c
            + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ
            ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c) →
    ValidKorenblumBound c
```

in `Proof/Reduction.lean`. The proof must:

1. Unfold `ValidKorenblumBound` via the existing constructor pattern
   (`refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`).
2. From the hypothesis, obtain the witness
   `⟨ρ, hcρ, hρ1, hInt, hBudget⟩`.
3. Apply sprint 003's existing
   `diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt`
   to obtain
   `diskExcess paper.circleGap c ≤ <closed-form bound>`.
4. Chain via `le_trans` against `hBudget` to conclude
   `diskExcess paper.circleGap c ≤ annulusExcess paper.circleGap c`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V4.lean` at the same `c = 0.3554` that compiles, scores
`≥` V3, and *materializes* the new chain by using
`valid_of_eq2_eq3_eq4_annulus_budget` somewhere in its closure — even if V4
ultimately falls back to `valid_of_eq15` for the final sink theorem (e.g. as a
verified side lemma `v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles`
that exercises the new sufficient condition against an *abstract*
budget hypothesis).

## Why

This is the natural and structurally novel downstream of sprint 003. Sprint 003
delivered a closed-form *upper* bound on `diskExcess` derived only from
equations `(2)`, `(3)`, `(4)`. Sprint 004 lifts that bound into a complete
*end-to-end* sufficient condition for `ValidKorenblumBound c` that
**bypasses every ingredient** of the seed `(15)` route:

- no `paper.eq14_combined`,
- no `paper.eq{5..13}_*`,
- no `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand{1,2}`,
- no `WangOuter.paperLambda`,
- no `Eq15ScalarBound`,
- no adjacency hypothesis on `annulusLeftExcess + annulusRightExcess`.

The only paper equations consumed are `(2)`, `(3)`, `(4)` (via sprint 002 →
sprint 003) plus the integral definition of `annulusExcess` itself. This is
the **first end-to-end reduction route in the workspace that does not pass
through `scalarCriterion`/`paperLambda`/`(15)`**. It is a strictly stronger
sufficient condition than the seed's `(15)` route in the sense that it
offers an alternative analytical chain — future sprints that prove the
budget hypothesis pointwise (for some chosen `ρ(c)` and using either the
`(8)+(9)`-derived bridge `sigmaMinus ρ ≤ Λ(c,ρ)·circleGap ρ` already exposed
as `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` or a direct lower bound on
`annulusExcess` from `eq3` at the outer radius) can *push `c` upward without
ever introducing a new `(15)`-style scalar axiom*.

Why this is **not** a numerical push:

- The new theorem's statement is purely structural: it exposes the
  closed-form upper bound from sprint 003 and asks for an annulus-side
  budget at *some* free `ρ ∈ (c, 1)`. No numeric bounds are baked in.
- The bound's coefficients `α(c, ρ) = (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` and
  `β(c, ρ) = (c⁶/6)/(ρ²−c²)` are inherited verbatim from sprint 003 — no
  re-derivation, no tightening.
- The candidate `V4.lean` keeps `c = 0.3554` and discharges the sink theorem
  via the existing `valid_of_eq15` so the score is exactly preserved at
  `1777/5000`.

Why this is **bounded enough for one Generator session**:

- The proof body is at most a dozen lines: unfold `ValidKorenblumBound`,
  destructure the witness, apply sprint 003's lemma, `le_trans`. There is
  no new integration, no new algebra, no new positivity argument — those
  were all done in sprints 002 and 003.
- The side-lemma in `V4.lean` is a one-line application of the new theorem
  against an abstract budget hypothesis (i.e., the candidate accepts the
  budget as an opaque assumption and confirms it discharges the contract).

Why this opens a clear path to a future `c`-pushing sprint without trust
expansion:

- The annulus-side budget is the *only* outstanding ingredient. A future
  sprint can attack it via:
  (a) lower-bounding `annulusExcess` by `2ρ·circleGap ρ · ε` for some
      `ε > 0` neighborhood of the chosen `ρ` — purely Lebesgue/continuity,
      no new paper axioms;
  (b) chaining `(8)+(9)` to express `circleGap ρ` in terms of
      `sigmaMinus ρ` and Λ, then using `sigmaMinus ρ = ρ²·sigmaZeroMinus ρ`
      (provable from the series definition since `n2Pred` requires
      `0 < k`, so the `k=0` term drops); or
  (c) integrating the `(8)+(9)`-derived bridge over a sub-interval of
      `(c, 1)` to produce an *integrated* lower bound on `annulusExcess`
      directly in terms of `sigmaZeroMinus ρ` for ρ in the sub-interval.
- Each of those routes uses only the already-trusted surface
  (`Section2Assumptions` plus `OneModePaperBridge`-style lemmas that sit
  inside the allowed import policy), so the present sprint sets up a
  strictly larger landing pad for the next move.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add new generic theorem `valid_of_eq2_eq3_eq4_annulus_budget` matching
    the shape above. The proof must:
    1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
    2. Obtain `⟨ρ, hcρ, hρ1, hInt, hBudget⟩` from the budget hypothesis
       applied to `paper`.
    3. Invoke `diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1
       hInt` to obtain the closed-form upper bound on `diskExcess`.
    4. `exact le_trans hUpper hBudget`.
  - The new theorem's body must NOT mention `paper.eq14_combined`,
    `paper.eq15_*`, `paper.eq{5,6,7,8,9,10,11,12,13}_*`,
    `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
    `Korenblum.scalarIntegrand{1,2}`, `WangPaperSideConditions.*`, the
    `eq15_implies_disk_le_annulus` helper, or the `valid_of_eq15` /
    `valid_of_eq12_eq13` reductions. The only theorems it may invoke from
    `Reduction.lean` are `diskExcess_upper_bound_of_eq2_eq3_eq4` and the
    `ValidKorenblumBound` constructor (plus `le_trans`/`Exists.intro`-style
    plumbing).
  - Add a one-line module-doc comment above the new theorem explaining that
    this is the Sprint 004 end-to-end sufficient condition: a complete
    `ValidKorenblumBound c` reduction that goes through equations
    `(2) + (3) + (4)` only (via sprints 002 and 003) plus an annulus-side
    budget hypothesis, with no use of `Eq15`/`paperLambda`/`scalarCriterion`.

- `ProofRefinement/Korenblum/Candidates/V4.lean`:
  - `-- @parent V3`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly as
    in V1/V2/V3; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does not
    regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles
        (h_budget :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ : ℝ, c_value < ρ ∧ ρ < 1 ∧
              IntervalIntegrable
                (fun r => 2 * r * PaperAxioms.circleGap a b r)
                volume 0 c_value ∧
              (c_value ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c_value ^ 2)
                  / (ρ ^ 2 - c_value ^ 2)
                  * PaperAxioms.sigmaZeroMinus a b c_value
                + (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
                  * PaperAxioms.sigmaZeroMinus a b ρ
                ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value) :
        ValidKorenblumBound c_value :=
      valid_of_eq2_eq3_eq4_annulus_budget c_value_pos c_value_lt_one h_budget
    ```

    so the new sufficient condition is exercised at the seed `c_value`
    against an abstract budget hypothesis, but the sink theorem is still
    discharged via `valid_of_eq15`. The side lemma must NOT be `axiom`-ed,
    must NOT call any seed axiom, and must NOT close the budget hypothesis
    (the budget is intentionally accepted as an explicit premise, mirroring
    sprint 001's `h_adjacency` and sprint 003's `hInt`). It exists purely
    to verify that the new reduction chain typechecks at the seed
    `c_value`.

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`, no
  edits to `lemma.toml`, no edits to `Candidates/V0.lean`, `V1.lean`,
  `V2.lean`, or `V3.lean`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V4.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V4.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V4 scores `≥` V3 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V4.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -nE 'eq14_combined|Eq15|eq5_|eq6_|eq7_|eq8_|eq9_|eq10_|eq11_|eq12_|eq13_|paperLambda|scalarCriterion|scalarIntegrand|WangPaperSideConditions|valid_of_eq15|valid_of_eq12_eq13|eq15_implies_disk_le_annulus' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that those substrings appear *only* outside the body of
   `valid_of_eq2_eq3_eq4_annulus_budget` — the new theorem's proof must use
   exactly `diskExcess_upper_bound_of_eq2_eq3_eq4` plus `le_trans` and the
   `ValidKorenblumBound` constructor.
6. `grep -n 'valid_of_eq2_eq3_eq4_annulus_budget' korenblum/ProofRefinement/Korenblum/Candidates/V4.lean`
   returns at least one match (V4 actually invokes the new reduction in its
   body, inside `v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles`).
7. `grep -n 'valid_of_eq2_eq3_eq4_annulus_budget' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site.
8. `grep -n 'diskExcess_upper_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes sprint 003's lemma (i.e. there are at
   least two matches — the original definition site from sprint 003 and at
   least one use inside `valid_of_eq2_eq3_eq4_annulus_budget`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, or any file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Discharging the budget hypothesis from `Section2Assumptions` itself. That
  is the explicit subject of a *future* sprint. The budget must remain an
  explicit premise on `valid_of_eq2_eq3_eq4_annulus_budget` here.
- Discharging the `IntervalIntegrable` hypothesis on `2r · paper.circleGap r`
  on `[0, c]`. That is also a future-sprint question and is intentionally
  bundled inside the budget existential here so a future sprint can attack
  it together with the budget.
- Choosing a concrete `ρ(c)` (e.g. `ρ = √((1+c²)/2)` or any tuned value).
  The free parameter `ρ` must remain *existentially* quantified inside the
  budget hypothesis — sprint 004 should not commit to any particular
  `ρ` policy.
- Attempting a strictly larger `c_value` in this sprint — the goal is the
  structural new chain, not a numerical push. Any future sprint that
  *does* push `c` is expected to consume `valid_of_eq2_eq3_eq4_annulus_budget`
  by proving the budget hypothesis at the new `c`.
- Adding a *second* new reduction route that mixes sprint 001's
  `valid_of_eq12_eq13` with sprint 003's bound. That is a separate
  hybridisation question — keep this sprint single-axis.
- Adding new Wang-paper axioms, new oracle entries, or any new `Proposals/`
  entry. This sprint must be self-contained against the current trust
  surface.
- Refactoring or simplifying sprints 001, 002, or 003. Their lemmas are
  consumed verbatim.

## Time budget

≤ 45 minutes runtime. The proof body is short — most of the budget is
typing the contract, the side lemma in `V4.lean`, and verifying the
`grep`-shaped acceptance criteria.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- The Generator finds that `diskExcess_upper_bound_of_eq2_eq3_eq4`'s
  conclusion does not literally syntactically match the budget's RHS
  because of how Lean prints the `(c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) /
  (ρ ^ 2 - c ^ 2)` term (e.g. associativity of `*` and `/`): close the
  `le_trans` step with an explicit `have hUpper := ...; have hBudget' :=
  ...; linarith` — the inequality is between two real numbers and
  `linarith` will handle any cosmetic associativity.
- The proof requires invoking `paper.eq{5..15}_*`, `WangOuter.paperLambda`,
  `Korenblum.scalar*`, `valid_of_eq15`, `valid_of_eq12_eq13`, or
  `eq15_implies_disk_le_annulus` to close: `STATUS=BLOCKED` — that would
  defeat the structural novelty of this sprint and indicates the contract
  needs revision.
- The Generator wants to *prove* the budget hypothesis from
  `Section2Assumptions` instead of taking it as a premise: `STATUS=BLOCKED` —
  that is explicitly out of scope and is the subject of a future sprint.
- The proof would require a Mathlib lemma not yet in the pinned toolchain:
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Any of acceptance criteria 4, 5, 6, 7, or 8 cannot be satisfied without
  weakening the contract: `STATUS=BLOCKED`.
