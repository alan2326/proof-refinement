# Sprint 006: Closed-form integrated lower bound on `annulusExcess` from sprint 005's outer pointwise bound

**Created**: 2026-05-02 12:30 by Planner
**Parent candidate**: `Candidates/V5.lean`
**Target file**: `Candidates/V6.lean`
**Direction**: section2-proof

## Goal

Ship two *new generic Lean theorems* in `Proof/Reduction.lean`, both consuming
sprint 005's deliverables:

1. A small structural side lemma

   ```text
   sigmaZeroMinus_nonneg_of_pos
       (a b : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
       0 ≤ PaperAxioms.sigmaZeroMinus a b ρ
   ```

   Proof: from sprint 005's identity
   `PaperAxioms.sigmaMinus a b ρ = ρ^2 * PaperAxioms.sigmaZeroMinus a b ρ`
   and `OneModePaperBridge.sigmaMinus_nonneg a b ρ`, conclude
   `0 ≤ ρ^2 * sigmaZeroMinus`. Use `pow_pos hρ 2` together with
   `nonneg_of_mul_nonneg_left` (or `le_div_iff₀` / `nonneg_of_mul_nonneg_right`
   — pick the variant whose direction matches Mathlib's signature) to
   conclude `0 ≤ sigmaZeroMinus a b ρ`.

   The body must NOT reference any `Section2Assumptions` field (this is a
   pure series statement) and must NOT call any seed axiom. It must use
   exactly `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (sprint 005) and
   `OneModePaperBridge.sigmaMinus_nonneg` plus arithmetic.

2. The integrated outer-side lower bound

   ```text
   annulusExcess_lower_bound_of_eq8_eq9 :
       {a b : ℕ → ℂ} → {K : ℝ → ℝ → ℝ} → {c : ℝ} →
       (paper : Section2Assumptions a b K c) →
       {ρ₁ ρ₂ : ℝ} →
       0 < c → c < ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ < 1 →
       IntervalIntegrable
         (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1 →
       IntervalIntegrable
         (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
           / WangOuter.paperLambda K c ρ) volume ρ₁ ρ₂ →
       (∫ ρ in ρ₁..ρ₂,
           2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
             / WangOuter.paperLambda K c ρ)
         ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
   ```

   This is the **structural counterpart** of sprint 003: where sprint 003
   integrated sprint 002's pointwise inner-disk *upper* bound to bound
   `diskExcess` from above, sprint 006 integrates sprint 005's pointwise
   outer-annulus *lower* bound to bound `annulusExcess` from below. The
   integration sub-interval `[ρ₁, ρ₂] ⊆ (c, 1)` is intentionally exposed
   as a `forall` so a downstream sprint can choose it (e.g. `[ρ₁, ρ₂] =
   [c + ε, 1 − ε]` for appropriate `ε`).

   The proof must route through:
     - `circleGap_outer_lower_bound_of_eq8_eq9` (sprint 005) applied
       pointwise on `Ioo ρ₁ ρ₂` to obtain
       `2 * ρ ^ 3 * Z_ρ / Λ(c, ρ) ≤ 2 * ρ * paper.circleGap ρ` for each
       `ρ ∈ Ioo ρ₁ ρ₂`;
     - `intervalIntegral.integral_mono_on_of_le_Ioo` to integrate the
       pointwise bound over `[ρ₁, ρ₂]`, yielding
       `∫ … ≤ ∫_{ρ₁}^{ρ₂} 2ρ · circleGap ρ = annulusSlice circleGap ρ₁ ρ₂`;
     - `AnnulusIntegralReduction.annulusSlice_add_adjacent` (twice if
       needed) to split `annulusSlice circleGap c 1` into
       `annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1`;
     - `AnnulusIntegralReduction.annulusSlice_nonneg` plus
       `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` to discharge
       `0 ≤ annulusSlice c ρ₁` and `0 ≤ annulusSlice ρ₂ 1` (since
       `circleGap ρ ≥ 0` on `(c, 1)` and the polar Jacobian `2ρ ≥ 0`);
     - chain `annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1 =
       annulusSlice c 1 = annulusExcess paper.circleGap c` and `linarith`.

   The body of the new theorem must NOT mention `paper.eq{2,3,4,5,6,7,10,11,
   12,13}_*`, `paper.eq14_combined`, `paper.eq15_*`,
   `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand{1,2}`,
   `valid_of_eq15`, `valid_of_eq12_eq13`, `valid_of_eq2_eq3_eq4_annulus_budget`,
   `eq15_implies_disk_le_annulus`, or any
   `WangPaperSideConditions.*` lemma other than `paperLambda_pos` (which is
   indirectly invoked by sprint 005's lemma — it's fine if it appears in
   the call graph, just not as a direct identifier in the new theorem
   body).

   `sigmaZeroMinus_nonneg_of_pos` from (1) is consumed in step (3)/(4) to
   discharge non-negativity of the integrand on `(ρ₁, ρ₂)` (so that
   `IntervalIntegrable` of the LHS plus pointwise bound suffices for
   `intervalIntegral.integral_mono_on_of_le_Ioo`'s monotonicity step
   without requiring strict pointwise positivity).

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V6.lean` at the same `c = 0.3554` that compiles, scores
`≥` V5, and *materializes* the new chain by using
`annulusExcess_lower_bound_of_eq8_eq9` somewhere in its closure — even if V6
ultimately falls back to `valid_of_eq15` for the final sink theorem (e.g. as a
verified side lemma `v6_annulusExcess_lower_bound_chain_compiles` that
exercises the new bound on the seed paper context against an abstract
`IntervalIntegrable` premise).

## Why

The bulletin's current priority is *novel analytical derivations* that build
toward an end-to-end `(15)`-free reduction. After sprint 005, the workspace
has:

- sprint 003: a closed-form *upper* bound on `diskExcess` from `(2)+(3)+(4)`;
- sprint 004: an end-to-end `(15)`-free reduction
  `valid_of_eq2_eq3_eq4_annulus_budget` that takes an *annulus-side budget*
  hypothesis as a premise;
- sprint 005: a pointwise *lower* bound on the annulus integrand
  `2ρ · circleGap ρ` from `(8)+(9)` plus the new identity
  `sigmaMinus = ρ²·sigmaZeroMinus`.

The *only* missing piece between sprints 005 and 004 is the integrated form
of sprint 005's pointwise bound: turn the pointwise lower bound into an
integrated lower bound on `annulusExcess`. Once that lands, a future sprint
can chain (`diskExcess` upper bound from sprint 003) ≤ (closed form) ≤
(annulusExcess lower bound from sprint 006) = annulusExcess, closing
sprint 004's budget hypothesis without `Eq15`. **This is the last
generic ingredient before an end-to-end `(15)`-free `ValidKorenblumBound`
proof becomes achievable.**

Why this is **structurally novel**:

- It is the **first integrated outer-side bound on `annulusExcess`** in the
  workspace. Every prior sprint either bounded `diskExcess` (sprints 002,
  003) or bounded the annulus integrand pointwise (sprint 005). Integration
  on the annulus side has not been done.
- It is the **first workspace theorem that combines sprint 005's identity
  with `intervalIntegral.integral_mono_on_of_le_Ioo`-style integration**.
  The pattern is well-validated by sprint 003, but sprint 003 ran on the
  *inner disk*; sprint 006 runs the same machinery on the *outer annulus*
  with a `Λ(c,ρ)`-laden integrand instead of a polynomial integrand.
- It introduces a brand-new auxiliary lemma `sigmaZeroMinus_nonneg_of_pos`
  derived from sprint 005's identity, which is reusable by any future
  sprint that needs `Z_ρ ≥ 0` (e.g. to drop the `Z_ρ` term from sprint
  003's `α·Z_c + β·Z_ρ` upper bound when `β ≤ 0`, or to dominate
  sigmaZeroMinus by sigmaMinus / ρ²).
- The dependency signature is fundamentally different from the seed
  `(15)` route and from sprints 001/002/003/004: it consumes only `(8)`,
  `(9)`, sprint 005's identity, and Mathlib measure-theory plumbing. No
  `paperLambda`-integrated `scalarCriterion`, no `paper.eq{2,3,4,5,6,7,
  10,11,12,13,14,15}_*`.

Why this is **not a numerical push**:

- No `c`-tuning, no choice of `ρ₁` or `ρ₂`, no concrete numbers in the
  theorem statement. The bound is purely structural with the
  sub-interval and integrability premises exposed as hypotheses.
- `c_value` stays at `3554/10000`; V6 still discharges the sink theorem
  via `valid_of_eq15` so the score is exactly preserved at `1777/5000`.
- The "numerics" are entirely inherited from sprint 005's already-trusted
  `paperLambda > 0` invocation.

Why this is **bounded enough for one Generator session**:

- Theorem (1) is at most ~10 lines: invoke sprint 005's identity,
  invoke `sigmaMinus_nonneg`, divide by `ρ² > 0`. The hardest part is
  picking the right Mathlib lemma name for "if `0 ≤ x*y` and `0 < x`
  then `0 ≤ y`" (Mathlib has `nonneg_of_mul_nonneg_left`,
  `le_of_mul_le_mul_left`, `pos_of_mul_pos_left`, etc.; if none match
  exactly, a one-line `nlinarith [...]` after introducing `pow_pos` will
  close it).
- Theorem (2) closely mirrors sprint 003's structure: a pointwise bound,
  an `intervalIntegral.integral_mono_on_of_le_Ioo` step, and a chain of
  `annulusSlice_add_adjacent` + `annulusSlice_nonneg` + `linarith`. Each
  sub-step has a worked precedent in `Reduction.lean` already. Estimated
  ~40-60 lines.
- The candidate side lemma is a one-line application of the new bound
  against an abstract integrability premise.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic side lemma `sigmaZeroMinus_nonneg_of_pos`
    matching the shape above. The proof must:
      1. Introduce
         `hId : PaperAxioms.sigmaMinus a b ρ = ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ`
         from `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`.
      2. Introduce
         `hNonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ` from
         `OneModePaperBridge.sigmaMinus_nonneg`.
      3. Rewrite by `hId` to obtain
         `0 ≤ ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ`.
      4. Use `pow_pos hρ 2 : 0 < ρ ^ 2` and divide / case-split to
         conclude `0 ≤ PaperAxioms.sigmaZeroMinus a b ρ`. A direct
         `nlinarith [pow_pos hρ 2, ...]` is acceptable if no specific
         Mathlib lemma matches the goal shape.
      5. Must NOT reference `Section2Assumptions` or any `paper.*` field.

  - Add the new generic theorem `annulusExcess_lower_bound_of_eq8_eq9`
    matching the shape above. The proof must:
      1. Establish positivity facts: `0 < ρ₁`, `0 < ρ₂`, `c ≤ ρ₁`,
         `ρ₂ ≤ 1` from the hypotheses.
      2. Show pointwise on `Ioo ρ₁ ρ₂`:
         `2 * ρ^3 * sigmaZeroMinus a b ρ / paperLambda K c ρ ≤
            2 * ρ * paper.circleGap ρ`
         by invoking `circleGap_outer_lower_bound_of_eq8_eq9 paper hc_pos
         hρ_lt hρ_lt_one` for each `ρ ∈ Ioo ρ₁ ρ₂` (where `hρ_lt : c < ρ`
         and `hρ_lt_one : ρ < 1` come from chaining `c < ρ₁ ≤ ρ` and
         `ρ ≤ ρ₂ < 1`).
      3. Integrate the pointwise bound over `[ρ₁, ρ₂]` via
         `intervalIntegral.integral_mono_on_of_le_Ioo (h := hρ₁₂)`,
         where `hρ₁₂ : ρ₁ ≤ ρ₂` is the hypothesis. This yields
         `∫ ρ in ρ₁..ρ₂, 2*ρ^3*Z_ρ/Λ ≤ ∫ ρ in ρ₁..ρ₂, 2*ρ*paper.circleGap ρ`.
      4. Recognize the RHS as
         `AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂`
         (unfold definitionally; this is `rfl` modulo
         `annulusDensity = 2 * ρ * circleGap ρ`).
      5. Split the full annulus integral via
         `AnnulusIntegralReduction.annulusSlice_add_adjacent` twice:
           - `annulusSlice c ρ₁ + annulusSlice ρ₁ 1 = annulusSlice c 1`,
           - `annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1 = annulusSlice ρ₁ 1`.
         Each application requires `IntervalIntegrable
         (annulusDensity paper.circleGap)` on the corresponding
         sub-interval; derive these by restricting the global
         hypothesis `IntervalIntegrable … volume c 1` via
         `IntervalIntegrable.mono_set` (the sub-intervals
         `[c, ρ₁] ⊆ [c, 1]`, `[ρ₁, ρ₂] ⊆ [c, 1]`, `[ρ₂, 1] ⊆ [c, 1]`).
         If `mono_set` requires `Set.uIcc` shape, use
         `Set.uIcc_subset_uIcc_iff_le`-style lemma to convert.
      6. Discharge `0 ≤ annulusSlice c ρ₁` and `0 ≤ annulusSlice ρ₂ 1`
         via `AnnulusIntegralReduction.annulusSlice_nonneg` plus a
         pointwise non-negativity argument: for `ρ ∈ Set.Icc c ρ₁` (or
         `Icc ρ₂ 1`), `circleGap_nonneg_of_eq8_eq9` gives
         `0 ≤ paper.circleGap ρ` whenever `c < ρ < 1` (handle the
         boundary points `ρ = c` and `ρ = 1` via the
         `annulusSlice_nonneg_of_ae` variant which only needs an
         a.e. statement on `Icc`, mirroring the existing
         `annulusExcess_nonneg` proof in `Reduction.lean`).
      7. Conclude by `linarith`-style chaining:
         `∫ … ≤ annulusSlice ρ₁ ρ₂ ≤ annulusSlice ρ₁ ρ₂ + annulusSlice c ρ₁ +
          annulusSlice ρ₂ 1 = annulusSlice c 1 = annulusExcess`.

  - Add a one-line module-doc comment above each new theorem explaining:
      - `sigmaZeroMinus_nonneg_of_pos` is the Sprint 006 corollary of the
        sprint 005 identity that exposes nonnegativity of
        `sigmaZeroMinus` at any positive radius without needing a
        `Section2Assumptions` instance;
      - `annulusExcess_lower_bound_of_eq8_eq9` is the Sprint 006
        integrated outer-side lower bound — the structural counterpart
        of sprint 003's `diskExcess_upper_bound_of_eq2_eq3_eq4` — and
        is the last generic ingredient before an end-to-end
        `(15)`-free `ValidKorenblumBound` proof becomes achievable
        (a future sprint will combine it with sprint 003's upper bound
        and sprint 004's `valid_of_eq2_eq3_eq4_annulus_budget`).

- `ProofRefinement/Korenblum/Candidates/V6.lean`:
  - `-- @parent V5`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3/V4/V5).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly as
    in V1/V2/V3/V4/V5; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does not
    regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v6_annulusExcess_lower_bound_chain_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ₁ ρ₂ : ℝ}
        (hρ₁ : c_value < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ < 1)
        (hIntCircle :
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c_value 1)
        (hIntLambda :
          IntervalIntegrable
            (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
              / WangOuter.paperLambda K c_value ρ) volume ρ₁ ρ₂) :
        (∫ ρ in ρ₁..ρ₂,
            2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
              / WangOuter.paperLambda K c_value ρ)
          ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value :=
      annulusExcess_lower_bound_of_eq8_eq9
        paper c_value_pos hρ₁ hρ₁₂ hρ₂ hIntCircle hIntLambda
    ```

    so the new chain is exercised at the seed `c_value` against abstract
    integrability premises, but the sink theorem is still discharged via
    `valid_of_eq15`. The side lemma must NOT be `axiom`-ed and must NOT
    call the seed axiom. It exists purely to verify that the new bound
    typechecks at the seed `c_value`.

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`, no
  edits to `lemma.toml`, no edits to `Candidates/V0.lean`, `V1.lean`,
  `V2.lean`, `V3.lean`, `V4.lean`, or `V5.lean`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V6.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V6.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V6 scores `≥` V5 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V6.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'sigmaZeroMinus_nonneg_of_pos' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site.
6. `grep -n 'annulusExcess_lower_bound_of_eq8_eq9' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains a use of `circleGap_outer_lower_bound_of_eq8_eq9` and a use of
   `AnnulusIntegralReduction.annulusSlice_add_adjacent`.
7. `grep -n 'annulusExcess_lower_bound_of_eq8_eq9' korenblum/ProofRefinement/Korenblum/Candidates/V6.lean`
   returns at least one match (V6 actually invokes the new bound in its body,
   inside `v6_annulusExcess_lower_bound_chain_compiles`).
8. The body of `annulusExcess_lower_bound_of_eq8_eq9` does NOT mention
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
   `paper.eq7_`, `paper.eq10_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
   `paper.eq14_combined`, `paper.eq15_`, `Korenblum.scalarCriterion`,
   `Korenblum.scalarIntegrand`, `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`, `eq15_implies_disk_le_annulus`,
   or `diskExcess_upper_bound_of_eq2_eq3_eq4`. (Verify with `grep -nE`
   against the substring of the theorem body.)
9. The body of `sigmaZeroMinus_nonneg_of_pos` does NOT reference any
   `paper.*` field at all (it is a pure series lemma about
   `sigmaZeroMinus` and `sigmaMinus`).
10. The body of `annulusExcess_lower_bound_of_eq8_eq9` invokes
    `sigmaZeroMinus_nonneg_of_pos` at least implicitly (either by direct
    reference to discharge integrand non-negativity in the
    `intervalIntegral.integral_mono_on_of_le_Ioo` step, or — if
    `integral_mono_on_of_le_Ioo` does not require non-negativity for the
    monotonicity step — the lemma may go unused in this sprint, in which
    case it must still be defined and exercised somewhere in V6 to count
    as "materialized". Flag in the report which path was taken.

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, `Candidates/V4.lean`, `Candidates/V5.lean`, or any
  file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Discharging the `IntervalIntegrable` premises from `Section2Assumptions`.
  Both integrability hypotheses are intentionally taken as explicit
  premises, mirroring sprint 003's `hInt`. Deriving them from
  `Section2Assumptions` (which would require a continuity result for
  `circleGapSeries` and for `sigmaZeroMinus`) is the subject of a
  *future* sprint.
- Choosing concrete `ρ₁, ρ₂` (e.g. `ρ₁ = √((1+c²)/2)`, `ρ₂ = (1+c)/2`,
  or any tuned values). The free parameters `ρ₁, ρ₂` must remain a
  `forall` here.
- Closing sprint 004's annulus budget hypothesis from
  `Section2Assumptions`. That requires combining sprint 003's upper
  bound and sprint 006's lower bound into a numerical inequality on
  the closed-form coefficients, which is a *separate* future sprint.
- Pushing `c_value` upward in this sprint — the goal is the structural
  new chain, not a numerical push. Any future sprint that *does* push
  `c` is expected to consume `annulusExcess_lower_bound_of_eq8_eq9`
  alongside `valid_of_eq2_eq3_eq4_annulus_budget` and
  `diskExcess_upper_bound_of_eq2_eq3_eq4` to dominate the budget at
  the new `c`.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
- Refactoring or simplifying sprints 001, 002, 003, 004, or 005. Their
  lemmas are consumed verbatim (sprint 006 only *adds* new theorems).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem with
  a `(2)+(3)+(4)+(8)+(9)`-only proof. That is the strategic payoff of
  the next-after-this sprint, not this one.
- Generalizing `sigmaZeroMinus_nonneg_of_pos` to `ρ ≥ 0` (the `ρ = 0`
  case has `sigmaZeroMinus a b 0 = 0` only conditionally; pinning to
  `0 < ρ` keeps the proof a one-liner).

## Time budget

≤ 90 minutes runtime. The new theorems are conceptually simple but the
proof of theorem (2) has several Mathlib plumbing steps
(`IntervalIntegrable.mono_set`, `annulusSlice_add_adjacent` x 2,
`annulusSlice_nonneg(_of_ae)` x 2, `intervalIntegral.integral_mono_on_of_le_Ioo`,
plus `linarith` chaining); most of the time will be in glue and
type-juggling, not deep mathematics.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- The Generator finds that `IntervalIntegrable.mono_set` requires a
  different shape (e.g. `Set.uIcc` vs `Set.Icc`) than the global
  `IntervalIntegrable … c 1` premise: convert via
  `Set.uIcc_of_le` (using `c ≤ 1` from `c < 1`) or
  `IntervalIntegrable.mono_set'` / `IntervalIntegrable.symm` plus an
  `Icc` rewrite. If no Mathlib lemma directly bridges the two shapes,
  fall back to taking three separate `IntervalIntegrable` premises
  (one for each sub-interval) instead of the single global premise.
  Document the choice in the report.
- The pointwise application of `circleGap_outer_lower_bound_of_eq8_eq9`
  for `ρ ∈ Ioo ρ₁ ρ₂` requires `c < ρ` and `ρ < 1`: derive these from
  `c < ρ₁ ≤ ρ` (by `lt_of_lt_of_le hρ₁ hr.1.le`) and `ρ ≤ ρ₂ < 1`
  (by `lt_of_le_of_lt hr.2.le hρ₂`). If the `Ioo`/`Icc` boundaries
  cause type mismatches, switch to `Ioo ρ₁ ρ₂`'s open form with
  `hr.1`, `hr.2` as strict inequalities and chain with `le_of_lt`.
- The non-negativity discharge of `annulusSlice c ρ₁` and
  `annulusSlice ρ₂ 1` via `circleGap_nonneg_of_eq8_eq9` requires
  `c < ρ` and `ρ < 1` for the pointwise step: handle the boundary
  point `ρ = c` (and `ρ = ρ₁`, `ρ = ρ₂`, `ρ = 1`) via the
  `annulusSlice_nonneg_of_ae` variant — this is the same trick used
  in `Reduction.lean::annulusExcess_nonneg`. If that pattern does
  not transfer cleanly, fall back to taking the non-negativity facts
  as additional explicit premises (acceptable but document it).
- The `annulusSlice_add_adjacent` chain produces an `=` between
  `annulusSlice ρ₁ ρ₂ + annulusSlice c ρ₁ + annulusSlice ρ₂ 1` and
  `annulusSlice c 1` modulo associativity/commutativity; use
  `linarith` or a `have` chain with explicit `add_assoc` /
  `add_comm` rewrites. Any cosmetic `+` reordering should close
  with `linarith` once the three sub-slice equalities are in scope.
- The proof would require `paper.eq{2,3,4,5,6,7,10,11,12,13,14,15}_*`,
  `Korenblum.scalar*`, `valid_of_eq15`, `valid_of_eq12_eq13`,
  `valid_of_eq2_eq3_eq4_annulus_budget`, or any other reduction
  theorem to close: `STATUS=BLOCKED` — that would defeat the
  structural novelty of this sprint and indicates the contract needs
  revision.
- The proof would require a Mathlib lemma not yet in the pinned
  toolchain (e.g. an obscure `IntervalIntegrable.restrict` /
  `Set.uIcc` bridge that has no direct counterpart):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Theorem (1)'s "if `0 ≤ ρ²·x` and `0 < ρ²` then `0 ≤ x`" step does
  not match a single Mathlib lemma name: fall back to
  `nonneg_of_mul_nonneg_left` or `nonneg_of_mul_nonneg_right`
  (depending on argument order), or simply
  `nlinarith [pow_pos hρ 2, hNonneg]`. If Lean rejects all three,
  use `(mul_nonneg_iff_of_pos_left (pow_pos hρ 2)).mp` (note: this
  may be named `mul_nonneg_iff_pos_of_neg` or similar in the pinned
  Mathlib version; try a few variants before giving up).
- Any of acceptance criteria 4, 5, 6, 7, 8, 9, or 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
