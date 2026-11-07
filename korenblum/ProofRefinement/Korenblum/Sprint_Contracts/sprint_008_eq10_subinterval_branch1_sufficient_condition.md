# Sprint 008: Sub-interval branch-1 sufficient condition for `ValidKorenblumBound` from equation `(10)`

**Created**: 2026-05-02 14:30 by Planner
**Parent candidate**: `Candidates/V7.lean`
**Target file**: `Candidates/V8.lean`
**Direction**: section2-proof

## Goal

Ship one *new generic Lean theorem* in `Proof/Reduction.lean` that exposes a
**strictly weaker sufficient condition** than Wang's `(15)` for
`ValidKorenblumBound c`: the existence of any sub-interval
`[ρ₁, ρ₂] ⊆ [c, branchSplit c]` on which the branch-1 kernel mass already
reaches `1`.

```lean
theorem valid_of_eq10_subinterval_branch1
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c
```

The proof must:

1. Unfold `ValidKorenblumBound` via `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
2. Obtain the witness `⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_split, hMass⟩` from
   `h_window paper`.
3. Establish `branchSplit c < 1` (`PaperAxioms.branchSplit c = c · √(4/3)` with
   `c < 1` and `√(4/3) < ?` — actually `√(4/3) ≈ 1.155 > 1`, so the
   branch-split radius might exceed `1` for `c` close enough to `1/√(4/3) ≈
   0.866`. Since the seed `c_value = 0.3554`, this is far from problematic;
   handle it by deriving `branchSplit c < 1` from `c · √(4/3) < 1`. For the
   generic theorem, take `branchSplit c < 1` as an additional hypothesis on
   `valid_of_eq10_subinterval_branch1` — call it `hSplit_lt_one`. This makes
   the theorem statement marginally more general; document that
   `c < √(3/4) ≈ 0.866` suffices.)
4. Apply `paper.eq10_branch1_pointwise` (Wang's printed `(10)`) to obtain
   the pointwise bound
   `branch1PointwiseFactor c (paperLambda K c) ρ · diskExcess ≤ circleGap ρ`
   for `ρ ∈ (c, branchSplit c)`.
5. Multiply by `2 · ρ ≥ 0` pointwise to get
   `2 · ρ · branch1PointwiseFactor c (paperLambda K c) ρ · diskExcess ≤
    2 · ρ · circleGap ρ = annulusDensity paper.circleGap ρ`,
   noting that `2 · ρ · branch1PointwiseFactor c (paperLambda K c) ρ =
   12 · ρ³ · (ρ² - c²) / (c⁶ · paperLambda K c ρ) =
   Korenblum.scalarIntegrand1 c (paperLambda K c) ρ`.
6. Invoke `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound`
   with `mass = 1`, `modeIntegrand = scalarIntegrand1 c (paperLambda K c)`,
   `innerExcess = diskExcess paper.circleGap c`, `[a, b] = [ρ₁, ρ₂]`. The
   premises:
     - `hab := hρ₁₂`,
     - `hMassNonneg := zero_le_one`,
     - `hMass := hMass` (the witness's
       `1 ≤ ∫ ρ in ρ₁..ρ₂, scalarIntegrand1 c (paperLambda K c) ρ`),
     - `hModeInt := WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
         hc_pos hρ₁₂ hcρ₁ (le_trans hρ₂_split hSplit_le_one) paper.eq7_paperK_formula`,
     - `hAnnInt`: integrability of `annulusDensity paper.circleGap = 2ρ · circleGap ρ`
       on `[ρ₁, ρ₂]`. Since this is not directly available from
       `Section2Assumptions`, take it as an *additional explicit hypothesis*
       on `valid_of_eq10_subinterval_branch1` (mirroring the
       `hInt`/`hIntCircle` premises in sprints 003, 005, 006). Document the
       intent: deriving annulus-density integrability from
       `Section2Assumptions` is a separate sprint.
     - `hPointwise`: from step 5 above, applied at each `ρ ∈ Icc ρ₁ ρ₂`
       (handle the boundary `ρ = ρ₁ = c` case carefully — `eq10_branch1_pointwise`
       wants strict `c < ρ`. If `ρ₁ = c`, the LHS at `ρ = c` becomes
       `scalarIntegrand1 c Λ c · diskExcess = 0 · diskExcess = 0 ≤
       2c · circleGap c`, which holds since
       `circleGap c ≥ 0` is provable from
       `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` only for `c < ρ < 1`,
       so handle the boundary via `circleGap c = sigmaPlus c - c² · sigmaZeroMinus c`
       and use `(4)` for non-negativity, **OR** simply require `c < ρ₁` strict
       in the contract (acceptable; the seed has `c_value = 0.3554`, so any
       `ρ₁ > 0.3554` works). **Choose strict `c < ρ₁` to keep the proof
       short.**),
     - `hAnnNonneg`: from `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9`
       applied to `paper`, plus `2ρ ≥ 0`. With `c < ρ₁ ≤ ρ ≤ ρ₂ < 1`, both
       conditions hold; use `annulusDensity_nonneg_of_lt` (private to
       `Reduction.lean`, already available in scope).
7. Conclude `1 · diskExcess paper.circleGap c ≤
   AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂`,
   simplify `1 · _ = _`, then dominate the slice by the full
   `annulusExcess`:
     - split `annulusExcess = annulusSlice c 1` via two
       `AnnulusIntegralReduction.annulusSlice_add_adjacent` calls into
       `annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1`
       (mirroring sprint 006's bookkeeping);
     - discharge `0 ≤ annulusSlice c ρ₁` and `0 ≤ annulusSlice ρ₂ 1` via
       `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae` plus
       `annulusDensity_nonneg_of_lt` (the same a.e. machinery as the
       existing `annulusExcess_nonneg` private lemma in `Reduction.lean`);
     - chain `diskExcess ≤ annulusSlice ρ₁ ρ₂ ≤ annulusExcess` by `linarith`.

   Take `IntervalIntegrable (annulusDensity paper.circleGap) volume c 1` as
   an explicit hypothesis on the new theorem (matching sprint 006's
   `hIntCircle`), so the three sub-slice integrabilities can be derived via
   `mono_set` (again mirroring sprint 006).

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V8.lean` at the same `c = 0.3554` that compiles,
scores `≥ V7`, and *materializes* the new sufficient condition in a side lemma
`v8_valid_of_eq10_subinterval_branch1_chain_compiles` exercised against an
abstract sub-interval / mass / integrability triple (mirroring V4's
`v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles` and V6's
`v6_annulusExcess_lower_bound_chain_compiles` patterns). The sink theorem is
still discharged via `valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprints 002–007 have built a complete `(15)`-free
ladder on the **`(2)+(3)+(4)+(8)+(9)`** axis (inner-disk closed-form upper
bound + outer-annulus closed-form lower bound + end-to-end
`valid_of_eq2_eq3_eq4_annulus_budget` reducer + branch-split single-`Z`
collapse). Sprint 008 opens a **fundamentally different axis** through
`Section2Assumptions` — the **`(10)` pointwise factor route on a
sub-interval of the branch-1 window**.

The novelty is structural and three-fold:

1. **First sufficient condition that uses a strict sub-interval of a
   branch.** Wang's `(15)` integrates `scalarIntegrand1` over the *full*
   `[c, branchSplit c]` and `scalarIntegrand2` over the *full*
   `[branchSplit c, 1]`, then asks the *sum* to be `≥ 1`. The new condition
   asks for the branch-1 integral over **any sub-interval** to be `≥ 1`.
   This is **strictly weaker**: any future numerical or analytical proof of
   the sub-window inequality automatically yields `ValidKorenblumBound c`
   without ever touching branch 2 or the full branch 1. Equivalently: it
   exposes for the first time in the workspace that the kernel does *not*
   need to be integrated over its full natural domain — local concentration
   of mass `≥ 1` suffices.
2. **First reduction that goes through `(10)` rather than `(12)`/`(14)` /
   `(15)`.** Sprints 001 (via `(12)+(13)`), 004 (via `(2)+(3)+(4)`), and
   the seed (via `(15)`) all chain through *integrated* paper inequalities.
   `eq10_branch1_pointwise` is a *pointwise* paper inequality; sprint 008
   integrates it locally on a chosen sub-interval, which is qualitatively
   distinct from integrating `scalarIntegrand1` on the full natural window
   per `(12)`. The Lean call graph for the new theorem hits
   `paper.eq10_branch1_pointwise` directly, with no use of
   `paper.eq12_branch1_integrated`, `paper.eq14_combined`, or
   `paper.eq15_*`. (`paper.eq7_paperK_formula` is consumed only via
   `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`'s
   integrability premise, which is purely measure-theoretic plumbing
   inherited from sprints 003, 005, 006.)
3. **First reduction that exposes a non-trivial degree of freedom — the
   sub-interval choice — at the structural level.** The end-to-end seed
   route via `(15)` is a single inequality at fixed integration limits.
   Sprint 004's `(2)+(3)+(4)` route exposes a free parameter `ρ` but
   only at the *budget hypothesis* side. Sprint 008 exposes two free
   parameters `ρ₁ ≤ ρ₂` directly inside the sufficient condition, which
   gives a downstream sprint two scalar knobs to tune (window center and
   window width) while still preserving structural correctness.

Why this is **not** a numerical push:

- The new theorem's statement is purely structural: it exposes the
  sub-interval `[ρ₁, ρ₂]`, the kernel-mass-`≥`-`1` inequality, and the
  annulus-density integrability as `forall`/explicit hypotheses. No
  numeric bounds are baked in.
- `c_value` stays at `3554/10000`; V8 still discharges the sink theorem
  via `valid_of_eq15` so the score is exactly preserved at `1777/5000`.
- The candidate side lemma is a one-line application of the new theorem
  against an *abstract* window/mass triple (the candidate accepts the
  triple as opaque assumptions and confirms it discharges the contract).

Why this is **bounded enough for one Generator session**:

- The proof body is ~50 lines: unfold `ValidKorenblumBound`, destructure
  the witness, derive positivity of `ρ₁, ρ₂`, feed
  `eq10_branch1_pointwise` and the `2ρ`-rescaling identity into
  `mass_mul_le_annulusSlice_of_integral_bound`, then chain the resulting
  `1 · diskExcess ≤ annulusSlice ρ₁ ρ₂` against the sliceSplit machinery
  to dominate by `annulusExcess`. Every sub-step has a precedent in
  `Reduction.lean` already (sprint 006's `mono_set` chain, the existing
  private `annulusDensity_nonneg_of_lt` and `annulusExcess_nonneg`,
  sprint 003's `mass_mul_le_annulusSlice_of_integral_bound` cousin
  `intervalIntegral.integral_mono_on_of_le_Ioo`).
- The candidate side lemma is one line: invoke
  `valid_of_eq10_subinterval_branch1` against `c_value_pos`,
  `c_value_lt_one`, and the abstract window hypothesis.
- No new Mathlib search beyond what sprint 006 already used.

Why this opens a clear path to a future `c`-pushing sprint without
trust expansion:

- The kernel-mass-`≥`-`1` premise on a sub-interval `[ρ₁, ρ₂]` is the
  *only* outstanding ingredient for an end-to-end `c`-push. A future
  sprint can attack it via:
    (a) a numerical oracle returning a certified lower bound on
        `∫ ρ in ρ₁..ρ₂, scalarIntegrand1 c (paperLambda K c) ρ` for a
        chosen `(c, ρ₁, ρ₂)` triple — this would be the workspace's
        first registered `[[oracles]]` entry, with the Lean-facing
        statement matching exactly the sub-interval kernel mass shape
        of `valid_of_eq10_subinterval_branch1`'s premise;
    (b) a Lean-only numerical proof using `Mathlib`'s
        `intervalIntegral.integral_le_sum` /
        `MeasureTheory.integral_pos_iff_support_of_nonneg_ae` for the
        polynomial-ratio integrand `12ρ³(ρ²-c²)/(c⁶·paperLambda)`;
    (c) a closed-form lower bound on the integral by replacing
        `paperLambda K c ρ ≤ 1` (paperLambda is bounded by `1` on
        the relevant region — see `WangPaperSideConditions.paperLambda_le_one`
        if it exists) with the constant `1`, then computing
        `∫ 12ρ³(ρ²-c²) dρ` in closed form on `[ρ₁, ρ₂]`. If for some
        triple `(c, ρ₁, ρ₂)` with `c > 0.3554` this closed-form lower
        bound exceeds `1`, an immediate `c`-push lands.
- Each route uses only the already-trusted surface plus possibly one
  registered numerical oracle — no new free-floating axiom, no new
  paper equation.

Why this is **not** a numerical-budget push in disguise:

- The sub-interval `[ρ₁, ρ₂]` is exposed as a `forall` inside the
  sufficient condition's witness, not pinned to any concrete pair.
- The kernel-mass `1` lower bound is structural — the same constant
  appears in `(15)`. The new condition does *not* tighten any
  inequality; it relaxes the integration window of an existing
  inequality.
- The Lean theorem is a complete reduction, not a numerical step. The
  numerical work (if any) is deferred to the sprint after this one.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic theorem `valid_of_eq10_subinterval_branch1`
    matching the shape above. The proof must:
      1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
      2. Obtain `⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_split, hMass⟩` from
         `h_window paper`.
      3. Derive `c < ρ₁` strict from `hcρ₁_strict` (rename the contract
         hypothesis to make it strict; see *Note on `c < ρ₁` strictness*
         below). Derive `ρ₂ < 1` from `ρ₂ ≤ branchSplit c` and
         `hSplit_lt_one`. Derive `c ≤ ρ₂` from `c < ρ₁ ≤ ρ₂`.
      4. Establish the pointwise bound on `Set.Icc ρ₁ ρ₂`:
         ```
         scalarIntegrand1 c (paperLambda K c) ρ * diskExcess paper.circleGap c
           ≤ annulusDensity paper.circleGap ρ
         ```
         by:
           - For `ρ ∈ Icc ρ₁ ρ₂`, derive `c < ρ` from `c < ρ₁ ≤ ρ` and
             `ρ < branchSplit c` from `ρ ≤ ρ₂ ≤ branchSplit c`. (If
             `ρ = ρ₂ = branchSplit c`, the strict inequality
             `ρ < branchSplit c` of `eq10_branch1_pointwise` fails.
             Handle via `annulusSlice_nonneg_of_ae` + integrand bound on
             `Ioo ρ₁ ρ₂` instead — see *Stop conditions* below.)
           - Apply `paper.eq10_branch1_pointwise hcρ hρ_split` to get
             `branch1PointwiseFactor c (paperLambda K c) ρ * diskExcess ≤
              circleGap ρ`.
           - Multiply both sides by `2ρ ≥ 0` (from `0 < c < ρ`) via
             `mul_le_mul_of_nonneg_left`.
           - Algebraically rewrite the LHS using
             `scalarIntegrand1 c Λ ρ = 2ρ · branch1PointwiseFactor c Λ ρ`
             via `unfold Korenblum.scalarIntegrand1
             PaperAxioms.branch1PointwiseFactor` + `field_simp` + `ring`.
           - The RHS becomes `2ρ · circleGap ρ = annulusDensity ρ` via
             `unfold AnnulusIntegralReduction.annulusDensity` (or `change`).
      5. Establish integrability of `scalarIntegrand1 c (paperLambda K c)` on
         `[ρ₁, ρ₂]` via
         `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
            hc_pos hρ₁₂ hcρ₁.le (le_trans hρ₂_split hSplit_le_one)
            paper.eq7_paperK_formula`.
      6. Establish integrability of `annulusDensity paper.circleGap` on
         `[ρ₁, ρ₂]` via `mono_set` from the explicit
         `IntervalIntegrable (annulusDensity paper.circleGap) volume c 1`
         premise (mirroring sprint 006's `hIntCircle.mono_set huIcc_ρ₁ρ₂`).
      7. Apply
         `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound`
         with `mass = 1`, `modeIntegrand = scalarIntegrand1 c (paperLambda K c)`,
         `innerExcess = diskExcess paper.circleGap c`, to conclude
         `1 · diskExcess paper.circleGap c ≤
            annulusSlice paper.circleGap ρ₁ ρ₂`.
         Discharge `hAnnNonneg` via the existing private
         `annulusDensity_nonneg_of_lt` lemma (already in scope in
         `Reduction.lean`), evaluated at each `ρ ∈ Icc ρ₁ ρ₂`. (The
         strict-inequality form of `annulusDensity_nonneg_of_lt` requires
         `c < ρ < 1`; for `ρ ∈ Icc ρ₁ ρ₂` with `c < ρ₁` strict and
         `ρ ≤ ρ₂ ≤ branchSplit c < 1`, the boundary case is `ρ = ρ₁` or
         `ρ = ρ₂`. Both satisfy `c < ρ₁ ≤ ρ` and `ρ ≤ ρ₂ < 1`, so
         non-strictness on the upper boundary is fine — but
         `annulusDensity_nonneg_of_lt` takes strict `c < ρ` and `ρ < 1`,
         so for `ρ = ρ₁` we have `c < ρ₁ = ρ` and `ρ ≤ ρ₂ < 1`, and for
         `ρ = ρ₂` we have `c < ρ₁ ≤ ρ₂ = ρ` and `ρ ≤ ρ₂ < 1`. All four
         strict inequalities hold, so the pointwise (not a.e.) form
         suffices. If type juggling makes this awkward, fall back to the
         a.e. version `mass_mul_le_annulusSlice_of_integral_bound_ae`
         and the `Ioo`-style a.e. discharge from the existing
         `annulusExcess_nonneg` proof.)
      8. Simplify `1 · diskExcess … = diskExcess …` via `one_mul`.
      9. Split `annulusExcess = annulusSlice c 1 = annulusSlice c ρ₁ +
         annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1` via two applications of
         `AnnulusIntegralReduction.annulusSlice_add_adjacent` (mirroring
         sprint 006). Discharge the three sub-interval integrabilities
         via `mono_set` from the global premise (same as sprint 006).
     10. Discharge `0 ≤ annulusSlice c ρ₁` and `0 ≤ annulusSlice ρ₂ 1`
         via `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae` +
         `annulusDensity_nonneg_of_lt` on the open interior (same a.e.
         pattern as sprint 006's `hSlice_cρ₁_nonneg` and
         `hSlice_ρ₂1_nonneg`).
     11. Chain
         `diskExcess paper.circleGap c ≤ annulusSlice ρ₁ ρ₂ ≤ annulusSlice c 1
            = annulusExcess paper.circleGap c`
         by `linarith` over the slice equalities and non-negativities.

  - The new theorem's body must NOT mention `paper.eq{2,3,4,5,6,7,8,9}_*`
    (note: `paper.eq7_paperK_formula` *is* allowed because it is consumed
    via `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
    only as the `hPaperK` integrability premise, which is measure-theoretic
    plumbing — the *analytical content* of the new chain comes from
    `eq10_branch1_pointwise` exclusively), `paper.eq11_branch2_pointwise`,
    `paper.eq12_branch1_integrated`, `paper.eq13_branch2_integrated`,
    `paper.eq14_combined`, `paper.eq15_*`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand2` (only
    `scalarIntegrand1` is allowed; the new condition is branch-1 only),
    `valid_of_eq15`, `valid_of_eq12_eq13`,
    `valid_of_eq2_eq3_eq4_annulus_budget`,
    `eq15_implies_disk_le_annulus`,
    `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
    `circleGap_outer_lower_bound_of_eq8_eq9`,
    `annulusExcess_lower_bound_of_eq8_eq9`,
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    `sigmaZeroMinus_nonneg_of_pos`. The only existing-workspace
    machinery the new theorem may invoke is the
    `annulusDensity_nonneg_of_lt` private helper (which itself uses
    `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9`); allowing this is
    consistent with `(8)+(9)` being the canonical source of
    `circleGap ≥ 0` on `(c, 1)` — without it the boundary
    integrability becomes much harder.

  - Add a one-line module-doc comment above the new theorem explaining:
    sprint 008 is the **first sub-interval branch-1 sufficient condition**
    for `ValidKorenblumBound`, derived from Wang's pointwise `(10)` by
    integrating against `2ρ` over a free sub-interval
    `[ρ₁, ρ₂] ⊆ (c, branchSplit c]` and asking the resulting kernel mass
    to reach `1`. This is **strictly weaker** than `(15)` (which asks the
    same integrand to integrate to `1` over the *full* branch window plus
    the branch-2 contribution), and exposes for the first time in the
    workspace that local concentration of branch-1 mass suffices.

- `ProofRefinement/Korenblum/Candidates/V8.lean`:
  - `-- @parent V7`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3/V4/V5/V6/V7).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly
    as in V1/V2/V3/V4/V5/V6/V7; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does
    not regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v8_valid_of_eq10_subinterval_branch1_chain_compiles
        (hSplit_lt_one : PaperAxioms.branchSplit c_value < 1)
        (hIntDensity :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            IntervalIntegrable
              (AnnulusIntegralReduction.annulusDensity paper.circleGap)
              volume c_value 1)
        (h_window :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value ∧
                (1 : ℝ) ≤
                  ∫ ρ in ρ₁..ρ₂,
                    Korenblum.scalarIntegrand1 c_value
                      (WangOuter.paperLambda K c_value) ρ) :
        ValidKorenblumBound c_value :=
      valid_of_eq10_subinterval_branch1
        c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window
    ```

    so the new sufficient condition is exercised at the seed `c_value`
    against abstract window/mass/integrability premises, but the sink
    theorem is still discharged via `valid_of_eq15`. The side lemma must
    NOT be `axiom`-ed and must NOT call the seed axiom. It exists purely
    to verify that the new reduction chain typechecks at the seed
    `c_value`.

  - Additionally, prove a tiny numeric witness lemma confirming that
    `branchSplit c_value < 1` at the seed:

    ```lean
    theorem v8_split_lt_one_at_seed :
        PaperAxioms.branchSplit c_value < 1 := by
      unfold PaperAxioms.branchSplit
      have h : Real.sqrt (4 / 3) < 3 := by
        have h43 : (4 / 3 : ℝ) < 9 := by norm_num
        nlinarith [Real.sq_sqrt (by norm_num : (4 / 3 : ℝ) ≥ 0),
                   Real.sqrt_nonneg (4 / 3 : ℝ)]
      have hcv : c_value < 1 / 3 := by norm_num [c_value]
      nlinarith [Real.sqrt_nonneg (4 / 3 : ℝ), h, hcv, c_value_pos]
    ```

    (Sanity check: `c_value = 0.3554`, `√(4/3) ≈ 1.1547`, so
    `branchSplit c_value ≈ 0.4104 < 1`. The witness lemma is local to V8
    and is not used elsewhere — its purpose is to demonstrate that the
    `hSplit_lt_one` hypothesis of the new theorem is non-vacuous at the
    seed `c_value`. If the manual `nlinarith` proof above is brittle,
    fall back to a `Real.sqrt_lt_sqrt`-style chain or a direct
    numerical bound `√(4/3) ≤ 12/10` proved via squaring.)

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V7.lean`.

### Note on `c < ρ₁` strictness

The contract above (and the side lemma in V8) uses `c < ρ₁` *strict*
rather than `c ≤ ρ₁`. The reason is that
`paper.eq10_branch1_pointwise` requires the strict hypothesis `c < ρ`
on each application point. For `ρ = ρ₁ = c`, one would have to show
`scalarIntegrand1 c Λ c · diskExcess ≤ 2c · circleGap c` with no
direct paper-side support. The boundary-trivialization route via
`scalarIntegrand1 c Λ c = 12·c³·0/(c⁶·Λ(c)) = 0` algebraically resolves
the LHS to `0`, after which `0 ≤ 2c · circleGap c` would need a
non-negativity fact about `circleGap c` — which is NOT directly
available from `Section2Assumptions` (only on the open interval
`(c, 1)`). Insisting on strict `c < ρ₁` sidesteps the entire boundary
question, costs one bit of generality, and keeps the proof body short.
A future sprint that wants to push to `ρ₁ = c` exactly can derive the
boundary non-negativity via `(3)` + `(4)` and add it as a side lemma.

## Acceptance criteria

1. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V8.lean` succeeds.
2. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V8.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V8 scores `≥` V7 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V8.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'valid_of_eq10_subinterval_branch1' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains a use of `paper.eq10_branch1_pointwise`, a use of
   `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound`
   (or its `_ae` variant), and a use of
   `AnnulusIntegralReduction.annulusSlice_add_adjacent`.
6. `grep -n 'valid_of_eq10_subinterval_branch1' korenblum/ProofRefinement/Korenblum/Candidates/V8.lean`
   returns at least one match (V8 actually invokes the new reduction in
   its body, inside `v8_valid_of_eq10_subinterval_branch1_chain_compiles`).
7. The body of `valid_of_eq10_subinterval_branch1` does NOT mention
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
   `paper.eq8_`, `paper.eq9_`, `paper.eq11_`, `paper.eq12_`,
   `paper.eq13_`, `paper.eq14_combined`, `paper.eq15_`,
   `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand2`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`,
   `eq15_implies_disk_le_annulus`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   `sigmaZeroMinus_nonneg_of_pos`. (Verify with `grep -nE` against the
   substring of the theorem body. `paper.eq7_paperK_formula` MAY appear
   exactly once, only as the `hPaperK` premise of the integrability
   call into `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`.)
8. `grep -n 'paper.eq10_branch1_pointwise' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes `eq10` at least once (i.e. there is
   at least one match inside `valid_of_eq10_subinterval_branch1`'s body).
9. `grep -n 'v8_split_lt_one_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V8.lean`
   returns exactly one definition site (the small numeric witness lemma
   confirming `branchSplit c_value < 1` at the seed).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, `Candidates/V4.lean`, `Candidates/V5.lean`,
  `Candidates/V6.lean`, `Candidates/V7.lean`, or any file in
  `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
- Discharging the `IntervalIntegrable (annulusDensity paper.circleGap)
  volume c 1` premise from `Section2Assumptions`. The integrability
  hypothesis is intentionally taken as an explicit premise, mirroring
  sprints 003, 005, 006. Deriving it from `Section2Assumptions` (which
  would require a continuity/measurability result for `circleGap`) is
  the subject of a *future* sprint.
- Discharging the kernel-mass `1 ≤ ∫ ρ in ρ₁..ρ₂, scalarIntegrand1 …`
  premise itself. That is the explicit subject of a future sprint
  (numerical or analytical; see "Why" section, paragraph on future
  `c`-pushing routes).
- Choosing a concrete `(ρ₁, ρ₂)` pair (e.g. `[c + ε, branchSplit c]` or
  `[c + ε, c + δ]` for specific `ε, δ`). The free parameters `ρ₁, ρ₂`
  must remain `forall`-quantified inside the window hypothesis — sprint
  008 should not commit to any particular sub-interval policy.
- Adding a *symmetric* branch-2 version
  `valid_of_eq11_subinterval_branch2`. That is a clean follow-up sprint
  but should be queued separately to keep this sprint single-axis.
  (Hybrid `(10) ∨ (11)` "either branch suffices on a sub-interval" is
  also out of scope here; the cleanest first move is branch-1 alone.)
- Pushing `c_value` upward in this sprint — the goal is the structural
  new chain, not a numerical push. Any future sprint that *does* push
  `c` is expected to consume `valid_of_eq10_subinterval_branch1` by
  proving the kernel-mass premise at the new `c`.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
- Refactoring or simplifying sprints 001–007. Their lemmas are consumed
  verbatim (sprint 008 only *adds* one new theorem and one V8 candidate).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem with
  a proof via `valid_of_eq10_subinterval_branch1`. That requires
  proving the kernel-mass premise at the seed `c_value`, which is the
  subject of a future numerical sprint.
- Generalising the branch1 hypothesis `ρ₂ ≤ branchSplit c` to allow
  `ρ₂` slightly above `branchSplit c` (which would require chaining
  with `eq11`). Strictly branch-1 in this sprint.
- Removing the explicit `IntervalIntegrable (annulusDensity
  paper.circleGap) volume c 1` premise. The whole point of taking it
  as an explicit hypothesis is to keep this sprint independent of any
  future continuity/measurability work on `circleGap`.

## Time budget

≤ 60 minutes runtime. The new theorem is ~50–70 lines: most of the work
is the boundary-juggling in step 4 (the `Icc ρ₁ ρ₂` vs `Ioo ρ₁ ρ₂`
shape question for `eq10`'s strict-inequality requirement) and the
sub-slice non-negativity bookkeeping in steps 9–10 (which is fully
template-able from sprint 006's `hSlice_cρ₁_nonneg` /
`hSlice_ρ₂1_nonneg` pattern). The
`mass_mul_le_annulusSlice_of_integral_bound` invocation is one line
once the premises are assembled. The candidate side lemma is one line.
The numeric witness lemma is ~5 lines.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- The pointwise bound on `Icc ρ₁ ρ₂` cannot be discharged at the
  endpoint `ρ = ρ₂` because `eq10_branch1_pointwise`'s strict-inequality
  hypothesis `ρ < branchSplit c` fails (i.e. the contract chose
  `ρ₂ ≤ branchSplit c` non-strict and `ρ₂ = branchSplit c` is the
  worst case): switch to the a.e. variant
  `mass_mul_le_annulusSlice_of_integral_bound_ae` and discharge
  `hPointwise` on `Ioo ρ₁ ρ₂` only (the boundary endpoints are
  measure-zero so the a.e. statement on `Icc` follows from the pointwise
  statement on `Ioo`, mirroring `annulusExcess_nonneg`'s
  `Ioo_ae_eq_Icc` rewrite). Document this choice in the report.
- The algebraic identity
  `2 * ρ * branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ`
  fails to close with one `field_simp` + `ring` because of how
  `paperLambda` is opaque: introduce an auxiliary `set Λρ := paperLambda K c ρ`
  and a hypothesis `hΛρ_pos : 0 < Λρ` from
  `WangPaperSideConditions.paperLambda_pos`, then expand both sides via
  `unfold` and apply `field_simp [ne_of_gt hΛρ_pos, ne_of_gt (pow_pos hc_pos 6)]`
  followed by `ring`. If `unfold` does not produce the right shape, use
  `show` to display the target shape and then `field_simp`.
- The `mass_mul_le_annulusSlice_of_integral_bound` call rejects the
  premise shape because of `Icc` vs `uIcc` mismatches in
  `IntervalIntegrable.mono_set`: chain with
  `Set.uIcc_of_le hρ₁₂` and `Set.uIcc_of_le hc_le_one` exactly as in
  sprint 006's `huIcc_ρ₁ρ₂` derivation. If the `mono_set` form does
  not match, take three separate `IntervalIntegrable` premises
  (one for each sub-interval `[c, ρ₁]`, `[ρ₁, ρ₂]`, `[ρ₂, 1]`) on
  the new theorem instead of the single global premise. Document the
  choice in the report.
- The numeric witness lemma `v8_split_lt_one_at_seed` fails to close
  with `nlinarith`: try the explicit numeric bound `√(4/3) ≤ 6/5` (via
  `nlinarith [Real.sq_sqrt (by norm_num : (4/3 : ℝ) ≥ 0)]` and
  `(6/5)^2 = 36/25 = 1.44 ≥ 4/3`), then conclude
  `c_value · √(4/3) ≤ 0.3554 · 1.2 = 0.42648 < 1` by `nlinarith`. If
  that still fails, fall back to taking `hSplit_lt_one` as an
  un-discharged hypothesis on `v8_valid_of_eq10_subinterval_branch1_chain_compiles`
  and *not* providing a witness lemma — flag this as a partial
  discharge in the report.
- The proof would require `paper.eq{2,3,4,5,6,8,9,11,12,13,14,15}_*`,
  `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand2`,
  `valid_of_eq15`, `valid_of_eq12_eq13`,
  `valid_of_eq2_eq3_eq4_annulus_budget`,
  `eq15_implies_disk_le_annulus`,
  `circleGap_inner_bound_of_eq2_eq3_eq4`,
  `diskExcess_upper_bound_of_eq2_eq3_eq4`,
  `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
  `circleGap_outer_lower_bound_of_eq8_eq9`,
  `annulusExcess_lower_bound_of_eq8_eq9`,
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, or
  `sigmaZeroMinus_nonneg_of_pos` directly: `STATUS=BLOCKED` — that
  would defeat the structural novelty of this sprint and indicates the
  contract needs revision. (`paper.eq7_paperK_formula` and
  `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` MAY be referenced —
  the former is consumed only as an integrability premise plumbing
  hook, the latter is the canonical source of `circleGap ≥ 0` on
  `(c, 1)` and is required for the sub-slice non-negativity discharge.)
- The proof would require a Mathlib lemma not yet in the pinned
  toolchain (e.g. an exotic `IntervalIntegrable` bridge):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Any of acceptance criteria 4, 5, 6, 7, 8, or 9 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
