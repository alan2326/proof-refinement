-- Sprint 097: hoisted from `Candidates/V63/Integrability.lean`
-- (originally Sprint 080, Phase A) for shared reuse across V63-V68
-- and any future candidate that needs the parametric `IntervalIntegrable`
-- of `ModeBridge.scalarIntegrand` (and its two-window consolidation
-- shape).
--
-- The hoist is structural and score-neutral: the file's mathematical
-- content (two `theorem`s, no `axiom`s, no `sorry`s) is preserved
-- byte-for-byte modulo namespace and import-line rewrites. The trust
-- surface is unchanged conjunct-for-conjunct: the module remains
-- paper-axiom-free, drawing only on
-- `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`,
-- `KorenblumPaper.PaperAxioms`, `KorenblumPaper.OneModePaperBridge`,
-- all pinned in `lemma.toml:[workspace_import_policy]`. The original
-- V63 per-candidate file at `Candidates/V63/Integrability.lean` is
-- reduced to a thin re-export shim under the same per-candidate
-- namespace `ProofRefinement.Korenblum.Candidates.V63.Integrability`,
-- which preserves backward compatibility for V63's existing imports.
--
-- This file ships two target theorems (no `axiom`s, no `sorry`s):
--
--   1. `modeScalarIntegrand_intervalIntegrable`: for `j ≥ 1`, `0 < c`,
--      and `[a, b] ⊆ [c, 1]`,
--
--      `IntervalIntegrable
--         (fun ρ => ModeBridge.scalarIntegrand c j (paperLambda K c) ρ)
--         volume a b`.
--
--      The proof models on
--      `KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`
--      (which handles the j = 1 case for the existing
--      `Korenblum.scalarIntegrand2` shape `4 ρ³ / (c⁴ Λ)`); the present
--      theorem generalises to arbitrary `j ≥ 1` against the
--      `ModeBridge.scalarIntegrand` shape, equal to
--      `(2 (j+1) / j) ρ^(2j+1) / (c^(2j+2) Λ)` away from `ρ = 0` by
--      `ModeBridge.scalarIntegrand_eq`.
--
--   2. `mode_two_and_one_scalarIntegrand_intervalIntegrable`: the
--      consolidation theorem packaging `modeScalarIntegrand_intervalIntegrable`
--      at `j = 2` on `[ρStart₁, ρStop₁]` and at `j = 1` on
--      `[ρStart₂, ρStop₂]`, in the exact `(j₁, j₂) = (2, 1)` shape
--      sprint 079's wrapper pins.
--
-- ### Hypothesis envelope
--
-- The proofs draw only on:
--
--   * `KorenblumPaper.WangPaperSideConditions.paperLambda_aemeasurableOn_Icc`
--     and `paperLambda_ge_half`, `paperLambda_pos` — the bundled
--     `paperLambda` measurability/positivity package,
--   * `KorenblumPaper.ModeBridge.scalarIntegrand` and
--     `OneModeKernel.term`, `OneModeKernel.weight` definitions,
--   * Mathlib's measure-theory + `IntegrableOn.of_bound` API plus
--     ordinary algebraic manipulation.
--
-- No new `axiom`s. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Proof.Integrability`, which is allowed by
-- the existing `[workspace_import_policy]`
-- `ProofRefinement.Korenblum.*` prefix entry; the candidate-side
-- `[import_policy].allowed_prefixes` already covers the hoisted path
-- via `ProofRefinement.Korenblum.Proof`.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import KorenblumPaper.PaperAxioms
import KorenblumPaper.OneModePaperBridge

open scoped BigOperators Topology
open Filter Finset MeasureTheory Set

noncomputable section

namespace ProofRefinement.Korenblum.Proof.Integrability

open KorenblumPaper

/-- Sprint 080 / Phase A — the general-`j` analogue of
`paperScalarIntegrand2_intervalIntegrable`.

For `j ≥ 1`, `0 < c`, and `[a, b] ⊆ [c, 1]`,

  `IntervalIntegrable
     (fun ρ => ModeBridge.scalarIntegrand c j (paperLambda K c) ρ)
     volume a b`.

The proof:

  1. Reduce to `IntegrableOn _ (Icc a b) volume` via
     `intervalIntegrable_iff_integrableOn_Icc_of_le hab`.
  2. Apply `IntegrableOn.of_bound` with the explicit constant
     `4 * (j + 1) / (j * c ^ (2j + 2))`. Finite measure of `Icc a b`
     follows from `measure_Icc_lt_top`.
  3. AE-strong measurability: rewrite `scalarIntegrand` against
     `OneModeKernel.term`'s definition and use `paperLambda`'s
     `aemeasurableOn_Icc` from the bundled side-conditions module
     plus `aemeasurable_id.pow_const`.
  4. Pointwise bound: on `Icc a b ⊆ Icc c 1` use
     `ModeBridge.scalarIntegrand_eq` to rewrite the integrand as
     `((2(j+1)/j) ρ^(2j+1)) / (c^(2j+2) Λ)`, then bound numerator by
     `(2(j+1)/j) · 1 = 2(j+1)/j` (using `ρ^(2j+1) ≤ 1`) and
     `1/Λ ≤ 2` (from `paperLambda_ge_half`). The final bound is
     `4(j+1) / (j · c^(2j+2))`. -/
theorem modeScalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ} {j : ℕ}
    (hj : 1 ≤ j)
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let μ := volume.restrict (Icc a b)
  have hjPos : 0 < j := hj
  have hjR_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjPos
  have hjR_ne : (j : ℝ) ≠ 0 := ne_of_gt hjR_pos
  have hjp1R_pos : (0 : ℝ) < ((j : ℝ) + 1) := by linarith
  have hcPow_pos : (0 : ℝ) < c ^ (2 * j + 2) := by positivity
  have hcPow_ne : (c ^ (2 * j + 2) : ℝ) ≠ 0 := ne_of_gt hcPow_pos
  -- Constant bound: 4 * (j + 1) / (j * c^(2j+2)).
  set M : ℝ := 4 * ((j : ℝ) + 1) / ((j : ℝ) * c ^ (2 * j + 2)) with hMdef
  have hMnonneg : 0 ≤ M := by
    have hDen_pos : 0 < (j : ℝ) * c ^ (2 * j + 2) := by positivity
    have hNum_nonneg : 0 ≤ 4 * ((j : ℝ) + 1) := by positivity
    exact div_nonneg hNum_nonneg hDen_pos.le
  -- AE-measurability of paperLambda K c on Icc a b.
  have hΛmeas : AEMeasurable (fun ρ => WangOuter.paperLambda K c ρ) μ :=
    WangPaperSideConditions.paperLambda_aemeasurableOn_Icc hca hb1 hPaperK
  -- AE-strong measurability of the integrand.
  have hMeas :
      AEStronglyMeasurable
        (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) μ := by
    have hAE :
        AEMeasurable
          (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) μ := by
      -- scalarIntegrand c j Λ ρ = 2 ρ / (term c ρ j * Λ ρ)
      -- term c ρ j = weight c j / ρ^(2j)
      have h2ρ : AEMeasurable (fun ρ : ℝ => (2 : ℝ) * ρ) μ := by
        exact (measurable_const.mul measurable_id).aemeasurable
      have hρpow : AEMeasurable (fun ρ : ℝ => ρ ^ (2 * j)) μ :=
        measurable_id.aemeasurable.pow_const _
      have hWeight :
          AEMeasurable
            (fun _ : ℝ => OneModeKernel.weight c j) μ :=
        aemeasurable_const
      have hTerm :
          AEMeasurable
            (fun ρ : ℝ => OneModeKernel.term c ρ j) μ := by
        unfold OneModeKernel.term
        exact hWeight.div hρpow
      have hDen :
          AEMeasurable
            (fun ρ : ℝ => OneModeKernel.term c ρ j *
              WangOuter.paperLambda K c ρ) μ :=
        hTerm.mul hΛmeas
      unfold ModeBridge.scalarIntegrand
      exact h2ρ.div hDen
    exact hAE.aestronglyMeasurable
  refine IntegrableOn.of_bound ?_ hMeas M ?_
  · simpa using (measure_Icc_lt_top (μ := volume) (a := a) (b := b))
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ fun ρ hρ => ?_
    -- Pointwise bounds.
    have hcρ : c ≤ ρ := le_trans hca hρ.1
    have hρnonneg : 0 ≤ ρ := le_trans hc.le hcρ
    have hρpos : 0 < ρ := lt_of_lt_of_le hc hcρ
    have hρne : ρ ≠ 0 := ne_of_gt hρpos
    have hρle1 : ρ ≤ 1 := le_trans hρ.2 hb1
    -- ρ^(2j+1) ≤ 1.
    have hρpow_nonneg : 0 ≤ ρ ^ (2 * j + 1) := by positivity
    have hρpow_le_one : ρ ^ (2 * j + 1) ≤ 1 := by
      exact pow_le_one₀ hρnonneg hρle1
    -- Λ ≥ 1/2 ⇒ 1/Λ ≤ 2.
    have hΛhalf : (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_ge_half (K := K) (c := c) (ρ := ρ)
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
    -- Rewrite scalarIntegrand via scalarIntegrand_eq.
    have hRewrite :
        ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ =
          ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1) /
            (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) :=
      ModeBridge.scalarIntegrand_eq c hjPos
        (WangOuter.paperLambda K c) hc hρne hΛne
    -- Numerator non-negativity.
    have hCoef_pos : 0 < (2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ) := by
      have : 0 < (2 : ℝ) * ((j : ℝ) + 1) := by linarith
      exact div_pos this hjR_pos
    have hCoef_nonneg : 0 ≤ (2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ) := hCoef_pos.le
    have hNum_nonneg :
        0 ≤ ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1) := by
      exact mul_nonneg hCoef_nonneg hρpow_nonneg
    -- Denominator positivity.
    have hDen_pos :
        0 < c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ := by
      exact mul_pos hcPow_pos hΛpos
    -- Bound on the rewritten integrand.
    have hCoefρ_le :
        ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1) ≤
          (2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ) := by
      calc
        ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1)
            ≤ ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * 1 := by
              exact mul_le_mul_of_nonneg_left hρpow_le_one hCoef_nonneg
        _ = (2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ) := by ring
    -- Now bound the full integrand.
    -- Goal: ‖scalarIntegrand‖ ≤ M.
    -- ‖scalarIntegrand‖ = scalarIntegrand (since non-negative).
    have hSI_nonneg :
        0 ≤ ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
      rw [hRewrite]
      exact div_nonneg hNum_nonneg hDen_pos.le
    -- Bound using division properties.
    -- We bound ((2(j+1)/j) * ρ^(2j+1)) / (c^(2j+2) * Λ) ≤ M
    -- = 4(j+1)/(j c^(2j+2)) by:
    --   numerator ≤ 2(j+1)/j (above),
    --   1/Λ ≤ 2,
    -- giving the overall bound 2 · (2(j+1)/j) / c^(2j+2) = 4(j+1)/(j c^(2j+2)).
    calc
      ‖ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ‖
          = ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hSI_nonneg]
      _ = ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1) /
            (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) := hRewrite
      _ ≤ M := by
          -- Standard div-le-div / clearing-denominators argument.
          rw [div_le_iff₀ hDen_pos]
          have hLHS :
              ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1) ≤
                M * (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) := by
            -- M · (c^(2j+2) · Λ) = 4(j+1)/j · Λ ≥ 4(j+1)/j · (1/2) = 2(j+1)/j.
            have hMulEq :
                M * (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) =
                  (4 * ((j : ℝ) + 1) / (j : ℝ)) *
                    WangOuter.paperLambda K c ρ := by
              have : M * (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) =
                  (4 * ((j : ℝ) + 1)) /
                    ((j : ℝ) * c ^ (2 * j + 2)) *
                    (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) := by
                rw [hMdef]
              rw [this]
              field_simp
            rw [hMulEq]
            -- numerator ≤ 2(j+1)/j ≤ 2 · (2(j+1)/j) · Λ ≤ 4(j+1)/j · Λ.
            have hRHS_nonneg :
                0 ≤ (4 * ((j : ℝ) + 1) / (j : ℝ)) := by
              have : 0 ≤ 4 * ((j : ℝ) + 1) := by linarith
              exact div_nonneg this hjR_pos.le
            have hΛ_ge : (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ := hΛhalf
            have hCoef4_eq :
                (4 * ((j : ℝ) + 1) / (j : ℝ)) =
                  2 * ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) := by
              field_simp
              ring
            calc
              ((2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ)) * ρ ^ (2 * j + 1)
                  ≤ (2 : ℝ) * ((j : ℝ) + 1) / (j : ℝ) := hCoefρ_le
              _ = (4 * ((j : ℝ) + 1) / (j : ℝ)) * (1 / 2) := by
                    rw [hCoef4_eq]; ring
              _ ≤ (4 * ((j : ℝ) + 1) / (j : ℝ)) *
                    WangOuter.paperLambda K c ρ := by
                    exact mul_le_mul_of_nonneg_left hΛ_ge hRHS_nonneg
          exact hLHS

/-- Sprint 080 / Phase A — consolidation theorem packaging
`modeScalarIntegrand_intervalIntegrable` at `j₁ = 2` on `[ρStart₁, ρStop₁]`
and at `j₂ = 1` on `[ρStart₂, ρStop₂]`, in the exact `(j₁, j₂) = (2, 1)`
shape sprint 079's wrapper pins.

Two direct invocations of `modeScalarIntegrand_intervalIntegrable` at
`j = 2` and `j = 1`. Provides the two integrability hypotheses required
by the `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's
`h_witness` predicate as a single consumable theorem. -/
theorem mode_two_and_one_scalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ}
    (hc : 0 < c)
    (hcStart₁ : c ≤ ρStart₁)
    (hStart₁LeStop₁ : ρStart₁ ≤ ρStop₁)
    (hStart₂LeStop₂ : ρStart₂ ≤ ρStop₂)
    (hStop₁_le_Start₂ : ρStop₁ ≤ ρStart₂)
    (hStop₂_le_one : ρStop₂ ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 2 (WangOuter.paperLambda K c) ρ)
      volume ρStart₁ ρStop₁ ∧
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 1 (WangOuter.paperLambda K c) ρ)
      volume ρStart₂ ρStop₂ := by
  have hStop₁_le_one : ρStop₁ ≤ 1 :=
    le_trans hStop₁_le_Start₂ (le_trans hStart₂LeStop₂ hStop₂_le_one)
  have hcStart₂ : c ≤ ρStart₂ :=
    le_trans (le_trans hcStart₁ hStart₁LeStop₁) hStop₁_le_Start₂
  refine ⟨?_, ?_⟩
  · -- j = 2 window [ρStart₁, ρStop₁].
    exact modeScalarIntegrand_intervalIntegrable
      (j := 2) (by decide) hc hStart₁LeStop₁ hcStart₁ hStop₁_le_one hPaperK
  · -- j = 1 window [ρStart₂, ρStop₂].
    exact modeScalarIntegrand_intervalIntegrable
      (j := 1) (le_refl 1) hc hStart₂LeStop₂ hcStart₂ hStop₂_le_one hPaperK

end ProofRefinement.Korenblum.Proof.Integrability
