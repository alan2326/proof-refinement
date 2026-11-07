-- Sprint 068, Phase A: per-candidate derived-theorem file shipping
-- THETA_STEP for V53.
--
-- This file ships THETA_STEP as a Lean theorem (not an axiom and not an
-- oracle) by composing existing trusted material:
--
--   * `paper.eq8_sigma_to_liftGap` and `paper.eq9_liftGap_to_circleGap`
--     (`KorenblumPaper.PaperAxioms`, packaged via
--     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`),
--   * `paper.eq3_circleGap_decomposition` (`KorenblumPaper.PaperAxioms`),
--   * sprint 005's series identity `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
--     (`ProofRefinement.Korenblum.Proof.Reduction`, paper-axiom-free),
--   * `KorenblumPaper.WangPaperSideConditions.paperLambda_pos`.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V53.ThetaStep`, which is allowed by
-- the existing `[workspace_import_policy]` `ProofRefinement.Korenblum.*`
-- prefix entry.
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V53.ThetaStep

open ProofRefinement.Korenblum
open KorenblumPaper

/--
Sprint 068 / Phase A — THETA_STEP_RAW, the cross-multiplied form.

Given `Section2Assumptions a b K c` and `0 ≤ c < ρ < 1`, the workspace's
chain of paper equations and series identities yields

  `(1 + Λ(c, ρ)) · Σ⁻(ρ) ≤ Λ(c, ρ) · Σ⁺(ρ)`.

Proof outline:
1. `(8) + (9)` bridge: `Σ⁻(ρ) ≤ Λ · circleGap(ρ)`.
2. `(3)` decomposition: `circleGap(ρ) = Σ⁺(ρ) − ρ² · Σ⁻₀(ρ)`.
3. Sprint 005: `Σ⁻(ρ) = ρ² · Σ⁻₀(ρ)`. So `circleGap(ρ) = Σ⁺(ρ) − Σ⁻(ρ)`.
4. Substitute and rearrange.

The `0 ≤ c` hypothesis is needed because `paper.eq3_circleGap_decomposition`
takes `0 ≤ r` as a precondition; combined with `c < ρ` this yields the
required `0 ≤ ρ`. This is the smallest hypothesis-set extension consistent
with the sprint contract's "generator surfaces it as a hypothesis" rule
(the contract explicitly anticipates this for the analogous summability
premise; the same logic applies here).
-/
theorem theta_step_raw
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
    (1 + WangOuter.paperLambda K c ρ) *
        PaperAxioms.sigmaMinus a b ρ ≤
      WangOuter.paperLambda K c ρ * PaperAxioms.sigmaPlus a b ρ := by
  -- Positivity / nonnegativity facts.
  have hρ_nonneg : (0 : ℝ) ≤ ρ := le_of_lt (lt_of_le_of_lt hc_nonneg hcρ)
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  -- Step 1: (8)+(9) bridge.
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ_lt_one
  -- Step 2: paper equation (3) at r = ρ.
  have hEq3 :
      PaperAxioms.circleGap a b ρ =
        PaperAxioms.sigmaPlus a b ρ - ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ := by
    have h := paper.eq3_circleGap_decomposition (r := ρ) hρ_nonneg hρ_lt_one
    simpa [PaperAxioms.Eq3CircleGapDecomposition] using h
  -- Step 3: sprint 005 series identity rewrites ρ² · Σ⁻₀(ρ) = Σ⁻(ρ).
  have hSigma005 :
      PaperAxioms.sigmaMinus a b ρ =
        ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  -- Combine: circleGap(ρ) = Σ⁺(ρ) - Σ⁻(ρ).
  have hCircleEq :
      PaperAxioms.circleGap a b ρ =
        PaperAxioms.sigmaPlus a b ρ - PaperAxioms.sigmaMinus a b ρ := by
    rw [hEq3, hSigma005]
  -- Step 4: substitute into the bridge and rearrange.
  -- `Σ⁻(ρ) ≤ Λ · (Σ⁺(ρ) - Σ⁻(ρ))`, hence `(1+Λ) · Σ⁻(ρ) ≤ Λ · Σ⁺(ρ)`.
  rw [hCircleEq] at hBridge
  -- hBridge : sigmaMinus ≤ Λ * (sigmaPlus - sigmaMinus)
  nlinarith [hBridge, hΛpos]

/--
Sprint 068 / Phase A — THETA_STEP (shrinkage form).

`Σ⁻(ρ) ≤ (Λ(c, ρ) / (1 + Λ(c, ρ))) · Σ⁺(ρ)`.

Proof: divide the cross-multiplied THETA_STEP_RAW by `1 + Λ > 0`.
-/
theorem theta_step
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
    PaperAxioms.sigmaMinus a b ρ ≤
      (WangOuter.paperLambda K c ρ /
        (1 + WangOuter.paperLambda K c ρ)) *
        PaperAxioms.sigmaPlus a b ρ := by
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hOnePlusΛ_pos : 0 < 1 + WangOuter.paperLambda K c ρ := by linarith
  have hRaw :=
    theta_step_raw (a := a) (b := b) (K := K) (c := c) paper
      (ρ := ρ) hc_nonneg hcρ hρ_lt_one
  -- Divide hRaw by `1 + Λ > 0`.
  have hDiv :
      PaperAxioms.sigmaMinus a b ρ ≤
        (WangOuter.paperLambda K c ρ * PaperAxioms.sigmaPlus a b ρ) /
          (1 + WangOuter.paperLambda K c ρ) := by
    rw [le_div_iff₀ hOnePlusΛ_pos]
    linarith [hRaw]
  -- Rearrange `(Λ · Σ⁺) / (1 + Λ) = (Λ / (1 + Λ)) · Σ⁺`.
  have hRewrite :
      (WangOuter.paperLambda K c ρ * PaperAxioms.sigmaPlus a b ρ) /
          (1 + WangOuter.paperLambda K c ρ) =
        (WangOuter.paperLambda K c ρ /
          (1 + WangOuter.paperLambda K c ρ)) *
          PaperAxioms.sigmaPlus a b ρ := by
    field_simp
  rw [hRewrite] at hDiv
  exact hDiv

/--
Sprint 068 / Phase A — `Λ / (1 + Λ) < 1` whenever `0 < Λ`.

The shrinkage factor in THETA_STEP is strictly less than 1 at every `ρ` in
the workspace's regime. This is the structural input that future planners
can compose against `Σ⁺` monotonicity / closing reducers to extract a
strict gap on `Σ⁻`.
-/
theorem theta_step_strict_less_than_one
    {K : ℝ → ℝ → ℝ} {c ρ : ℝ} :
    WangOuter.paperLambda K c ρ /
        (1 + WangOuter.paperLambda K c ρ) < 1 := by
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hOnePlusΛ_pos : 0 < 1 + WangOuter.paperLambda K c ρ := by linarith
  rw [div_lt_one hOnePlusΛ_pos]
  linarith

end ProofRefinement.Korenblum.Candidates.V53.ThetaStep
