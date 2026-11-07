import KorenblumProofSearch3.OneModeKernel

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace ModeBridge

/--
The scalar integrand attached to a fixed one-mode coefficient term.
-/
def scalarIntegrand (c : ℝ) (j : ℕ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  2 * ρ / (OneModeKernel.term c ρ j * Λ ρ)

/--
Algebraic form of the mode-`j` scalar integrand for positive `j`.
-/
theorem scalarIntegrand_eq
    (c : ℝ)
    {j : ℕ}
    (hj : 0 < j)
    (Λ : ℝ → ℝ)
    {ρ : ℝ}
    (hc : 0 < c)
    (hρ : ρ ≠ 0)
    (hΛ : Λ ρ ≠ 0) :
    scalarIntegrand c j Λ ρ =
      ((2 : ℝ) * (j + 1) / j) * ρ ^ (2 * j + 1) / (c ^ (2 * j + 2) * Λ ρ) := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hρpow : ρ ^ (2 * j) ≠ 0 := pow_ne_zero _ hρ
  have hcPow : c ^ (2 * j + 2) ≠ 0 := pow_ne_zero _ hc.ne'
  unfold scalarIntegrand OneModeKernel.term OneModeKernel.weight
  field_simp [hjR, hρpow, hcPow, hΛ]
  ring

/--
Mode-`j` pointwise bridge: a coefficient-side bound by the `j`th one-mode term,
combined with Wang's printed equations `(8)` and `(9)`, yields a pointwise
boundary excess inequality.
-/
theorem pointwise_of_sigma_term_eq8_eq9
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    {j : ℕ}
    (hj : 0 < j)
    {sigmaMinus liftGap circleGap : ℝ → ℝ}
    (hSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        innerExcess ≤ OneModeKernel.term c ρ j * sigmaMinus ρ)
    (h8 : PaperAxioms.Eq8SigmaToLiftGap c sigmaMinus liftGap)
    (h9 : PaperAxioms.Eq9LiftGapToCircleGap K c liftGap circleGap)
    (hc : 0 < c) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      scalarIntegrand c j (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  intro ρ hcr hρ1
  have hSigmaρ : innerExcess ≤ OneModeKernel.term c ρ j * sigmaMinus ρ := hSigma hcr hρ1
  have h89ρ : sigmaMinus ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9 h8 h9 hcr hρ1
  have hρpos : 0 < ρ := lt_trans hc hcr
  have hTermPos : 0 < OneModeKernel.term c ρ j := by
    unfold OneModeKernel.term OneModeKernel.weight
    positivity
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hFactorNonneg :
      0 ≤ scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
    unfold scalarIntegrand
    positivity
  have hTermNe : OneModeKernel.term c ρ j ≠ 0 := ne_of_gt hTermPos
  have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hFactorKernel :
      scalarIntegrand c j (WangOuter.paperLambda K c) ρ *
        OneModeKernel.term c ρ j =
        2 * ρ / WangOuter.paperLambda K c ρ := by
    unfold scalarIntegrand
    field_simp [hTermNe, hΛne]
  have hScaled :
      scalarIntegrand c j (WangOuter.paperLambda K c) ρ * innerExcess ≤
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
    calc
      scalarIntegrand c j (WangOuter.paperLambda K c) ρ * innerExcess
          ≤ scalarIntegrand c j (WangOuter.paperLambda K c) ρ *
              (OneModeKernel.term c ρ j * sigmaMinus ρ) := by
              exact mul_le_mul_of_nonneg_left hSigmaρ hFactorNonneg
      _ = (scalarIntegrand c j (WangOuter.paperLambda K c) ρ *
            OneModeKernel.term c ρ j) * sigmaMinus ρ := by ring
      _ = (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
        rw [hFactorKernel]
  have hDiv :
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ ≤ 2 * ρ * circleGap ρ := by
    have hScaled89 :
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ ≤
          (2 * ρ / WangOuter.paperLambda K c ρ) *
            (WangOuter.paperLambda K c ρ * circleGap ρ) := by
      exact mul_le_mul_of_nonneg_left h89ρ (by positivity)
    calc
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ
          ≤ (2 * ρ / WangOuter.paperLambda K c ρ) *
              (WangOuter.paperLambda K c ρ * circleGap ρ) := hScaled89
      _ = 2 * ρ * circleGap ρ := by
            field_simp [hΛne]
  exact le_trans hScaled hDiv

end ModeBridge

end KorenblumProofSearch3
