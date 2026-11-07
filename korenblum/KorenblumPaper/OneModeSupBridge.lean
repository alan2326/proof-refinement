import KorenblumPaper.FiniteModeWindow
import KorenblumPaper.OneModeSup

open scoped BigOperators

noncomputable section

namespace KorenblumPaper

namespace OneModeSupBridge

/--
The scalar integrand associated with the full one-mode supremum kernel.
-/
def scalarIntegrand (c : ℝ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  2 * ρ / (OneModeSup.supKernel c ρ * Λ ρ)

theorem innerWeightedDifference_le_supKernel_mul
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (sPos sNeg : Finset ℕ)
    (hsNeg : sNeg.Nonempty)
    (δ η : ℕ → ℝ)
    (hρ : ρ ≠ 0)
    (hδ : ∀ k ∈ sPos, 0 ≤ δ k)
    (hη : ∀ j ∈ sNeg, 0 ≤ η j)
    (hModes : ∀ j ∈ sNeg, 1 ≤ j)
    (hMajor :
      Finset.sum sPos (fun k => δ k * c ^ (2 * k)) ≤
        Finset.sum sNeg (fun j => η j * c ^ (2 * j))) :
    FiniteModeWindow.innerWeightedDifference c sPos sNeg δ η ≤
      OneModeSup.supKernel c ρ * FiniteModeWindow.sigmaMinusOn sNeg η ρ := by
  have hKernel :
      FiniteModeWindow.innerWeightedDifference c sPos sNeg δ η ≤
        OneModeKernel.kernelOn c ρ sNeg hsNeg *
          FiniteModeWindow.sigmaMinusOn sNeg η ρ := by
    simpa [FiniteModeWindow.innerWeightedDifference, FiniteModeWindow.sigmaMinusOn] using
      (OneModeAlgebra.weighted_difference_le_kernelOn_mul
        hc sPos sNeg hsNeg δ η hρ hδ hη hMajor)
  have hKernelLe :
      OneModeKernel.kernelOn c ρ sNeg hsNeg ≤ OneModeSup.supKernel c ρ := by
    exact Finset.sup'_le (s := sNeg) (f := OneModeKernel.term c ρ) hsNeg
      (fun j hj => OneModeSup.term_le_supKernel c ρ hc hcρ (hModes j hj))
  have hSigmaNonneg :
      0 ≤ FiniteModeWindow.sigmaMinusOn sNeg η ρ := by
    unfold FiniteModeWindow.sigmaMinusOn
    refine Finset.sum_nonneg ?_
    intro j hj
    have hηj : 0 ≤ η j := hη j hj
    have hPow : 0 ≤ ρ ^ (2 * j) := by
      have hEq : ρ ^ (2 * j) = (ρ ^ j) ^ 2 := by
        rw [show 2 * j = j * 2 by omega, pow_mul]
      rw [hEq]
      exact sq_nonneg (ρ ^ j)
    exact mul_nonneg hηj hPow
  exact le_trans hKernel (mul_le_mul_of_nonneg_right hKernelLe hSigmaNonneg)

theorem sigma_reduction_of_supKernel
    {c ρ innerExcess : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (sPos sNeg : Finset ℕ)
    (hsNeg : sNeg.Nonempty)
    (δ η : ℕ → ℝ)
    (hρ : ρ ≠ 0)
    (hδ : ∀ k ∈ sPos, 0 ≤ δ k)
    (hη : ∀ j ∈ sNeg, 0 ≤ η j)
    (hModes : ∀ j ∈ sNeg, 1 ≤ j)
    (hMajor :
      Finset.sum sPos (fun k => δ k * c ^ (2 * k)) ≤
        Finset.sum sNeg (fun j => η j * c ^ (2 * j)))
    (hInner :
      innerExcess ≤ FiniteModeWindow.innerWeightedDifference c sPos sNeg δ η) :
    innerExcess ≤
      OneModeSup.supKernel c ρ * FiniteModeWindow.sigmaMinusOn sNeg η ρ :=
  le_trans hInner
    (innerWeightedDifference_le_supKernel_mul
      hc hcρ sPos sNeg hsNeg δ η hρ hδ hη hModes hMajor)

theorem pointwise_of_sigma_supKernel
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    (hc : 0 < c)
    {sigmaMinus circleGap : ℝ → ℝ}
    (hSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        innerExcess ≤ OneModeSup.supKernel c ρ * sigmaMinus ρ)
    (hSigmaToCircle :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        sigmaMinus ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  intro ρ hcr hρ1
  have hSigmaρ :
      innerExcess ≤ OneModeSup.supKernel c ρ * sigmaMinus ρ :=
    hSigma hcr hρ1
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hSupPos : 0 < OneModeSup.supKernel c ρ :=
    OneModeSup.supKernel_pos hc hcr
  have hFactorNonneg :
      0 ≤ scalarIntegrand c (WangOuter.paperLambda K c) ρ := by
    unfold scalarIntegrand
    have hρnonneg : 0 ≤ 2 * ρ := by nlinarith
    exact div_nonneg hρnonneg (mul_nonneg hSupPos.le hΛpos.le)
  have hSupNe : OneModeSup.supKernel c ρ ≠ 0 := ne_of_gt hSupPos
  have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hFactorKernel :
      scalarIntegrand c (WangOuter.paperLambda K c) ρ *
        OneModeSup.supKernel c ρ =
        2 * ρ / WangOuter.paperLambda K c ρ := by
    unfold scalarIntegrand
    field_simp [hSupNe, hΛne]
  have hScaled :
      scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
    calc
      scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess
          ≤ scalarIntegrand c (WangOuter.paperLambda K c) ρ *
              (OneModeSup.supKernel c ρ * sigmaMinus ρ) := by
                exact mul_le_mul_of_nonneg_left hSigmaρ hFactorNonneg
      _ = (scalarIntegrand c (WangOuter.paperLambda K c) ρ *
            OneModeSup.supKernel c ρ) * sigmaMinus ρ := by
            ring
      _ = (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
            rw [hFactorKernel]
  have hDiv :
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ ≤
        2 * ρ * circleGap ρ := by
    have hScaleNonneg : 0 ≤ 2 * ρ / WangOuter.paperLambda K c ρ := by
      have hρnonneg : 0 ≤ 2 * ρ := by nlinarith
      exact div_nonneg hρnonneg hΛpos.le
    have hScaledSigma :
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ ≤
          (2 * ρ / WangOuter.paperLambda K c ρ) *
            (WangOuter.paperLambda K c ρ * circleGap ρ) := by
      exact mul_le_mul_of_nonneg_left (hSigmaToCircle hcr hρ1) hScaleNonneg
    calc
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinus ρ
          ≤ (2 * ρ / WangOuter.paperLambda K c ρ) *
              (WangOuter.paperLambda K c ρ * circleGap ρ) := hScaledSigma
      _ = 2 * ρ * circleGap ρ := by
            field_simp [hΛne]
  exact le_trans hScaled hDiv

theorem pointwise_of_supKernel
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    (hc : 0 < c)
    (sPos sNeg : Finset ℕ)
    (hsNeg : sNeg.Nonempty)
    (δ η : ℕ → ℝ)
    (hδ : ∀ k ∈ sPos, 0 ≤ δ k)
    (hη : ∀ j ∈ sNeg, 0 ≤ η j)
    (hModes : ∀ j ∈ sNeg, 1 ≤ j)
    (hMajor :
      Finset.sum sPos (fun k => δ k * c ^ (2 * k)) ≤
        Finset.sum sNeg (fun j => η j * c ^ (2 * j)))
    (hInner :
      innerExcess ≤ FiniteModeWindow.innerWeightedDifference c sPos sNeg δ η)
    {circleGap : ℝ → ℝ}
    (hSigmaToCircle :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        FiniteModeWindow.sigmaMinusOn sNeg η ρ ≤
          WangOuter.paperLambda K c ρ * circleGap ρ) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  apply pointwise_of_sigma_supKernel hc
  · intro ρ hcr hρ1
    have hρne : ρ ≠ 0 := ne_of_gt (lt_trans hc hcr)
    exact sigma_reduction_of_supKernel
      hc.le hcr.le sPos sNeg hsNeg δ η hρne hδ hη hModes hMajor hInner
  · exact hSigmaToCircle

end OneModeSupBridge

end KorenblumPaper
