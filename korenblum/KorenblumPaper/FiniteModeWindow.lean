import KorenblumPaper.OneModeAlgebra
import KorenblumPaper.ModeBridge

open scoped BigOperators

noncomputable section

namespace KorenblumPaper

namespace FiniteModeWindow

def sigmaMinusOn (sNeg : Finset ℕ) (η : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  Finset.sum sNeg (fun j => η j * ρ ^ (2 * j))

def innerWeightedDifference
    (c : ℝ)
    (sPos sNeg : Finset ℕ)
    (δ η : ℕ → ℝ) : ℝ :=
  Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) -
    Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ))

theorem sigma_term_bound_of_tau_window
    {c ρ : ℝ}
    (hc : 0 ≤ c)
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
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2)
    (hUpper : c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode) :
    innerWeightedDifference c sPos sNeg δ η ≤
      OneModeKernel.term c ρ mode * sigmaMinusOn sNeg η ρ := by
  simpa [innerWeightedDifference, sigmaMinusOn] using
    (OneModeAlgebra.weighted_difference_le_term_of_tau_bounds
      hc sPos sNeg hsNeg δ η hρ hδ hη hModes hMajor hMode hLower hUpper)

theorem pointwise_of_tau_window
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
    (hInner : innerExcess ≤ innerWeightedDifference c sPos sNeg δ η)
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    {circleGap : ℝ → ℝ}
    (hSigmaToCircle :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        sigmaMinusOn sNeg η ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2 →
      c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode →
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  intro ρ hcr hρ1 hLower hUpper
  have hρne : ρ ≠ 0 := ne_of_gt (lt_trans hc hcr)
  have hCoeff :
      innerWeightedDifference c sPos sNeg δ η ≤
        OneModeKernel.term c ρ mode * sigmaMinusOn sNeg η ρ :=
    sigma_term_bound_of_tau_window hc.le sPos sNeg hsNeg δ η hρne hδ hη hModes hMajor hMode
      hLower hUpper
  have hSigma :
      innerExcess ≤ OneModeKernel.term c ρ mode * sigmaMinusOn sNeg η ρ :=
    le_trans hInner hCoeff
  have hmodepos : 0 < mode := Nat.succ_le_iff.mp hMode
  have hρpos : 0 < ρ := lt_trans hc hcr
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hTermPos : 0 < OneModeKernel.term c ρ mode := by
    unfold OneModeKernel.term OneModeKernel.weight
    positivity
  have hFactorNonneg :
      0 ≤ ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ := by
    unfold ModeBridge.scalarIntegrand
    exact div_nonneg (by positivity) (by positivity)
  have hTermNe : OneModeKernel.term c ρ mode ≠ 0 := ne_of_gt hTermPos
  have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hFactorKernel :
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ *
        OneModeKernel.term c ρ mode =
        2 * ρ / WangOuter.paperLambda K c ρ := by
    unfold ModeBridge.scalarIntegrand
    field_simp [hTermNe, hΛne]
  have hScaled :
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ * innerExcess ≤
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinusOn sNeg η ρ := by
    calc
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ * innerExcess
          ≤ ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ *
              (OneModeKernel.term c ρ mode * sigmaMinusOn sNeg η ρ) := by
                exact mul_le_mul_of_nonneg_left hSigma hFactorNonneg
      _ = (ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ *
            OneModeKernel.term c ρ mode) * sigmaMinusOn sNeg η ρ := by ring
      _ = (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinusOn sNeg η ρ := by
        rw [hFactorKernel]
  have hDiv :
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinusOn sNeg η ρ ≤
        2 * ρ * circleGap ρ := by
    have hScaleNonneg : 0 ≤ 2 * ρ / WangOuter.paperLambda K c ρ := by
      positivity
    have hScaledSigma :
        (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinusOn sNeg η ρ ≤
          (2 * ρ / WangOuter.paperLambda K c ρ) *
            (WangOuter.paperLambda K c ρ * circleGap ρ) := by
      exact mul_le_mul_of_nonneg_left (hSigmaToCircle hcr hρ1) hScaleNonneg
    calc
      (2 * ρ / WangOuter.paperLambda K c ρ) * sigmaMinusOn sNeg η ρ
          ≤ (2 * ρ / WangOuter.paperLambda K c ρ) *
              (WangOuter.paperLambda K c ρ * circleGap ρ) := hScaledSigma
      _ = 2 * ρ * circleGap ρ := by
            field_simp [hΛne]
  exact le_trans hScaled hDiv

end FiniteModeWindow

end KorenblumPaper
