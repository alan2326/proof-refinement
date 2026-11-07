import KorenblumPaper.OneModeSeries
import KorenblumPaper.OneModeSupBridge
import KorenblumPaper.OneModeTauWindow

noncomputable section

namespace KorenblumPaper

namespace OneModePaperBridge

open Classical in
def plusSeq (a b : ℕ → ℂ) (k : ℕ) : ℝ :=
  if PaperAxioms.n1Pred a b k then PaperAxioms.coeffPlusGap a b k else 0

open Classical in
def minusSeq (a b : ℕ → ℂ) (k : ℕ) : ℝ :=
  if PaperAxioms.n2Pred a b k then PaperAxioms.coeffMinusGap a b k else 0

theorem plusSeq_nonneg_of_pos
    (a b : ℕ → ℂ)
    (k : ℕ)
    (hk1 : 1 ≤ k) :
    0 ≤ plusSeq a b k := by
  classical
  by_cases hk : PaperAxioms.n1Pred a b k
  · rw [plusSeq, if_pos hk]
    rcases hk with rfl | hk
    · omega
    · unfold PaperAxioms.coeffPlusGap
      have ha : 0 ≤ ‖a k‖ := norm_nonneg _
      have hb : 0 ≤ ‖b k‖ := norm_nonneg _
      nlinarith
  · rw [plusSeq, if_neg hk]

theorem minusSeq_nonneg (a b : ℕ → ℂ) (k : ℕ) : 0 ≤ minusSeq a b k := by
  classical
  by_cases hk : PaperAxioms.n2Pred a b k
  · rw [minusSeq, if_pos hk]
    unfold PaperAxioms.coeffMinusGap
    have ha : 0 ≤ ‖a k‖ := norm_nonneg _
    have hb : 0 ≤ ‖b k‖ := norm_nonneg _
    have hab : ‖a k‖ < ‖b k‖ := hk.2
    nlinarith
  · rw [minusSeq, if_neg hk]

theorem minusSeq_mode
    (a b : ℕ → ℂ)
    (k : ℕ)
    (hk : minusSeq a b k ≠ 0) :
    1 ≤ k := by
  classical
  by_cases hPred : PaperAxioms.n2Pred a b k
  · exact Nat.succ_le_of_lt hPred.1
  · simp [minusSeq, hPred] at hk

theorem sigmaPlus_eq_sigmaSeq
    (a b : ℕ → ℂ)
    (s : ℝ) :
    PaperAxioms.sigmaPlus a b s = OneModeSeries.sigmaSeq (plusSeq a b) s := by
  classical
  unfold PaperAxioms.sigmaPlus OneModeSeries.sigmaSeq
  refine tsum_congr ?_
  intro k
  by_cases hk : PaperAxioms.n1Pred a b k
  · simp [plusSeq, hk]
  · simp [plusSeq, hk]

theorem sigmaMinus_eq_sigmaSeq
    (a b : ℕ → ℂ)
    (s : ℝ) :
    PaperAxioms.sigmaMinus a b s = OneModeSeries.sigmaSeq (minusSeq a b) s := by
  classical
  unfold PaperAxioms.sigmaMinus OneModeSeries.sigmaSeq
  refine tsum_congr ?_
  intro k
  by_cases hk : PaperAxioms.n2Pred a b k
  · simp [minusSeq, hk]
  · simp [minusSeq, hk]

theorem sigmaMinus_nonneg
    (a b : ℕ → ℂ)
    (ρ : ℝ) :
    0 ≤ PaperAxioms.sigmaMinus a b ρ := by
  rw [sigmaMinus_eq_sigmaSeq]
  unfold OneModeSeries.sigmaSeq
  refine tsum_nonneg ?_
  intro n
  have hPow : 0 ≤ ρ ^ (2 * n) := by
    have hEq : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [hEq]
    exact sq_nonneg (ρ ^ n)
  exact mul_nonneg (minusSeq_nonneg a b n) hPow

theorem sigmaPlus_le_sigmaMinus_of_eq4
    {sigmaPlus sigmaMinus sigmaZeroMinus : ℝ → ℝ}
    {r c : ℝ}
    (hEq4 : PaperAxioms.Eq4SigmaPlusBound sigmaPlus sigmaMinus sigmaZeroMinus r c) :
    sigmaPlus c ≤ sigmaMinus c :=
  hEq4.2.1

/--
Coefficient-side disk excess obtained by integrating the coefficient gaps with
the Bergman disk weights `c^(2n+2)/(n+1)`.
-/
def innerSeriesExcess (a b : ℕ → ℂ) (c : ℝ) : ℝ :=
  OneModeSeries.diskWeightedSeq (plusSeq a b) c -
    OneModeSeries.diskWeightedSeq (minusSeq a b) c

theorem sigmaReduction_of_series
    {a b : ℕ → ℂ}
    {c ρ innerExcess : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n)))
    (hMinusSigmaRho :
      Summable (fun n : ℕ => minusSeq a b n * ρ ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ => minusSeq a b n * OneModeKernel.weight c n))
    (hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInner :
      innerExcess ≤
        OneModeSeries.diskWeightedSeq (plusSeq a b) c -
          OneModeSeries.diskWeightedSeq (minusSeq a b) c) :
    innerExcess ≤ OneModeSup.supKernel c ρ * PaperAxioms.sigmaMinus a b ρ := by
  have hMajor :
      OneModeSeries.sigmaSeq (plusSeq a b) c ≤
        OneModeSeries.sigmaSeq (minusSeq a b) c := by
    simpa [sigmaPlus_eq_sigmaSeq, sigmaMinus_eq_sigmaSeq] using hPlusLeMinus
  have hCore :=
    OneModeSeries.inner_le_supKernel_mul_sigmaSeq
      hc hcρ hρ
      (plusSeq_nonneg_of_pos a b)
      (minusSeq_nonneg a b)
      (minusSeq_mode a b)
      hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusSigmaRho hMinusWeight
      hMajor hInner
  simpa [sigmaMinus_eq_sigmaSeq] using hCore

theorem innerSeriesExcess_le_supKernel_mul_sigmaMinus
    {a b : ℕ → ℂ}
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n)))
    (hMinusSigmaRho :
      Summable (fun n : ℕ => minusSeq a b n * ρ ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ => minusSeq a b n * OneModeKernel.weight c n))
    (hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) :
    innerSeriesExcess a b c ≤
      OneModeSup.supKernel c ρ * PaperAxioms.sigmaMinus a b ρ := by
  exact sigmaReduction_of_series
    hc hcρ hρ
    hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusSigmaRho hMinusWeight
    hPlusLeMinus le_rfl

theorem pointwise_of_series_eq8_eq9
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    (hc : 0 < c)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ => minusSeq a b n * OneModeKernel.weight c n))
    (hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInner : innerExcess ≤ innerSeriesExcess a b c)
    {liftGap circleGap : ℝ → ℝ}
    (h8 :
      PaperAxioms.Eq8SigmaToLiftGap c (PaperAxioms.sigmaMinus a b) liftGap)
    (h9 :
      PaperAxioms.Eq9LiftGapToCircleGap K c liftGap circleGap)
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        Summable (fun n : ℕ => minusSeq a b n * ρ ^ (2 * n))) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  apply OneModeSupBridge.pointwise_of_sigma_supKernel hc
  · intro ρ hcr hρ1
    have hρne : ρ ≠ 0 := ne_of_gt (lt_trans hc hcr)
    exact le_trans hInner <|
      innerSeriesExcess_le_supKernel_mul_sigmaMinus hc.le hcr.le hρne
      hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC
      (hMinusSigma hcr hρ1) hMinusWeight hPlusLeMinus
  · exact PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9 h8 h9

theorem circleGap_nonneg_of_eq8_eq9
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    {ρ : ℝ}
    (hcr : c < ρ)
    (hρ1 : ρ < 1) :
    0 ≤ paper.circleGap ρ := by
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * paper.circleGap ρ :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcr hρ1
  have hSigmaNonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ :=
    sigmaMinus_nonneg a b ρ
  have hMulNonneg : 0 ≤ WangOuter.paperLambda K c ρ * paper.circleGap ρ := by
    exact le_trans hSigmaNonneg hBridge
  have hLambdaPos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  nlinarith

theorem supScalar_eq_modeScalar_of_tau_bounds
    {K : ℝ → ℝ → ℝ}
    {c ρ : ℝ}
    (hc : 0 < c)
    (hcr : c < ρ)
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2)
    (hUpper : c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode) :
    OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ =
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ := by
  have hρne : ρ ≠ 0 := ne_of_gt (lt_trans hc hcr)
  have hSupEq :
      OneModeSup.supKernel c ρ = OneModeKernel.term c ρ mode :=
    OneModeSup.supKernel_eq_term_of_tau_bounds
      hc.le hcr.le hρne hMode hLower hUpper
  unfold OneModeSupBridge.scalarIntegrand ModeBridge.scalarIntegrand
  rw [hSupEq]

theorem pointwise_of_series_tau_window_eq8_eq9
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    (hc : 0 < c)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ => minusSeq a b n * OneModeKernel.weight c n))
    (hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInner : innerExcess ≤ innerSeriesExcess a b c)
    {liftGap circleGap : ℝ → ℝ}
    (h8 :
      PaperAxioms.Eq8SigmaToLiftGap c (PaperAxioms.sigmaMinus a b) liftGap)
    (h9 :
      PaperAxioms.Eq9LiftGapToCircleGap K c liftGap circleGap)
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        Summable (fun n : ℕ => minusSeq a b n * ρ ^ (2 * n)))
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    (hLower :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2)
    (hUpper :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  intro ρ hcr hρ1
  have hSup :
      OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ :=
    pointwise_of_series_eq8_eq9
      hc hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInner
      h8 h9 hMinusSigma hcr hρ1
  have hEq :
      OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ =
        ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ :=
    supScalar_eq_modeScalar_of_tau_bounds
      (K := K) hc hcr hMode (hLower hcr hρ1) (hUpper hcr hρ1)
  simpa [hEq] using hSup

theorem pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    (hc : 0 < c)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ => minusSeq a b n * OneModeKernel.weight c n))
    (hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInner : innerExcess ≤ innerSeriesExcess a b c)
    {liftGap circleGap : ℝ → ℝ}
    (h8 :
      PaperAxioms.Eq8SigmaToLiftGap c (PaperAxioms.sigmaMinus a b) liftGap)
    (h9 :
      PaperAxioms.Eq9LiftGapToCircleGap K c liftGap circleGap)
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        Summable (fun n : ℕ => minusSeq a b n * ρ ^ (2 * n)))
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    {start stop : ℝ}
    (hStart : c < start)
    (hStop : stop < 1)
    (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / stop ^ 2)
    (hUpper : c ^ 2 / start ^ 2 ≤ OneModeTail.tau mode) :
    ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc start stop →
      ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ := by
  intro ρ hρ
  have hcr : c < ρ := lt_of_lt_of_le hStart hρ.1
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 hStop
  have hTau :
      OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2 ∧
        c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode :=
    OneModeTauWindow.tau_bounds_of_mem_Icc
      (lt_trans hc hStart) hρ hLower hUpper
  have hSup :
      OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        2 * ρ * circleGap ρ :=
    pointwise_of_series_eq8_eq9
      hc hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInner
      h8 h9 hMinusSigma hcr hρ1
  have hEq :
      OneModeSupBridge.scalarIntegrand c (WangOuter.paperLambda K c) ρ =
        ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ :=
    supScalar_eq_modeScalar_of_tau_bounds
      (K := K) hc hcr hMode hTau.1 hTau.2
  simpa [hEq] using hSup

end OneModePaperBridge

end KorenblumPaper
