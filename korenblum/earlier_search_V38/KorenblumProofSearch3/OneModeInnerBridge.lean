import KorenblumProofSearch3.OneModeDiskBridge
import KorenblumProofSearch3.OneModePaperBridge

open MeasureTheory

noncomputable section

namespace KorenblumProofSearch3

namespace OneModePaperBridge

theorem sq_mul_sigmaZeroMinus_eq_sigmaMinus
    (a b : ℕ → ℂ)
    (r : ℝ) :
    r ^ 2 * PaperAxioms.sigmaZeroMinus a b r = PaperAxioms.sigmaMinus a b r := by
  classical
  rw [PaperAxioms.sigmaZeroMinus, PaperAxioms.sigmaMinus, ← tsum_mul_left]
  refine tsum_congr ?_
  intro k
  by_cases hk : PaperAxioms.n2Pred a b k
  · have hkpos : 0 < k := hk.1
    calc
      r ^ 2 * (if PaperAxioms.n2Pred a b k then PaperAxioms.coeffMinusGap a b k * r ^ (2 * k - 2) else 0)
          = r ^ 2 * (PaperAxioms.coeffMinusGap a b k * r ^ (2 * k - 2)) := by simp [hk]
      _ = PaperAxioms.coeffMinusGap a b k * r ^ (2 * k) := by
            have hExp : 2 + (2 * k - 2) = 2 * k := by omega
            have hPow : r ^ (2 * k) = r ^ 2 * r ^ (2 * k - 2) := by
              calc
                r ^ (2 * k) = r ^ (2 + (2 * k - 2)) := by rw [hExp]
                _ = r ^ 2 * r ^ (2 * k - 2) := by rw [pow_add]
            rw [hPow]
            ring
      _ = if PaperAxioms.n2Pred a b k then PaperAxioms.coeffMinusGap a b k * r ^ (2 * k) else 0 := by
            simp [hk]
  · simp [hk]

theorem eq3_pointwise_sub_sigmaMinus
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    paper.circleGap r = PaperAxioms.sigmaPlus a b r - PaperAxioms.sigmaMinus a b r := by
  have hEq3 := paper.eq3_circleGap_decomposition hr0 hr1
  simpa [PaperAxioms.Eq3CircleGapDecomposition, sq_mul_sigmaZeroMinus_eq_sigmaMinus] using hEq3

theorem annulusSlice_sigmaPlus_eq_diskWeightedSeq
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n))) :
    AnnulusIntegralReduction.annulusSlice (PaperAxioms.sigmaPlus a b) 0 c =
      OneModeSeries.diskWeightedSeq (plusSeq a b) c := by
  have hSigma :
      PaperAxioms.sigmaPlus a b = OneModeSeries.sigmaSeq (plusSeq a b) := by
    funext s
    exact sigmaPlus_eq_sigmaSeq (a := a) (b := b) (s := s)
  rw [hSigma]
  exact OneModeSeries.annulusSlice_sigmaSeq_eq_diskWeightedSeq_of_nonneg_tail
    hc (plusSeq_nonneg_of_pos a b) hPlusDisk hPlusSigma

theorem annulusSlice_sigmaMinus_eq_diskWeightedSeq
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hMinusSigma :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n))) :
    AnnulusIntegralReduction.annulusSlice (PaperAxioms.sigmaMinus a b) 0 c =
      OneModeSeries.diskWeightedSeq (minusSeq a b) c := by
  have hSigma :
      PaperAxioms.sigmaMinus a b = OneModeSeries.sigmaSeq (minusSeq a b) := by
    funext s
    exact sigmaMinus_eq_sigmaSeq (a := a) (b := b) (s := s)
  rw [hSigma]
  exact OneModeSeries.annulusSlice_sigmaSeq_eq_diskWeightedSeq hc (minusSeq_nonneg a b) hMinusSigma

theorem annulusDensity_sigmaPlus_intervalIntegrable
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n))) :
    IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaPlus a b))
      volume 0 c := by
  have hSigma :
      PaperAxioms.sigmaPlus a b = OneModeSeries.sigmaSeq (plusSeq a b) := by
    funext s
    exact sigmaPlus_eq_sigmaSeq (a := a) (b := b) (s := s)
  rw [hSigma]
  exact OneModeSeries.annulusDensity_sigmaSeq_intervalIntegrable_of_nonneg_tail
    hc (plusSeq_nonneg_of_pos a b) hPlusSigma

theorem annulusDensity_sigmaMinus_intervalIntegrable
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hMinusSigma :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n))) :
    IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b))
      volume 0 c := by
  have hSigma :
      PaperAxioms.sigmaMinus a b = OneModeSeries.sigmaSeq (minusSeq a b) := by
    funext s
    exact sigmaMinus_eq_sigmaSeq (a := a) (b := b) (s := s)
  rw [hSigma]
  exact OneModeSeries.annulusDensity_sigmaSeq_intervalIntegrable
    hc (minusSeq_nonneg a b) hMinusSigma

theorem annulusSlice_circleGap_eq_innerSeriesExcess
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    (hc : 0 ≤ c)
    (hc1 : c < 1)
    (hPlusDisk :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => plusSeq a b n * c ^ (2 * n)))
    (hMinusSigma :
      Summable (fun n : ℕ => minusSeq a b n * c ^ (2 * n))) :
    AnnulusIntegralReduction.annulusSlice paper.circleGap 0 c = innerSeriesExcess a b c := by
  have hIntPlus :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaPlus a b))
        volume 0 c :=
    annulusDensity_sigmaPlus_intervalIntegrable hc hPlusSigma
  have hIntMinus :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b))
        volume 0 c :=
    annulusDensity_sigmaMinus_intervalIntegrable hc hMinusSigma
  unfold AnnulusIntegralReduction.annulusSlice innerSeriesExcess
  calc
    ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity paper.circleGap ρ
        = ∫ ρ in 0..c,
            AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaPlus a b) ρ -
              AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b) ρ := by
            refine intervalIntegral.integral_congr ?_
            intro ρ hρ
            have hρIcc : ρ ∈ Set.Icc 0 c := by
              simpa [Set.uIcc_of_le hc] using hρ
            have hEq :
                paper.circleGap ρ = PaperAxioms.sigmaPlus a b ρ - PaperAxioms.sigmaMinus a b ρ :=
              eq3_pointwise_sub_sigmaMinus paper hρIcc.1 (lt_of_le_of_lt hρIcc.2 hc1)
            simp [AnnulusIntegralReduction.annulusDensity, hEq]
            ring
    _ = (∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaPlus a b) ρ) -
          ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b) ρ := by
            rw [intervalIntegral.integral_sub hIntPlus hIntMinus]
    _ = OneModeSeries.diskWeightedSeq (plusSeq a b) c -
          ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b) ρ := by
            rw [show
                ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaPlus a b) ρ =
                  AnnulusIntegralReduction.annulusSlice (PaperAxioms.sigmaPlus a b) 0 c by
                rfl]
            rw [annulusSlice_sigmaPlus_eq_diskWeightedSeq hc hPlusDisk hPlusSigma]
    _ = OneModeSeries.diskWeightedSeq (plusSeq a b) c -
          OneModeSeries.diskWeightedSeq (minusSeq a b) c := by
            rw [show
                ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (PaperAxioms.sigmaMinus a b) ρ =
                  AnnulusIntegralReduction.annulusSlice (PaperAxioms.sigmaMinus a b) 0 c by
                rfl]
            rw [annulusSlice_sigmaMinus_eq_diskWeightedSeq hc hMinusSigma]

end OneModePaperBridge

end KorenblumProofSearch3
