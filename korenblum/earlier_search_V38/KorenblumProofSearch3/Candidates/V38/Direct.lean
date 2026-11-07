import KorenblumProofSearch3.Candidates.V38.Main
import KorenblumProofSearch3.OneModeInnerBridge
import KorenblumProofSearch3.WindowBoxReduction

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3.V38

open KorenblumProofSearch3

private theorem annulusSubset
    {a b : ℚ}
    (hca : cValueQ ≤ a)
    (hab : a ≤ b)
    (hb1 : b ≤ 1) :
    Set.uIcc (a : ℝ) (b : ℝ) ⊆ Set.uIcc (cValueQ : ℝ) (1 : ℝ) := by
  apply Set.uIcc_subset_uIcc
  · exact Set.mem_uIcc_of_le (by exact_mod_cast hca) (by exact_mod_cast le_trans hab hb1)
  · exact Set.mem_uIcc_of_le (by exact_mod_cast le_trans hca hab) (by exact_mod_cast hb1)

private theorem annulusInt_subinterval
    {circleGap : ℝ → ℝ}
    {a b : ℚ}
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (cValueQ : ℝ) (1 : ℝ))
    (hca : cValueQ ≤ a)
    (hab : a ≤ b)
    (hb1 : b ≤ 1) :
    IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
      volume (a : ℝ) (b : ℝ) :=
  hAnnInt.mono_set (annulusSubset hca hab hb1)

private theorem plusDisk_summable_of_plusSigma
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hPlusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.plusSeq a b n * c ^ (2 * n))) :
    Summable
      (fun n : ℕ => OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
  let v := OneModeSeries.tailSeq (OneModePaperBridge.plusSeq a b)
  have hSigmaV : Summable (fun n : ℕ => v n * c ^ (2 * n)) :=
    OneModeSeries.summable_sigma_tail_of_summable_sigma hPlusSigma
  have hDiskV :
      Summable (fun n : ℕ => v n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
    have hScaled : Summable (fun n : ℕ => c ^ 2 * (v n * c ^ (2 * n))) :=
      hSigmaV.mul_left (c ^ 2)
    refine Summable.of_nonneg_of_le ?_ ?_ hScaled
    · intro n
      have hv : 0 ≤ v n :=
        OneModeSeries.tailSeq_nonneg (OneModePaperBridge.plusSeq_nonneg_of_pos a b) n
      exact div_nonneg (mul_nonneg hv (pow_nonneg hc _)) (by positivity)
    · intro n
      have hv : 0 ≤ v n :=
        OneModeSeries.tailSeq_nonneg (OneModePaperBridge.plusSeq_nonneg_of_pos a b) n
      have hcmp :
          v n * (c ^ (2 * n + 2) / (n + 1 : ℝ)) ≤
            v n * (c ^ 2 * c ^ (2 * n)) := by
        exact mul_le_mul_of_nonneg_left (OneModeAlgebra.positive_term_le_csq_mul hc n) hv
      calc
        v n * c ^ (2 * n + 2) / (n + 1 : ℝ)
            = v n * (c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
                rw [mul_div_assoc]
        _ ≤ v n * (c ^ 2 * c ^ (2 * n)) := hcmp
        _ = c ^ 2 * (v n * c ^ (2 * n)) := by ring
  have hHead :
      Summable (fun n : ℕ => if n = 0 then OneModePaperBridge.plusSeq a b n * c ^ 2 else 0) := by
    exact summable_of_finite_support <| (Set.finite_singleton 0).subset <| by
      intro n hn
      by_cases h : n = 0
      · simp [h]
      · simp [h] at hn
  refine (hHead.add hDiskV).congr ?_
  intro n
  by_cases hn : n = 0
  · simp [v, OneModeSeries.tailSeq, hn]
  · simp [v, OneModeSeries.tailSeq, hn]

private theorem minusDisk_summable_of_minusSigma
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hMinusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * c ^ (2 * n))) :
    Summable
      (fun n : ℕ => OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
  have hScaled : Summable (fun n : ℕ => c ^ 2 * (OneModePaperBridge.minusSeq a b n * c ^ (2 * n))) :=
    hMinusSigma.mul_left (c ^ 2)
  refine Summable.of_nonneg_of_le ?_ ?_ hScaled
  · intro n
    exact div_nonneg
      (mul_nonneg (OneModePaperBridge.minusSeq_nonneg a b n) (pow_nonneg hc _))
      (by positivity)
  · intro n
    have hcmp :
        OneModePaperBridge.minusSeq a b n * (c ^ (2 * n + 2) / (n + 1 : ℝ)) ≤
          OneModePaperBridge.minusSeq a b n * (c ^ 2 * c ^ (2 * n)) := by
      exact mul_le_mul_of_nonneg_left
        (OneModeAlgebra.positive_term_le_csq_mul hc n)
        (OneModePaperBridge.minusSeq_nonneg a b n)
    calc
      OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)
          = OneModePaperBridge.minusSeq a b n * (c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
              rw [mul_div_assoc]
      _ ≤ OneModePaperBridge.minusSeq a b n * (c ^ 2 * c ^ (2 * n)) := hcmp
      _ = c ^ 2 * (OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) := by ring

private theorem weight_le_csq_mul_pow
    {c : ℝ}
    (hc : 0 ≤ c)
    (n : ℕ) :
    OneModeKernel.weight c n ≤ c ^ 2 * c ^ (2 * n) := by
  unfold OneModeKernel.weight
  have hcoeff : ((n : ℝ) / (n + 1 : ℝ)) ≤ 1 := by
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    exact (div_le_iff₀ hpos).2 (by nlinarith)
  have hpow_nonneg : 0 ≤ c ^ 2 * c ^ (2 * n) := by positivity
  have hpow :
      c ^ (2 * n + 2) = c ^ 2 * c ^ (2 * n) := by
    rw [show 2 * n + 2 = 2 + 2 * n by omega, pow_add]
  rw [hpow]
  calc
    ((n : ℝ) / (n + 1 : ℝ)) * (c ^ 2 * c ^ (2 * n))
        ≤ 1 * (c ^ 2 * c ^ (2 * n)) := by
          exact mul_le_mul_of_nonneg_right hcoeff hpow_nonneg
    _ = c ^ 2 * c ^ (2 * n) := by ring

private theorem minusWeight_summable_of_minusSigma
    {a b : ℕ → ℂ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hMinusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * c ^ (2 * n))) :
    Summable
      (fun n : ℕ => OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) := by
  have hScaled : Summable (fun n : ℕ => c ^ 2 * (OneModePaperBridge.minusSeq a b n * c ^ (2 * n))) :=
    hMinusSigma.mul_left (c ^ 2)
  refine Summable.of_nonneg_of_le ?_ ?_ hScaled
  · intro n
    unfold OneModeKernel.weight
    positivity [OneModePaperBridge.minusSeq_nonneg a b n, hc]
  · intro n
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left
        (weight_le_csq_mul_pow hc n)
        (OneModePaperBridge.minusSeq_nonneg a b n)

private theorem annulusDensity_nonneg_of_lt
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {ρ : ℝ}
    (hcr : (cValueQ : ℝ) < ρ)
    (hρ1 : ρ < 1) :
    0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  have hCircleNonneg :
      0 ≤ paper.circleGap ρ :=
    OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper hcr hρ1
  unfold AnnulusIntegralReduction.annulusDensity
  have hρpos : 0 < ρ := lt_trans cValue_pos hcr
  nlinarith

private theorem annulusNonneg_subinterval
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {qA qB : ℚ}
    (hca : (cValueQ : ℝ) < (qA : ℝ))
    (hb1 : (qB : ℝ) < 1) :
    ∀ ρ ∈ Icc (qA : ℝ) (qB : ℝ),
      0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  intro ρ hρ
  exact annulusDensity_nonneg_of_lt paper
    (lt_of_lt_of_le hca hρ.1) (lt_of_le_of_lt hρ.2 hb1)

private theorem annulusNonneg_ae_subinterval
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {qA qB : ℚ}
    (hca : cValueQ ≤ qA)
    (hb1 : qB ≤ 1) :
    ∀ᵐ ρ ∂volume.restrict (Icc (qA : ℝ) (qB : ℝ)),
      0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  have hIoo :
      ∀ᵐ ρ ∂volume.restrict (Ioo (qA : ℝ) (qB : ℝ)),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun ρ hρ => by
      have hcaR : (cValueQ : ℝ) ≤ (qA : ℝ) := by exact_mod_cast hca
      have hb1R : (qB : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hb1
      have hcr : (cValueQ : ℝ) < ρ := lt_of_le_of_lt hcaR hρ.1
      have hρ1 : ρ < 1 := lt_of_lt_of_le hρ.2 hb1R
      exact annulusDensity_nonneg_of_lt paper hcr hρ1
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
  exact hIoo

private theorem branchSplit_lt_one : PaperAxioms.branchSplit (cValueQ : ℝ) < 1 := by
  have hsplit_nonneg : 0 ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    unfold PaperAxioms.branchSplit
    exact mul_nonneg cValue_pos.le (Real.sqrt_nonneg _)
  have hsq :
      (PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2 < (1 : ℝ) ^ 2 := by
    unfold PaperAxioms.branchSplit
    have hsqrt_sq : Real.sqrt (4 / 3 : ℝ) ^ 2 = 4 / 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have hrat : (4 : ℚ) * cValueQ ^ 2 < 3 := by
      native_decide
    have hratR : (4 : ℝ) * (cValueQ : ℝ) ^ 2 < 3 := by
      exact_mod_cast hrat
    nlinarith [hsqrt_sq]
  nlinarith

private abbrev cSqQ : ℚ := 127021672801 / 1000000000000

private theorem mode4_tau_lower :
    OneModeTail.tau (4 - 1) ≤ (cValueQ : ℝ) ^ 2 / (mode4StopQ : ℝ) ^ 2 := by
  norm_num [OneModeTail.tau, cValueQ, mode4StopQ, branch1_box_0005]

private theorem mode4_tau_upper :
    (cValueQ : ℝ) ^ 2 / (mode4StartQ : ℝ) ^ 2 ≤ OneModeTail.tau 4 := by
  norm_num [OneModeTail.tau, cValueQ, mode4StartQ, branch1_box_0004]

private theorem mode3_tau_lower :
    OneModeTail.tau (3 - 1) ≤ (cValueQ : ℝ) ^ 2 / (mode3StopQ : ℝ) ^ 2 := by
  norm_num [OneModeTail.tau, cValueQ, mode3StopQ, branch1_box_0011]

private theorem mode3_tau_upper :
    (cValueQ : ℝ) ^ 2 / (mode3StartQ : ℝ) ^ 2 ≤ OneModeTail.tau 3 := by
  norm_num [OneModeTail.tau, cValueQ, mode3StartQ, branch1_box_0007]

private theorem mode2_tau_lower :
    OneModeTail.tau (2 - 1) ≤ (cValueQ : ℝ) ^ 2 / (mode2StopQ : ℝ) ^ 2 := by
  norm_num [OneModeTail.tau, cValueQ, mode2StopQ, branch1_box_0031]

private theorem mode2_tau_upper :
    (cValueQ : ℝ) ^ 2 / (mode2StartQ : ℝ) ^ 2 ≤ OneModeTail.tau 2 := by
  norm_num [OneModeTail.tau, cValueQ, mode2StartQ, branch1_box_0013]

private theorem mode1_tau_lower :
    OneModeTail.tau (1 - 1) ≤ (cValueQ : ℝ) ^ 2 / (mode1StopQ : ℝ) ^ 2 := by
  have hnonneg : 0 ≤ (cValueQ : ℝ) ^ 2 / (mode1StopQ : ℝ) ^ 2 := by positivity
  simpa [OneModeTail.tau] using hnonneg

private theorem mode1_tau_upper :
    (cValueQ : ℝ) ^ 2 / (mode1StartQ : ℝ) ^ 2 ≤ OneModeTail.tau 1 := by
  norm_num [OneModeTail.tau, cValueQ, mode1StartQ, branch2_box_0000]

private theorem c_lt_mode4Start : (cValueQ : ℝ) < (mode4StartQ : ℝ) := by
  exact_mod_cast (show cValueQ < mode4StartQ by native_decide)

private theorem c_lt_fallbackBStart : (cValueQ : ℝ) < (fallbackBStartQ : ℝ) := by
  exact_mod_cast (show cValueQ < fallbackBStartQ by native_decide)

private theorem c_lt_mode3Start : (cValueQ : ℝ) < (mode3StartQ : ℝ) := by
  exact_mod_cast (show cValueQ < mode3StartQ by native_decide)

private theorem c_lt_fallbackCStart : (cValueQ : ℝ) < (fallbackCStartQ : ℝ) := by
  exact_mod_cast (show cValueQ < fallbackCStartQ by native_decide)

private theorem c_lt_mode2Start : (cValueQ : ℝ) < (mode2StartQ : ℝ) := by
  exact_mod_cast (show cValueQ < mode2StartQ by native_decide)

private theorem c_lt_mode1Start : (cValueQ : ℝ) < (mode1StartQ : ℝ) := by
  exact_mod_cast (show cValueQ < mode1StartQ by native_decide)

private theorem mode4Stop_lt_one : (mode4StopQ : ℝ) < 1 := by
  exact_mod_cast (show mode4StopQ < 1 by native_decide)

private theorem mode3Stop_lt_one : (mode3StopQ : ℝ) < 1 := by
  exact_mod_cast (show mode3StopQ < 1 by native_decide)

private theorem mode2Stop_lt_one : (mode2StopQ : ℝ) < 1 := by
  exact_mod_cast (show mode2StopQ < 1 by native_decide)

private theorem mode1Stop_lt_one : (mode1StopQ : ℝ) < 1 := by
  exact_mod_cast (show mode1StopQ < 1 by native_decide)

private theorem mode1Start_le_one : mode1StartQ ≤ 1 := by
  exact le_trans mode1Start_le_mode1Stop mode1Stop_le_one

private theorem mode1Start_lt_one : (mode1StartQ : ℝ) < 1 := by
  exact lt_of_le_of_lt (by exact_mod_cast mode1Start_le_mode1Stop) mode1Stop_lt_one

private theorem fallbackAStop_lt_branchSplit : (fallbackAStopQ : ℝ) < PaperAxioms.branchSplit (cValueQ : ℝ) := by
  have hnonneg : 0 ≤ (fallbackAStopQ : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ fallbackAStopQ by native_decide)
  have hsplit_nonneg : 0 ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    unfold PaperAxioms.branchSplit
    exact mul_nonneg cValue_pos.le (Real.sqrt_nonneg _)
  have hsq :
      ((fallbackAStopQ : ℝ) ^ 2) < (PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2 := by
    unfold PaperAxioms.branchSplit
    have hsqrt_sq : Real.sqrt (4 / 3 : ℝ) ^ 2 = 4 / 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have hrat : 3 * fallbackAStopQ ^ 2 < 4 * cValueQ ^ 2 := by
      native_decide
    have hratR : (3 : ℝ) * (fallbackAStopQ : ℝ) ^ 2 < 4 * (cValueQ : ℝ) ^ 2 := by
      exact_mod_cast hrat
    have hdivQ : fallbackAStopQ ^ 2 < (4 * cValueQ ^ 2) / 3 := by
      native_decide
    have hdiv : ((fallbackAStopQ : ℝ) ^ 2) < (4 * (cValueQ : ℝ) ^ 2) / 3 := by
      exact_mod_cast hdivQ
    calc
      ((fallbackAStopQ : ℝ) ^ 2) < (4 / 3 : ℝ) * (cValueQ : ℝ) ^ 2 := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = ((cValueQ : ℝ) * Real.sqrt (4 / 3 : ℝ)) ^ 2 := by
        nlinarith [hsqrt_sq]
  have hsqrt_lt :
      Real.sqrt ((fallbackAStopQ : ℝ) ^ 2) <
        Real.sqrt ((PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2) := by
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  have hsqrt_lt_abs :
      (fallbackAStopQ : ℝ) < |PaperAxioms.branchSplit (cValueQ : ℝ)| := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt_lt
  have hsplit_abs_le :
      |PaperAxioms.branchSplit (cValueQ : ℝ)| ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    exact le_of_eq (abs_of_nonneg hsplit_nonneg)
  exact lt_of_lt_of_le hsqrt_lt_abs hsplit_abs_le

private theorem fallbackBStop_lt_branchSplit : (fallbackBStopQ : ℝ) < PaperAxioms.branchSplit (cValueQ : ℝ) := by
  have hnonneg : 0 ≤ (fallbackBStopQ : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ fallbackBStopQ by native_decide)
  have hsplit_nonneg : 0 ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    unfold PaperAxioms.branchSplit
    exact mul_nonneg cValue_pos.le (Real.sqrt_nonneg _)
  have hsq :
      ((fallbackBStopQ : ℝ) ^ 2) < (PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2 := by
    unfold PaperAxioms.branchSplit
    have hsqrt_sq : Real.sqrt (4 / 3 : ℝ) ^ 2 = 4 / 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have hrat : 3 * fallbackBStopQ ^ 2 < 4 * cValueQ ^ 2 := by
      native_decide
    have hratR : (3 : ℝ) * (fallbackBStopQ : ℝ) ^ 2 < 4 * (cValueQ : ℝ) ^ 2 := by
      exact_mod_cast hrat
    have hdivQ : fallbackBStopQ ^ 2 < (4 * cValueQ ^ 2) / 3 := by
      native_decide
    have hdiv : ((fallbackBStopQ : ℝ) ^ 2) < (4 * (cValueQ : ℝ) ^ 2) / 3 := by
      exact_mod_cast hdivQ
    calc
      ((fallbackBStopQ : ℝ) ^ 2) < (4 / 3 : ℝ) * (cValueQ : ℝ) ^ 2 := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = ((cValueQ : ℝ) * Real.sqrt (4 / 3 : ℝ)) ^ 2 := by
        nlinarith [hsqrt_sq]
  have hsqrt_lt :
      Real.sqrt ((fallbackBStopQ : ℝ) ^ 2) <
        Real.sqrt ((PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2) := by
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  have hsqrt_lt_abs :
      (fallbackBStopQ : ℝ) < |PaperAxioms.branchSplit (cValueQ : ℝ)| := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt_lt
  have hsplit_abs_le :
      |PaperAxioms.branchSplit (cValueQ : ℝ)| ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    exact le_of_eq (abs_of_nonneg hsplit_nonneg)
  exact lt_of_lt_of_le hsqrt_lt_abs hsplit_abs_le

private theorem fallbackCStop_lt_branchSplit : (fallbackCStopQ : ℝ) < PaperAxioms.branchSplit (cValueQ : ℝ) := by
  have hnonneg : 0 ≤ (fallbackCStopQ : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ fallbackCStopQ by native_decide)
  have hsplit_nonneg : 0 ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    unfold PaperAxioms.branchSplit
    exact mul_nonneg cValue_pos.le (Real.sqrt_nonneg _)
  have hsq :
      ((fallbackCStopQ : ℝ) ^ 2) < (PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2 := by
    unfold PaperAxioms.branchSplit
    have hsqrt_sq : Real.sqrt (4 / 3 : ℝ) ^ 2 = 4 / 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have hrat : 3 * fallbackCStopQ ^ 2 < 4 * cValueQ ^ 2 := by
      native_decide
    have hratR : (3 : ℝ) * (fallbackCStopQ : ℝ) ^ 2 < 4 * (cValueQ : ℝ) ^ 2 := by
      exact_mod_cast hrat
    have hdivQ : fallbackCStopQ ^ 2 < (4 * cValueQ ^ 2) / 3 := by
      native_decide
    have hdiv : ((fallbackCStopQ : ℝ) ^ 2) < (4 * (cValueQ : ℝ) ^ 2) / 3 := by
      exact_mod_cast hdivQ
    calc
      ((fallbackCStopQ : ℝ) ^ 2) < (4 / 3 : ℝ) * (cValueQ : ℝ) ^ 2 := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = ((cValueQ : ℝ) * Real.sqrt (4 / 3 : ℝ)) ^ 2 := by
        nlinarith [hsqrt_sq]
  have hsqrt_lt :
      Real.sqrt ((fallbackCStopQ : ℝ) ^ 2) <
        Real.sqrt ((PaperAxioms.branchSplit (cValueQ : ℝ)) ^ 2) := by
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  have hsqrt_lt_abs :
      (fallbackCStopQ : ℝ) < |PaperAxioms.branchSplit (cValueQ : ℝ)| := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt_lt
  have hsplit_abs_le :
      |PaperAxioms.branchSplit (cValueQ : ℝ)| ≤ PaperAxioms.branchSplit (cValueQ : ℝ) := by
    exact le_of_eq (abs_of_nonneg hsplit_nonneg)
  exact lt_of_lt_of_le hsqrt_lt_abs hsplit_abs_le

private theorem fallbackA_mass_mul_le_slice_of_pointwise
    (K : ℝ → ℝ → ℝ)
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    (hPoint :
      ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < PaperAxioms.branchSplit (cValueQ : ℝ) →
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ * innerExcess ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (cValueQ : ℝ) (1 : ℝ)) :
    (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice paper.circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) := by
  have hScalarInt :
      IntervalIntegrable
        (fun ρ =>
          Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ)
        volume (cValueQ : ℝ) (fallbackAStopQ : ℝ) := by
    exact WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      (K := K) (c := (cValueQ : ℝ)) (a := (cValueQ : ℝ)) (b := (fallbackAStopQ : ℝ))
      cValue_pos (by exact_mod_cast c_le_fallbackAStop) le_rfl
      (show (fallbackAStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackAStop_le_one)
      paper.eq7_paperK_formula
  have hMass :
      (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ)) ≤
        ∫ ρ in (cValueQ : ℝ)..(fallbackAStopQ : ℝ),
          Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ := by
    refine WangBoxQ.branch1TotalMassQ_cast_le_intervalIntegral
      K cValueQ fallbackAStopQ fallbackABoxes
      cValue_pos c_le_fallbackAStop fallbackABoxes_ordered fallbackABoxes_hi_le
      fallbackABoxes_valid (fallbackABoxes_kSqUpper (K := K) (a := a) (b := b) paper) ?_ hScalarInt
    intro ρ _
    exact WangPaperSideConditions.paperLambda_pos (K := K) (c := (cValueQ : ℝ)) (ρ := ρ)
  have hPointwise :
      ∀ᵐ ρ ∂volume.restrict (Icc (cValueQ : ℝ) (fallbackAStopQ : ℝ)),
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoc :
        ∀ᵐ ρ ∂volume.restrict (Ioc (cValueQ : ℝ) (fallbackAStopQ : ℝ)),
          Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
              innerExcess ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun ρ hρ =>
        hPoint hρ.1 (lt_of_le_of_lt hρ.2 fallbackAStop_lt_branchSplit)
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hIoc
    exact hIoc
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
    (a := (cValueQ : ℝ))
    (b := (fallbackAStopQ : ℝ))
    (modeIntegrand := fun ρ =>
      Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ)
    (circleGap := paper.circleGap)
    (mass := (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ)))
    (by exact_mod_cast c_le_fallbackAStop)
    fallbackA_mass_nonneg hMass hScalarInt
    (annulusInt_subinterval hAnnInt le_rfl c_le_fallbackAStop fallbackAStop_le_one)
    hPointwise
    (annulusNonneg_ae_subinterval paper le_rfl fallbackAStop_le_one)

theorem direct_target_reduction
    (K : ℝ → ℝ → ℝ)
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    (hPlusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.plusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < 1 →
        Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (cValueQ : ℝ) (1 : ℝ)) :
    PaperAxioms.diskExcess paper.circleGap (cValueQ : ℝ) ≤
      AnnulusIntegralReduction.annulusSlice paper.circleGap (cValueQ : ℝ) (1 : ℝ) := by
  let circleGap := paper.circleGap
  let innerExcess := PaperAxioms.diskExcess circleGap (cValueQ : ℝ)
  have hPlusDisk :
      Summable
        (fun n : ℕ =>
          OneModePaperBridge.plusSeq a b n * (cValueQ : ℝ) ^ (2 * n + 2) / (n + 1 : ℝ)) :=
    plusDisk_summable_of_plusSigma cValue_pos.le hPlusSigma
  have hMinusDisk :
      Summable
        (fun n : ℕ =>
          OneModePaperBridge.minusSeq a b n * (cValueQ : ℝ) ^ (2 * n + 2) / (n + 1 : ℝ)) :=
    minusDisk_summable_of_minusSigma cValue_pos.le hMinusSigmaC
  have hMinusWeight :
      Summable
        (fun n : ℕ =>
          OneModePaperBridge.minusSeq a b n * OneModeKernel.weight (cValueQ : ℝ) n) :=
    minusWeight_summable_of_minusSigma cValue_pos.le hMinusSigmaC
  have hInnerEq :
      innerExcess = OneModePaperBridge.innerSeriesExcess a b (cValueQ : ℝ) := by
    dsimp [innerExcess, circleGap]
    simpa [PaperAxioms.diskExcess] using
      OneModePaperBridge.annulusSlice_circleGap_eq_innerSeriesExcess
        paper cValue_pos.le cValue_lt_one hPlusDisk hPlusSigma hMinusSigmaC
  have hInnerLeSeries :
      innerExcess ≤ OneModePaperBridge.innerSeriesExcess a b (cValueQ : ℝ) :=
    le_of_eq hInnerEq
  have hEq4 :
      PaperAxioms.Eq4SigmaPlusBound
        (PaperAxioms.sigmaPlus a b) (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b)
        0 (cValueQ : ℝ) := by
    exact paper.eq4_sigmaPlus_bound (r := 0) (by norm_num) cValue_pos cValue_lt_one
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b (cValueQ : ℝ) ≤ PaperAxioms.sigmaMinus a b (cValueQ : ℝ) :=
    OneModePaperBridge.sigmaPlus_le_sigmaMinus_of_eq4 hEq4
  have hEq10 :
      PaperAxioms.Eq10Branch1Pointwise K (cValueQ : ℝ) innerExcess circleGap := by
    exact PaperAxioms.eq10_of_eq5_eq8_eq9
      cValue_pos branchSplit_lt_one
      paper.eq5_branch1_sigmaReduction
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
  have hEq10Density :
      ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < PaperAxioms.branchSplit (cValueQ : ℝ) →
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ * innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ := by
    intro ρ hcr hρsplit
    have hρpos : 0 < ρ := lt_trans cValue_pos hcr
    have hρnonneg : 0 ≤ 2 * ρ := by nlinarith [hρpos]
    have hScaled := mul_le_mul_of_nonneg_left (hEq10 hcr hρsplit) hρnonneg
    calc
      Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ * innerExcess
          = (2 * ρ) *
              (PaperAxioms.branch1PointwiseFactor (cValueQ : ℝ)
                (WangOuter.paperLambda K (cValueQ : ℝ)) ρ * innerExcess) := by
                  unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
                  ring
      _ ≤ (2 * ρ) * circleGap ρ := hScaled
      _ = AnnulusIntegralReduction.annulusDensity circleGap ρ := by rfl
  have hFallbackA :
      (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ) * innerExcess) ≤
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) := by
    simpa [circleGap] using
      fallbackA_mass_mul_le_slice_of_pointwise K paper hEq10Density hAnnInt
  have hMode4 :
      WangBoxQ.modeTotalMass 4 cValueQ mode4Boxes * innerExcess ≤
        AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) := by
    apply WangBoxQ.modeTotalMass_mul_le_annulusSlice
      (j := 4) (by norm_num) K cValueQ mode4StartQ mode4StopQ mode4Boxes
      cValue_pos c_le_mode4Start mode4Start_le_mode4Stop
      (show (mode4StopQ : ℝ) ≤ 1 by exact_mod_cast mode4Stop_le_one)
      mode4Boxes_ordered mode4Boxes_hi_le mode4Boxes_valid
      (mode4Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
      mode4_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      exact OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
        cValue_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInnerLeSeries
        paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hMinusSigma (mode := 4) (by norm_num)
        c_lt_mode4Start mode4Stop_lt_one mode4_tau_lower mode4_tau_upper hρ
    · exact annulusInt_subinterval hAnnInt c_le_mode4Start mode4Start_le_mode4Stop mode4Stop_le_one
    · exact annulusNonneg_subinterval paper c_lt_mode4Start mode4Stop_lt_one
  have hFallbackB :
      (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackBBox : ℚ) : ℝ) * innerExcess) ≤
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) := by
    apply WangBoxQ.branch1WindowTotalMass_mul_le_annulusSlice
      K cValueQ fallbackBStartQ fallbackBStopQ fallbackBBox
      cValue_pos c_le_fallbackBStart fallbackBStart_le_fallbackBStop
      (show (fallbackBStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackBStop_le_one)
      fallbackBBox_ordered fallbackBBox_hi_le fallbackBBox_valid
      (fallbackBBox_kSqUpper (K := K) (a := a) (b := b) paper)
      fallbackB_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      have hcr : (cValueQ : ℝ) < ρ := lt_of_lt_of_le c_lt_fallbackBStart hρ.1
      exact hEq10Density hcr (lt_of_le_of_lt hρ.2 fallbackBStop_lt_branchSplit)
    · exact annulusInt_subinterval hAnnInt c_le_fallbackBStart fallbackBStart_le_fallbackBStop fallbackBStop_le_one
    · exact annulusNonneg_subinterval paper c_lt_fallbackBStart
        (lt_trans fallbackBStop_lt_branchSplit branchSplit_lt_one)
  have hMode3 :
      WangBoxQ.modeTotalMass 3 cValueQ mode3Boxes * innerExcess ≤
        AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) := by
    apply WangBoxQ.modeTotalMass_mul_le_annulusSlice
      (j := 3) (by norm_num) K cValueQ mode3StartQ mode3StopQ mode3Boxes
      cValue_pos c_le_mode3Start mode3Start_le_mode3Stop
      (show (mode3StopQ : ℝ) ≤ 1 by exact_mod_cast mode3Stop_le_one)
      mode3Boxes_ordered mode3Boxes_hi_le mode3Boxes_valid
      (mode3Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
      mode3_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      exact OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
        cValue_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInnerLeSeries
        paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hMinusSigma (mode := 3) (by norm_num)
        c_lt_mode3Start mode3Stop_lt_one mode3_tau_lower mode3_tau_upper hρ
    · exact annulusInt_subinterval hAnnInt c_le_mode3Start mode3Start_le_mode3Stop mode3Stop_le_one
    · exact annulusNonneg_subinterval paper c_lt_mode3Start mode3Stop_lt_one
  have hFallbackC :
      (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackCBox : ℚ) : ℝ) * innerExcess) ≤
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) := by
    apply WangBoxQ.branch1WindowTotalMass_mul_le_annulusSlice
      K cValueQ fallbackCStartQ fallbackCStopQ fallbackCBox
      cValue_pos c_le_fallbackCStart fallbackCStart_le_fallbackCStop
      (show (fallbackCStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackCStop_le_one)
      fallbackCBox_ordered fallbackCBox_hi_le fallbackCBox_valid
      (fallbackCBox_kSqUpper (K := K) (a := a) (b := b) paper)
      fallbackC_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      have hcr : (cValueQ : ℝ) < ρ := lt_of_lt_of_le c_lt_fallbackCStart hρ.1
      exact hEq10Density hcr (lt_of_le_of_lt hρ.2 fallbackCStop_lt_branchSplit)
    · exact annulusInt_subinterval hAnnInt c_le_fallbackCStart fallbackCStart_le_fallbackCStop fallbackCStop_le_one
    · exact annulusNonneg_subinterval paper c_lt_fallbackCStart
        (lt_trans fallbackCStop_lt_branchSplit branchSplit_lt_one)
  have hMode2 :
      WangBoxQ.modeTotalMass 2 cValueQ mode2Boxes * innerExcess ≤
        AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
    apply WangBoxQ.modeTotalMass_mul_le_annulusSlice
      (j := 2) (by norm_num) K cValueQ mode2StartQ mode2StopQ mode2Boxes
      cValue_pos c_le_mode2Start mode2Start_le_mode2Stop
      (show (mode2StopQ : ℝ) ≤ 1 by exact_mod_cast mode2Stop_le_one)
      mode2Boxes_ordered mode2Boxes_hi_le mode2Boxes_valid
      (mode2Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
      mode2_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      exact OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
        cValue_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInnerLeSeries
        paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hMinusSigma (mode := 2) (by norm_num)
        c_lt_mode2Start mode2Stop_lt_one mode2_tau_lower mode2_tau_upper hρ
    · exact annulusInt_subinterval hAnnInt c_le_mode2Start mode2Start_le_mode2Stop mode2Stop_le_one
    · exact annulusNonneg_subinterval paper c_lt_mode2Start mode2Stop_lt_one
  have hMode1 :
      WangBoxQ.modeTotalMass 1 cValueQ mode1Boxes * innerExcess ≤
        AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) := by
    apply WangBoxQ.modeTotalMass_mul_le_annulusSlice
      (j := 1) (by norm_num) K cValueQ mode1StartQ mode1StopQ mode1Boxes
      cValue_pos c_le_mode1Start mode1Start_le_mode1Stop
      (show (mode1StopQ : ℝ) ≤ 1 by exact_mod_cast mode1Stop_le_one)
      (by simpa [mode1StartQ, mode1Boxes] using branch2Boxes_ordered)
      mode1Boxes_hi_le mode1Boxes_valid
      (mode1Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
      mode1_mass_nonneg paper.eq7_paperK_formula
    · intro ρ hρ
      exact OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
        cValue_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight hPlusLeMinus hInnerLeSeries
        paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hMinusSigma (mode := 1) (by norm_num)
        c_lt_mode1Start mode1Stop_lt_one mode1_tau_lower mode1_tau_upper hρ
    · exact annulusInt_subinterval hAnnInt c_le_mode1Start mode1Start_le_mode1Stop mode1Stop_le_one
    · exact annulusNonneg_subinterval paper c_lt_mode1Start mode1Stop_lt_one
  have hGapNonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StartQ : ℝ) := by
    refine AnnulusIntegralReduction.annulusSlice_nonneg ?_ ?_
    · exact_mod_cast mode2Stop_le_mode1Start
    · exact annulusNonneg_subinterval paper
        (lt_of_lt_of_le c_lt_mode2Start (by exact_mod_cast mode2Start_le_mode2Stop))
        mode1Start_lt_one
  have hTailNonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice circleGap (mode1StopQ : ℝ) (1 : ℝ) := by
    have hTailNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Icc (mode1StopQ : ℝ) (1 : ℝ)),
          0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ := by
      simpa [circleGap] using
        (annulusNonneg_ae_subinterval (qA := mode1StopQ) (qB := (1 : ℚ)) paper
          (le_trans c_le_mode1Start mode1Start_le_mode1Stop)
          (show (1 : ℚ) ≤ 1 by norm_num))
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae (by exact_mod_cast mode1Stop_le_one)
      hTailNonnegAE
  have hIntFallbackA :=
    annulusInt_subinterval hAnnInt le_rfl c_le_fallbackAStop fallbackAStop_le_one
  have hIntMode4 :=
    annulusInt_subinterval hAnnInt c_le_mode4Start mode4Start_le_mode4Stop mode4Stop_le_one
  have hIntFallbackB :=
    annulusInt_subinterval hAnnInt c_le_fallbackBStart fallbackBStart_le_fallbackBStop fallbackBStop_le_one
  have hIntMode3 :=
    annulusInt_subinterval hAnnInt c_le_mode3Start mode3Start_le_mode3Stop mode3Stop_le_one
  have hIntFallbackC :=
    annulusInt_subinterval hAnnInt c_le_fallbackCStart fallbackCStart_le_fallbackCStop fallbackCStop_le_one
  have hIntMode2 :=
    annulusInt_subinterval hAnnInt c_le_mode2Start mode2Start_le_mode2Stop mode2Stop_le_one
  have hIntGap :=
    annulusInt_subinterval hAnnInt
      (le_trans c_le_mode2Start mode2Start_le_mode2Stop) mode2Stop_le_mode1Start mode1Start_le_one
  have hIntMode1 :=
    annulusInt_subinterval hAnnInt c_le_mode1Start mode1Start_le_mode1Stop mode1Stop_le_one
  have hIntTail :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode1StopQ : ℝ) (1 : ℝ) := by
    simpa using
      (annulusInt_subinterval hAnnInt
        (le_trans c_le_mode1Start mode1Start_le_mode1Stop) mode1Stop_le_one
        (show (1 : ℚ) ≤ 1 by norm_num))
  have hIntMode2ToOne :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode2StopQ : ℝ) (1 : ℝ) := by
    simpa using
      (annulusInt_subinterval hAnnInt
        (le_trans c_le_mode2Start mode2Start_le_mode2Stop) mode2Stop_le_one
        (show (1 : ℚ) ≤ 1 by norm_num))
  have hSlicesToMode2 :
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) =
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) := by
    have hA4 :
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) =
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode4StopQ : ℝ) := by
      simpa [fallbackA_mode4_adj] using
        (AnnulusIntegralReduction.annulusSlice_add_adjacent hIntFallbackA hIntMode4)
    have hAB :
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode4StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) =
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackBStopQ : ℝ) := by
      simpa [mode4_fallbackB_adj] using
        (AnnulusIntegralReduction.annulusSlice_add_adjacent
          (annulusInt_subinterval hAnnInt le_rfl (le_trans c_le_mode4Start mode4Start_le_mode4Stop) mode4Stop_le_one)
          hIntFallbackB)
    have hABC :
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackBStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) =
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode3StopQ : ℝ) := by
      simpa [fallbackB_mode3_adj] using
        (AnnulusIntegralReduction.annulusSlice_add_adjacent
          (annulusInt_subinterval hAnnInt le_rfl (le_trans c_le_fallbackBStart fallbackBStart_le_fallbackBStop) fallbackBStop_le_one)
          hIntMode3)
    have hABCD :
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode3StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) =
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackCStopQ : ℝ) := by
      simpa [mode3_fallbackC_adj] using
        (AnnulusIntegralReduction.annulusSlice_add_adjacent
          (annulusInt_subinterval hAnnInt le_rfl (le_trans c_le_mode3Start mode3Start_le_mode3Stop) mode3Stop_le_one)
          hIntFallbackC)
    have hABCDE :
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackCStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) =
        AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) := by
      simpa [fallbackC_mode2_adj] using
        (AnnulusIntegralReduction.annulusSlice_add_adjacent
          (annulusInt_subinterval hAnnInt le_rfl (le_trans c_le_fallbackCStart fallbackCStart_le_fallbackCStop) fallbackCStop_le_one)
          hIntMode2)
    calc
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ)
          = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode4StopQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
                rw [hA4]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackBStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
              rw [hAB]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode3StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
              rw [hABC]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackCStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
              rw [hABCD]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) := by
              rw [hABCDE]
  have hGapMode1 :
      AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StartQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) =
      AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StopQ : ℝ) := by
    simpa using
      (AnnulusIntegralReduction.annulusSlice_add_adjacent hIntGap hIntMode1)
  have hGapTail :
      AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode1StopQ : ℝ) (1 : ℝ) =
      AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (1 : ℝ) := by
    simpa using
      (AnnulusIntegralReduction.annulusSlice_add_adjacent
        (annulusInt_subinterval hAnnInt
          (le_trans c_le_mode2Start mode2Start_le_mode2Stop)
          (le_trans mode2Stop_le_mode1Start mode1Start_le_mode1Stop) mode1Stop_le_one)
        hIntTail)
  have hOuterBound :
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) +
        AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (1 : ℝ) := by
    calc
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) +
          AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ)
          ≤ AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StartQ : ℝ) +
              AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) := by
                rw [hSlicesToMode2]
                nlinarith
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StopQ : ℝ) := by
              rw [add_assoc, hGapMode1]
      _ ≤ AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (mode1StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode1StopQ : ℝ) (1 : ℝ) := by
              nlinarith [hTailNonneg]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (mode2StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StopQ : ℝ) (1 : ℝ) := by
              rw [add_assoc, hGapTail]
      _ = AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (1 : ℝ) := by
              exact AnnulusIntegralReduction.annulusSlice_add_adjacent
                (annulusInt_subinterval hAnnInt le_rfl (le_trans c_le_mode2Start mode2Start_le_mode2Stop) mode2Stop_le_one)
                hIntMode2ToOne
  by_cases hInnerNonneg : 0 ≤ innerExcess
  · have hScaled :
        innerExcess ≤ (hybridTotalMassQ : ℝ) * innerExcess := by
      simpa [hybridTotalMassQ] using
        mul_le_mul_of_nonneg_right hybridTotalMass_ge_one hInnerNonneg
    have hMassSum :
        ((hybridTotalMassQ : ℝ) * innerExcess)
          = (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ) * innerExcess) +
              WangBoxQ.modeTotalMass 4 cValueQ mode4Boxes * innerExcess +
              (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackBBox : ℚ) : ℝ) * innerExcess) +
              WangBoxQ.modeTotalMass 3 cValueQ mode3Boxes * innerExcess +
              (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackCBox : ℚ) : ℝ) * innerExcess) +
              WangBoxQ.modeTotalMass 2 cValueQ mode2Boxes * innerExcess +
              WangBoxQ.modeTotalMass 1 cValueQ mode1Boxes * innerExcess := by
      simp [hybridTotalMassQ, WangBoxQ.modeTotalMassQ_cast_eq_modeTotalMass]
      ring
    calc
      innerExcess ≤ (hybridTotalMassQ : ℝ) * innerExcess := hScaled
      _ = (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ) * innerExcess) +
            WangBoxQ.modeTotalMass 4 cValueQ mode4Boxes * innerExcess +
            (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackBBox : ℚ) : ℝ) * innerExcess) +
            WangBoxQ.modeTotalMass 3 cValueQ mode3Boxes * innerExcess +
            (((WangBoxQ.totalMassQ Branch.one cValueQ fallbackCBox : ℚ) : ℝ) * innerExcess) +
            WangBoxQ.modeTotalMass 2 cValueQ mode2Boxes * innerExcess +
            WangBoxQ.modeTotalMass 1 cValueQ mode1Boxes * innerExcess := hMassSum
      _ ≤ AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) +
            AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) := by
              gcongr
      _ ≤ AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (1 : ℝ) := hOuterBound
  · have hInnerNonpos : innerExcess ≤ 0 := le_of_not_ge hInnerNonneg
    have hOuterNonneg :
        0 ≤ AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (1 : ℝ) := by
      have hOuterNonnegAE :
          ∀ᵐ ρ ∂volume.restrict (Icc (cValueQ : ℝ) (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ := by
        simpa [circleGap] using
          (annulusNonneg_ae_subinterval (qA := cValueQ) (qB := (1 : ℚ)) paper
            le_rfl (show (1 : ℚ) ≤ 1 by norm_num))
      exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae cValue_lt_one.le hOuterNonnegAE
    exact le_trans hInnerNonpos hOuterNonneg

theorem direct_disk_vs_annulus
    (K : ℝ → ℝ → ℝ)
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    (hPlusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.plusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < 1 →
        Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (cValueQ : ℝ) (1 : ℝ)) :
    AnnulusIntegralReduction.annulusSlice paper.circleGap 0 (cValueQ : ℝ) ≤
      AnnulusIntegralReduction.annulusSlice paper.circleGap (cValueQ : ℝ) (1 : ℝ) := by
  exact direct_target_reduction K paper
    hPlusSigma hMinusSigmaC hMinusSigma hAnnInt

end KorenblumProofSearch3.V38
