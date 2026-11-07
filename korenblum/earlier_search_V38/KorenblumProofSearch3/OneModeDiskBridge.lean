import Mathlib.Analysis.Normed.Group.FunctionSeries
import KorenblumProofSearch3.OneModeRadialIntegral

open MeasureTheory
open TopologicalSpace
open scoped Topology

noncomputable section

namespace KorenblumProofSearch3

namespace OneModeSeries

/-- Zero out the `n = 0` coefficient while leaving the tail unchanged. -/
def tailSeq (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else u n

theorem tailSeq_nonneg
    {u : ℕ → ℝ}
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n) :
    ∀ n, 0 ≤ tailSeq u n := by
  intro n
  by_cases hn : n = 0
  · simp [tailSeq, hn]
  · simp [tailSeq, hn, hu n (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))]

theorem summable_sigma_tail_of_summable_sigma
    {u : ℕ → ℝ}
    {s : ℝ}
    (hSigma : Summable (fun n : ℕ => u n * s ^ (2 * n))) :
    Summable (fun n : ℕ => tailSeq u n * s ^ (2 * n)) := by
  refine hSigma.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [tailSeq, hn0]

theorem summable_disk_tail_of_summable_disk
    {u : ℕ → ℝ}
    {c : ℝ}
    (hDisk : Summable (fun n : ℕ => u n * c ^ (2 * n + 2) / (n + 1 : ℝ))) :
    Summable (fun n : ℕ => tailSeq u n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
  refine hDisk.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [tailSeq, hn0]

theorem sigmaSeq_eq_head_add_tail
    {u : ℕ → ℝ}
    {s : ℝ}
    (hSigma : Summable (fun n : ℕ => u n * s ^ (2 * n))) :
    sigmaSeq u s = u 0 + sigmaSeq (tailSeq u) s := by
  unfold sigmaSeq
  rw [hSigma.tsum_eq_add_tsum_ite 0]
  have hTail :
      (∑' n : ℕ, ite (n = 0) 0 (u n * s ^ (2 * n))) =
        ∑' n : ℕ, tailSeq u n * s ^ (2 * n) := by
    refine tsum_congr ?_
    intro n
    by_cases hn : n = 0
    · simp [tailSeq, hn]
    · simp [tailSeq, hn]
  simpa using congrArg (u 0 + ·) hTail

theorem diskWeightedSeq_eq_head_add_tail
    {u : ℕ → ℝ}
    {c : ℝ}
    (hDisk : Summable (fun n : ℕ => u n * c ^ (2 * n + 2) / (n + 1 : ℝ))) :
    diskWeightedSeq u c = u 0 * c ^ 2 + diskWeightedSeq (tailSeq u) c := by
  unfold diskWeightedSeq
  rw [hDisk.tsum_eq_add_tsum_ite 0]
  have hTail :
      (∑' n : ℕ, ite (n = 0) 0 (u n * c ^ (2 * n + 2) / (n + 1 : ℝ))) =
        ∑' n : ℕ, tailSeq u n * c ^ (2 * n + 2) / (n + 1 : ℝ) := by
    refine tsum_congr ?_
    intro n
    by_cases hn : n = 0
    · simp [tailSeq, hn]
    · simp [tailSeq, hn]
  have hHead : u 0 * c ^ (2 * 0 + 2) / (0 + 1 : ℝ) = u 0 * c ^ 2 := by
    norm_num
  calc
    u 0 * c ^ (2 * 0 + 2) / (((0 : ℕ) : ℝ) + 1) +
        ∑' n : ℕ, ite (n = 0) 0 (u n * c ^ (2 * n + 2) / (n + 1 : ℝ))
        = u 0 * c ^ 2 + ∑' n : ℕ, ite (n = 0) 0 (u n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
            norm_num [hHead]
    _ = u 0 * c ^ 2 + ∑' n : ℕ, tailSeq u n * c ^ (2 * n + 2) / (n + 1 : ℝ) :=
          congrArg (fun x => u 0 * c ^ 2 + x) hTail

theorem summable_sigmaSeq_of_mem_Icc_of_nonneg_tail
    {u : ℕ → ℝ}
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n)))
    (hρ : ρ ∈ Set.Icc 0 c) :
    Summable (fun n : ℕ => u n * ρ ^ (2 * n)) := by
  let v := tailSeq u
  have hSigmaV : Summable (fun n : ℕ => v n * c ^ (2 * n)) :=
    summable_sigma_tail_of_summable_sigma hSigma
  have hRhoV : Summable (fun n : ℕ => v n * ρ ^ (2 * n)) :=
    summable_sigmaSeq_of_mem_Icc hc (tailSeq_nonneg hu) hSigmaV hρ
  have hHead :
      Summable (fun n : ℕ => if n = 0 then u 0 * ρ ^ (2 * n) else 0) := by
    exact summable_of_finite_support <| (Set.finite_singleton 0).subset <| by
      intro n hn
      by_cases h : n = 0
      · simp [h]
      · simp [h] at hn
  refine (hHead.add hRhoV).congr ?_
  intro n
  by_cases hn : n = 0
  · simp [v, tailSeq, hn]
  · simp [v, tailSeq, hn]

theorem annulusDensity_sigmaSeq_continuousOn
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    ContinuousOn (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) (Set.uIcc 0 c) := by
  have hContTsum :
      ContinuousOn (fun ρ : ℝ => ∑' n : ℕ, densityTerm u n ρ) (Set.uIcc 0 c) := by
    refine continuousOn_tsum (fun n => (densityTerm u n).continuous.continuousOn) (hSigma.mul_left (2 * c)) ?_
    intro n ρ hρ
    have hρIcc : ρ ∈ Set.Icc 0 c := by
      simpa [Set.uIcc_of_le hc] using hρ
    have hCoeff : 0 ≤ 2 * u n := by nlinarith [hu n]
    have hNonneg :
        0 ≤ (2 * u n) * ρ ^ (2 * n + 1) := by
      exact mul_nonneg hCoeff (pow_nonneg hρIcc.1 _)
    calc
      ‖densityTerm u n ρ‖ = (2 * u n) * ρ ^ (2 * n + 1) := by
          rw [show densityTerm u n ρ = (2 * u n) * ρ ^ (2 * n + 1) by
            simp [densityTerm]
            ring_nf]
          rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      _ ≤ (2 * u n) * c ^ (2 * n + 1) := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρIcc.1 hρIcc.2 _) hCoeff
      _ = 2 * c * (u n * c ^ (2 * n)) := by ring
  refine hContTsum.congr ?_
  intro ρ hρ
  simpa using density_eq_tsum hc hu hSigma (by simpa [Set.uIcc_of_le hc] using hρ)

theorem annulusDensity_sigmaSeq_intervalIntegrable
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) volume 0 c := by
  have hCont :
      ContinuousOn (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) (Set.Icc 0 c) := by
    simpa [Set.uIcc_of_le hc] using annulusDensity_sigmaSeq_continuousOn hc hu hSigma
  exact hCont.intervalIntegrable_of_Icc hc

theorem annulusDensity_sigmaSeq_intervalIntegrable_of_nonneg_tail
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) volume 0 c := by
  let v := tailSeq u
  have hSigmaV : Summable (fun n : ℕ => v n * c ^ (2 * n)) :=
    summable_sigma_tail_of_summable_sigma hSigma
  have hContV :
      ContinuousOn (AnnulusIntegralReduction.annulusDensity (sigmaSeq v)) (Set.uIcc 0 c) :=
    annulusDensity_sigmaSeq_continuousOn hc (tailSeq_nonneg hu) hSigmaV
  have hContConst :
      ContinuousOn (fun ρ : ℝ => 2 * ρ * u 0) (Set.uIcc 0 c) := by
    fun_prop
  have hCont :
      ContinuousOn (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) (Set.uIcc 0 c) := by
    refine (hContConst.add hContV).congr ?_
    intro ρ hρ
    have hρIcc : ρ ∈ Set.Icc 0 c := by
      simpa [Set.uIcc_of_le hc] using hρ
    have hSigmaRho : Summable (fun n : ℕ => u n * ρ ^ (2 * n)) :=
      summable_sigmaSeq_of_mem_Icc_of_nonneg_tail hc hu hSigma hρIcc
    unfold AnnulusIntegralReduction.annulusDensity
    rw [sigmaSeq_eq_head_add_tail hSigmaRho]
    simp [v]
    ring_nf
  have hContIcc :
      ContinuousOn (AnnulusIntegralReduction.annulusDensity (sigmaSeq u)) (Set.Icc 0 c) := by
    simpa [Set.uIcc_of_le hc] using hCont
  exact hContIcc.intervalIntegrable_of_Icc hc

theorem annulusSlice_sigmaSeq_eq_diskWeightedSeq_of_nonneg_tail
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n)
    (hDisk : Summable (fun n : ℕ => u n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    AnnulusIntegralReduction.annulusSlice (sigmaSeq u) 0 c = diskWeightedSeq u c := by
  let v := tailSeq u
  have hSigmaV : Summable (fun n : ℕ => v n * c ^ (2 * n)) :=
    summable_sigma_tail_of_summable_sigma hSigma
  have hDiskV : Summable (fun n : ℕ => v n * c ^ (2 * n + 2) / (n + 1 : ℝ)) :=
    summable_disk_tail_of_summable_disk hDisk
  have hIntConst : IntervalIntegrable (fun ρ : ℝ => 2 * ρ * u 0) volume 0 c := by
    exact Continuous.intervalIntegrable (by fun_prop) 0 c
  have hIntTail :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity (sigmaSeq v)) volume 0 c :=
    annulusDensity_sigmaSeq_intervalIntegrable hc (tailSeq_nonneg hu) hSigmaV
  have hTail :
      AnnulusIntegralReduction.annulusSlice (sigmaSeq v) 0 c = diskWeightedSeq v c :=
    annulusSlice_sigmaSeq_eq_diskWeightedSeq hc (tailSeq_nonneg hu) hSigmaV
  unfold AnnulusIntegralReduction.annulusSlice
  calc
    ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (sigmaSeq u) ρ
        = ∫ ρ in 0..c, (2 * ρ * u 0) + AnnulusIntegralReduction.annulusDensity (sigmaSeq v) ρ := by
            refine intervalIntegral.integral_congr ?_
            intro ρ hρ
            have hρIcc : ρ ∈ Set.Icc 0 c := by
              simpa [Set.uIcc_of_le hc] using hρ
            have hSigmaRho : Summable (fun n : ℕ => u n * ρ ^ (2 * n)) :=
              summable_sigmaSeq_of_mem_Icc_of_nonneg_tail hc hu hSigma hρIcc
            unfold AnnulusIntegralReduction.annulusDensity
            rw [sigmaSeq_eq_head_add_tail hSigmaRho]
            simp [v]
            ring_nf
    _ = (∫ ρ in 0..c, 2 * ρ * u 0) +
          ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (sigmaSeq v) ρ := by
            rw [intervalIntegral.integral_add hIntConst hIntTail]
    _ = u 0 * c ^ 2 + diskWeightedSeq v c := by
          rw [show ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (sigmaSeq v) ρ =
              AnnulusIntegralReduction.annulusSlice (sigmaSeq v) 0 c by rfl]
          rw [hTail]
          have hConst :
              ∫ ρ in 0..c, 2 * ρ * u 0 = u 0 * c ^ 2 := by
            have hId : ∫ ρ in 0..c, (ρ : ℝ) = c ^ 2 / 2 := by
              simpa using (intervalIntegral.integral_pow (a := 0) (b := c) 1)
            have hRewrite :
                (fun ρ : ℝ => 2 * ρ * u 0) = fun ρ : ℝ => u 0 * (2 * ρ) := by
              ext ρ
              ring
            have hTwo :
                ∫ ρ in 0..c, (2 : ℝ) * ρ = c ^ 2 := by
              rw [intervalIntegral.integral_const_mul]
              rw [hId]
              ring
            calc
              ∫ ρ in 0..c, 2 * ρ * u 0
                  = u 0 * ∫ ρ in 0..c, (2 : ℝ) * ρ := by
                      rw [hRewrite, intervalIntegral.integral_const_mul]
              _ = u 0 * c ^ 2 := by rw [hTwo]
          rw [hConst]
    _ = diskWeightedSeq u c := by
          symm
          exact diskWeightedSeq_eq_head_add_tail hDisk

end OneModeSeries

end KorenblumProofSearch3
