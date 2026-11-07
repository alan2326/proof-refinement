import KorenblumProofSearch3.OneModeSeries
import KorenblumProofSearch3.AnnulusIntegralReduction

open MeasureTheory
open TopologicalSpace

noncomputable section

namespace KorenblumProofSearch3

namespace OneModeSeries

/--
Single-mode contribution to the radial density `2ρ Σ(ρ)`.
-/
def densityTerm (u : ℕ → ℝ) (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun ρ => 2 * ρ * (u n * ρ ^ (2 * n)), by continuity⟩

theorem summable_sigmaSeq_of_mem_Icc
    {u : ℕ → ℝ}
    {c ρ : ℝ}
    (_hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n)))
    (hρ : ρ ∈ Set.Icc 0 c) :
    Summable (fun n : ℕ => u n * ρ ^ (2 * n)) := by
  refine Summable.of_nonneg_of_le ?_ ?_ hSigma
  · intro n
    exact mul_nonneg (hu n) (pow_nonneg hρ.1 _)
  · intro n
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.1 hρ.2 _) (hu n)

theorem densityTerm_norm_restrict_le
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (n : ℕ)
    (hu : 0 ≤ u n) :
    ‖(densityTerm u n).restrict (⟨Set.uIcc 0 c, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      2 * c * (u n * c ^ (2 * n)) := by
  have hbound_nonneg : 0 ≤ 2 * c * (u n * c ^ (2 * n)) := by
    positivity
  rw [ContinuousMap.norm_le _ hbound_nonneg]
  intro x
  have hx : x.1 ∈ Set.Icc 0 c := by
    simpa [Set.uIcc_of_le hc] using x.2
  have hval :
      ‖(densityTerm u n) x.1‖ ≤ (2 * u n) * c ^ (2 * n + 1) := by
    have hnonneg' :
        0 ≤ (2 * u n) * x.1 ^ (2 * n + 1) := by
      exact mul_nonneg (by positivity) (pow_nonneg hx.1 _)
    rw [show (densityTerm u n) x.1 = (2 * u n) * x.1 ^ (2 * n + 1) by
      simp [densityTerm]
      ring_nf]
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) (by positivity)
  rw [show 2 * c * (u n * c ^ (2 * n)) = (2 * u n) * c ^ (2 * n + 1) by ring]
  simpa [ContinuousMap.restrict_apply] using hval

theorem summable_densityTerm_norm_restrict
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    Summable (fun n : ℕ =>
      ‖(densityTerm u n).restrict (⟨Set.uIcc 0 c, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (hSigma.mul_left (2 * c))
  · intro n
    exact norm_nonneg _
  · intro n
    exact densityTerm_norm_restrict_le hc n (hu n)

theorem density_eq_tsum
    {u : ℕ → ℝ}
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n)))
    (hρ : ρ ∈ Set.Icc 0 c) :
    AnnulusIntegralReduction.annulusDensity (sigmaSeq u) ρ =
      ∑' n : ℕ, densityTerm u n ρ := by
  have hSummRho :
      Summable (fun n : ℕ => u n * ρ ^ (2 * n)) :=
    summable_sigmaSeq_of_mem_Icc hc hu hSigma hρ
  calc
    AnnulusIntegralReduction.annulusDensity (sigmaSeq u) ρ
        = 2 * ρ * ∑' n : ℕ, u n * ρ ^ (2 * n) := by
            simp [AnnulusIntegralReduction.annulusDensity, sigmaSeq]
    _ = ∑' n : ℕ, 2 * ρ * (u n * ρ ^ (2 * n)) := by
          rw [← tsum_mul_left]
    _ = ∑' n : ℕ, densityTerm u n ρ := by
          refine tsum_congr ?_
          intro n
          simp [densityTerm]

theorem integral_densityTerm
    (u : ℕ → ℝ)
    (n : ℕ)
    (c : ℝ) :
    ∫ ρ in 0..c, densityTerm u n ρ = u n * c ^ (2 * n + 2) / (n + 1 : ℝ) := by
  have hEq :
      (fun ρ : ℝ => densityTerm u n ρ) =
        fun ρ : ℝ => (2 * u n) * ρ ^ (2 * n + 1) := by
    funext ρ
    simp [densityTerm]
    ring_nf
  rw [hEq, intervalIntegral.integral_const_mul, integral_pow]
  simp
  field_simp
  ring

theorem annulusSlice_sigmaSeq_eq_diskWeightedSeq
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 0 ≤ u n)
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    AnnulusIntegralReduction.annulusSlice (sigmaSeq u) 0 c = diskWeightedSeq u c := by
  unfold AnnulusIntegralReduction.annulusSlice diskWeightedSeq
  calc
    ∫ ρ in 0..c, AnnulusIntegralReduction.annulusDensity (sigmaSeq u) ρ
        = ∫ ρ in 0..c, ∑' n : ℕ, densityTerm u n ρ := by
            refine intervalIntegral.integral_congr ?_
            intro ρ hρ
            exact density_eq_tsum hc hu hSigma (by simpa [Set.uIcc_of_le hc] using hρ)
    _ = ∑' n : ℕ, ∫ ρ in 0..c, densityTerm u n ρ := by
          symm
          exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
            (summable_densityTerm_norm_restrict hc hu hSigma)
    _ = ∑' n : ℕ, u n * c ^ (2 * n + 2) / (n + 1 : ℝ) := by
          refine tsum_congr ?_
          intro n
          exact integral_densityTerm u n c

end OneModeSeries

end KorenblumProofSearch3
