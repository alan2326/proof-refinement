import KorenblumPaper.OneModeMax

open scoped BigOperators

noncomputable section

namespace KorenblumPaper

namespace OneModeAlgebra

theorem positive_term_le_csq_mul
    {c : ℝ}
    (hc : 0 ≤ c)
    (k : ℕ) :
    c ^ (2 * k + 2) / (k + 1 : ℝ) ≤ c ^ 2 * c ^ (2 * k) := by
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hk1pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  have hA : 0 ≤ c ^ 2 * c ^ (2 * k) := by positivity
  have hMul :
      c ^ 2 * c ^ (2 * k) ≤ (c ^ 2 * c ^ (2 * k)) * (k + 1 : ℝ) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_left hk1 hA
  have hPow :
      c ^ (2 * k + 2) = c ^ 2 * c ^ (2 * k) := by
    rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add]
  rw [hPow]
  exact (div_le_iff₀ hk1pos).2 hMul

theorem positive_sum_le_csq_mul
    {c : ℝ}
    (hc : 0 ≤ c)
    (s : Finset ℕ)
    (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ s, 0 ≤ δ k) :
    Finset.sum s (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) ≤
      c ^ 2 * Finset.sum s (fun k => δ k * c ^ (2 * k)) := by
  calc
    Finset.sum s (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ))
        ≤ Finset.sum s (fun k => δ k * (c ^ 2 * c ^ (2 * k))) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hδk : 0 ≤ δ k := hδ k hk
          simpa [mul_div_assoc, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left (positive_term_le_csq_mul hc k) hδk
    _ = c ^ 2 * Finset.sum s (fun k => δ k * c ^ (2 * k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring

theorem weighted_difference_le_kernelOn_mul
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (sPos sNeg : Finset ℕ)
    (hsNeg : sNeg.Nonempty)
    (δ η : ℕ → ℝ)
    (hρ : ρ ≠ 0)
    (hδ : ∀ k ∈ sPos, 0 ≤ δ k)
    (hη : ∀ j ∈ sNeg, 0 ≤ η j)
    (hMajor :
      Finset.sum sPos (fun k => δ k * c ^ (2 * k)) ≤
        Finset.sum sNeg (fun j => η j * c ^ (2 * j))) :
    Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) -
        Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ)) ≤
      OneModeKernel.kernelOn c ρ sNeg hsNeg *
        Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := by
  have hPos :
      Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) ≤
        c ^ 2 * Finset.sum sPos (fun k => δ k * c ^ (2 * k)) :=
    positive_sum_le_csq_mul hc sPos δ hδ
  have hMajorScaled :
      c ^ 2 * Finset.sum sPos (fun k => δ k * c ^ (2 * k)) ≤
        c ^ 2 * Finset.sum sNeg (fun j => η j * c ^ (2 * j)) := by
    exact mul_le_mul_of_nonneg_left hMajor (sq_nonneg c)
  have hWeight :
      c ^ 2 * Finset.sum sNeg (fun j => η j * c ^ (2 * j)) -
        Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ)) =
          Finset.sum sNeg (fun j => η j * OneModeKernel.weight c j) := by
    rw [Finset.mul_sum]
    have hSplit :
        (∑ i ∈ sNeg, c ^ 2 * (η i * c ^ (2 * i))) -
          ∑ j ∈ sNeg, η j * c ^ (2 * j + 2) / (j + 1 : ℝ) =
            ∑ j ∈ sNeg,
              (c ^ 2 * (η j * c ^ (2 * j)) - η j * c ^ (2 * j + 2) / (j + 1 : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
    rw [hSplit]
    refine Finset.sum_congr rfl ?_
    intro j hj
    unfold OneModeKernel.weight
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hPow :
        c ^ (2 * j + 2) = c ^ 2 * c ^ (2 * j) := by
      rw [show 2 * j + 2 = 2 + 2 * j by omega, pow_add]
    rw [hPow]
    field_simp [hj1]
    ring
  have hKernel :=
    OneModeKernel.weighted_sum_le_kernelOn_mul c ρ sNeg hsNeg η hρ hη
  calc
    Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) -
        Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ))
        ≤ c ^ 2 * Finset.sum sNeg (fun j => η j * c ^ (2 * j)) -
          Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ)) := by
            exact sub_le_sub (le_trans hPos hMajorScaled) le_rfl
    _ = Finset.sum sNeg (fun j => η j * OneModeKernel.weight c j) := hWeight
    _ ≤ OneModeKernel.kernelOn c ρ sNeg hsNeg *
          Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := hKernel

theorem weighted_difference_le_term_of_tau_bounds
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
    Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) -
        Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ)) ≤
      OneModeKernel.term c ρ mode *
        Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := by
  have hKernel :=
    weighted_difference_le_kernelOn_mul hc sPos sNeg hsNeg δ η hρ hδ hη hMajor
  have hKernelLe :
      OneModeKernel.kernelOn c ρ sNeg hsNeg ≤ OneModeKernel.term c ρ mode := by
    exact Finset.sup'_le (s := sNeg) (f := OneModeKernel.term c ρ) hsNeg
      (fun j hj => OneModeMax.term_le_mode_of_tau_bounds hρ hMode (hModes j hj) hLower hUpper)
  have hScaleNonneg :
      0 ≤ Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    have hηj : 0 ≤ η j := hη j hj
    have hPow : 0 ≤ ρ ^ (2 * j) := by
      have hEq : ρ ^ (2 * j) = (ρ ^ j) ^ 2 := by
        rw [show 2 * j = j * 2 by omega, pow_mul]
      rw [hEq]
      exact sq_nonneg (ρ ^ j)
    exact mul_nonneg hηj hPow
  calc
    Finset.sum sPos (fun k => δ k * c ^ (2 * k + 2) / (k + 1 : ℝ)) -
        Finset.sum sNeg (fun j => η j * c ^ (2 * j + 2) / (j + 1 : ℝ))
        ≤ OneModeKernel.kernelOn c ρ sNeg hsNeg *
          Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := hKernel
    _ ≤ OneModeKernel.term c ρ mode *
          Finset.sum sNeg (fun j => η j * ρ ^ (2 * j)) := by
            exact mul_le_mul_of_nonneg_right hKernelLe hScaleNonneg

end OneModeAlgebra

end KorenblumPaper
