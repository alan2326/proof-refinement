import KorenblumPaper.OneModeAlgebra
import KorenblumPaper.OneModeSup

noncomputable section

namespace KorenblumPaper

namespace OneModeSeries

/--
Generic `Σ`-type series `∑ u_n s^(2n)`.
-/
def sigmaSeq (u : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, u n * s ^ (2 * n)

/--
Disk-integral weight `c^(2n+2) / (n+1)`.
-/
def diskWeightedSeq (u : ℕ → ℝ) (c : ℝ) : ℝ :=
  ∑' n : ℕ, u n * c ^ (2 * n + 2) / (n + 1 : ℝ)

/--
One-mode weight `j/(j+1) c^(2j+2)`.
-/
def oneModeWeightedSeq (u : ℕ → ℝ) (c : ℝ) : ℝ :=
  ∑' n : ℕ, u n * OneModeKernel.weight c n

theorem weight_zero (c : ℝ) : OneModeKernel.weight c 0 = 0 := by
  simp [OneModeKernel.weight]

theorem weight_le_supKernel_mul_pow
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    {j : ℕ}
    (hj : 1 ≤ j) :
    OneModeKernel.weight c j ≤ OneModeSup.supKernel c ρ * ρ ^ (2 * j) := by
  have hPow : 0 ≤ ρ ^ (2 * j) := by
    have hEq : ρ ^ (2 * j) = (ρ ^ j) ^ 2 := by
      rw [show 2 * j = j * 2 by omega, pow_mul]
    rw [hEq]
    exact sq_nonneg (ρ ^ j)
  calc
    OneModeKernel.weight c j = OneModeKernel.term c ρ j * ρ ^ (2 * j) := by
      exact OneModeKernel.weight_eq_term_mul_pow c ρ j hρ
    _ ≤ OneModeSup.supKernel c ρ * ρ ^ (2 * j) := by
      exact mul_le_mul_of_nonneg_right
        (OneModeSup.term_le_supKernel c ρ hc hcρ hj) hPow

theorem diskWeightedSeq_le_csq_mul_sigmaSeq
    {u : ℕ → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n)
    (hDisk : Summable (fun n : ℕ => u n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n))) :
    diskWeightedSeq u c ≤ c ^ 2 * sigmaSeq u c := by
  unfold diskWeightedSeq sigmaSeq
  have hScaled : Summable (fun n : ℕ => c ^ 2 * (u n * c ^ (2 * n))) :=
    hSigma.mul_left (c ^ 2)
  calc
    ∑' n : ℕ, u n * c ^ (2 * n + 2) / (n + 1 : ℝ)
        ≤ ∑' n : ℕ, c ^ 2 * (u n * c ^ (2 * n)) := by
          refine Summable.tsum_le_tsum ?_ hDisk hScaled
          intro n
          by_cases hn : n = 0
          · subst hn
            have hEq : u 0 * c ^ 2 = c ^ 2 * u 0 := by ring
            simpa using le_of_eq hEq
          · have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
            have hun : 0 ≤ u n := hu n h1
            simpa [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left (OneModeAlgebra.positive_term_le_csq_mul hc n) hun
    _ = c ^ 2 * ∑' n : ℕ, u n * c ^ (2 * n) := by
          rw [tsum_mul_left]

theorem csq_mul_sigmaSeq_sub_diskWeightedSeq_eq_oneModeWeightedSeq
    {u : ℕ → ℝ}
    {c : ℝ}
    (hSigma : Summable (fun n : ℕ => u n * c ^ (2 * n)))
    (hDisk : Summable (fun n : ℕ => u n * c ^ (2 * n + 2) / (n + 1 : ℝ))) :
    c ^ 2 * sigmaSeq u c - diskWeightedSeq u c = oneModeWeightedSeq u c := by
  unfold sigmaSeq diskWeightedSeq oneModeWeightedSeq
  have hScaled : Summable (fun n : ℕ => c ^ 2 * (u n * c ^ (2 * n))) :=
    hSigma.mul_left (c ^ 2)
  calc
    c ^ 2 * ∑' n : ℕ, u n * c ^ (2 * n) - ∑' n : ℕ, u n * c ^ (2 * n + 2) / (n + 1 : ℝ)
        = ∑' n : ℕ, (c ^ 2 * (u n * c ^ (2 * n)) - u n * c ^ (2 * n + 2) / (n + 1 : ℝ)) := by
            rw [← tsum_mul_left, ← Summable.tsum_sub hScaled hDisk]
    _ = ∑' n : ℕ, u n * OneModeKernel.weight c n := by
          refine tsum_congr ?_
          intro n
          have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
          have hPow : c ^ (2 * n + 2) = c ^ 2 * c ^ (2 * n) := by
            rw [show 2 * n + 2 = 2 + 2 * n by omega, pow_add]
          rw [hPow]
          unfold OneModeKernel.weight
          field_simp [hn]
          ring

theorem oneModeWeightedSeq_le_supKernel_mul_sigmaSeq
    {u : ℕ → ℝ}
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    (hu : ∀ n, 0 ≤ u n)
    (hModes : ∀ n, u n ≠ 0 → 1 ≤ n)
    (hWeight : Summable (fun n : ℕ => u n * OneModeKernel.weight c n))
    (hSigma : Summable (fun n : ℕ => u n * ρ ^ (2 * n))) :
    oneModeWeightedSeq u c ≤ OneModeSup.supKernel c ρ * sigmaSeq u ρ := by
  unfold oneModeWeightedSeq sigmaSeq
  have hScaled : Summable (fun n : ℕ => (u n * ρ ^ (2 * n)) * OneModeSup.supKernel c ρ) :=
    hSigma.mul_right (OneModeSup.supKernel c ρ)
  calc
    ∑' n : ℕ, u n * OneModeKernel.weight c n
        ≤ ∑' n : ℕ, (u n * ρ ^ (2 * n)) * OneModeSup.supKernel c ρ := by
          refine Summable.tsum_le_tsum ?_ hWeight hScaled
          intro n
          by_cases hun0 : u n = 0
          · simp [hun0]
          · have hMode : 1 ≤ n := hModes n hun0
            have hun : 0 ≤ u n := hu n
            calc
              u n * OneModeKernel.weight c n
                  ≤ u n * (OneModeSup.supKernel c ρ * ρ ^ (2 * n)) := by
                    exact mul_le_mul_of_nonneg_left
                      (weight_le_supKernel_mul_pow hc hcρ hρ hMode) hun
              _ = (u n * ρ ^ (2 * n)) * OneModeSup.supKernel c ρ := by ring
    _ = (∑' n : ℕ, u n * ρ ^ (2 * n)) * OneModeSup.supKernel c ρ := by
          rw [tsum_mul_right]
    _ = OneModeSup.supKernel c ρ * ∑' n : ℕ, u n * ρ ^ (2 * n) := by
          ring

theorem inner_le_supKernel_mul_sigmaSeq
    {δ η : ℕ → ℝ}
    {c ρ innerExcess : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    (hδ : ∀ n, 1 ≤ n → 0 ≤ δ n)
    (hη : ∀ n, 0 ≤ η n)
    (hModes : ∀ n, η n ≠ 0 → 1 ≤ n)
    (hPosDisk : Summable (fun n : ℕ => δ n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPosSigma : Summable (fun n : ℕ => δ n * c ^ (2 * n)))
    (hNegDisk : Summable (fun n : ℕ => η n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hNegSigmaC : Summable (fun n : ℕ => η n * c ^ (2 * n)))
    (hNegSigmaRho : Summable (fun n : ℕ => η n * ρ ^ (2 * n)))
    (hNegWeight : Summable (fun n : ℕ => η n * OneModeKernel.weight c n))
    (hMajor : sigmaSeq δ c ≤ sigmaSeq η c)
    (hInner :
      innerExcess ≤ diskWeightedSeq δ c - diskWeightedSeq η c) :
    innerExcess ≤ OneModeSup.supKernel c ρ * sigmaSeq η ρ := by
  have hPos :
      diskWeightedSeq δ c ≤ c ^ 2 * sigmaSeq δ c :=
    diskWeightedSeq_le_csq_mul_sigmaSeq hc hδ hPosDisk hPosSigma
  have hMajorScaled :
      c ^ 2 * sigmaSeq δ c ≤ c ^ 2 * sigmaSeq η c := by
    exact mul_le_mul_of_nonneg_left hMajor (sq_nonneg c)
  have hEq :
      c ^ 2 * sigmaSeq η c - diskWeightedSeq η c = oneModeWeightedSeq η c :=
    csq_mul_sigmaSeq_sub_diskWeightedSeq_eq_oneModeWeightedSeq hNegSigmaC hNegDisk
  have hWeight :
      oneModeWeightedSeq η c ≤ OneModeSup.supKernel c ρ * sigmaSeq η ρ :=
    oneModeWeightedSeq_le_supKernel_mul_sigmaSeq
      hc hcρ hρ hη hModes hNegWeight hNegSigmaRho
  calc
    innerExcess ≤ diskWeightedSeq δ c - diskWeightedSeq η c := hInner
    _ ≤ c ^ 2 * sigmaSeq δ c - diskWeightedSeq η c := by
          exact sub_le_sub_right hPos _
    _ ≤ c ^ 2 * sigmaSeq η c - diskWeightedSeq η c := by
          exact sub_le_sub_right hMajorScaled _
    _ = oneModeWeightedSeq η c := hEq
    _ ≤ OneModeSup.supKernel c ρ * sigmaSeq η ρ := hWeight

end OneModeSeries

end KorenblumPaper
