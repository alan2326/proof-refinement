import KorenblumPaper.OneModeTail

noncomputable section

namespace KorenblumPaper

namespace OneModeMax

/--
`term c ρ j` is `c^2` times the normalized mode sequence at
`t = c^2 / ρ^2`.
-/
theorem term_eq_csq_mul_normalized
    (c ρ : ℝ)
    {j : ℕ}
    (hρ : ρ ≠ 0) :
    OneModeKernel.term c ρ j =
      c ^ 2 * OneModeTail.normalizedTerm (c ^ 2 / ρ ^ 2) j := by
  unfold OneModeKernel.term OneModeKernel.weight OneModeTail.normalizedTerm
  have hρpow : ρ ^ (2 * j) ≠ 0 := pow_ne_zero _ hρ
  have hpow :
      (c ^ 2 / ρ ^ 2) ^ j = c ^ (2 * j) / ρ ^ (2 * j) := by
    rw [div_pow, pow_mul, pow_mul]
  calc
    (j : ℝ) / (j + 1) * c ^ (2 * j + 2) / ρ ^ (2 * j)
        = ((j : ℝ) / (j + 1)) * (c ^ 2 * (c ^ (2 * j) / ρ ^ (2 * j))) := by
            field_simp [hρpow]
            ring_nf
    _ = c ^ 2 * (((j : ℝ) / (j + 1)) * (c ^ (2 * j) / ρ ^ (2 * j))) := by ring
    _ = c ^ 2 * (((j : ℝ) / (j + 1)) * (c ^ 2 / ρ ^ 2) ^ j) := by rw [hpow]

/--
If `c^2 / ρ^2` lies in the mode-`j` window

`tau (j - 1) ≤ c^2 / ρ^2 ≤ tau j`,

then the `j`th one-mode term dominates every positive mode.
-/
theorem term_le_mode_of_tau_bounds
    {c ρ : ℝ}
    (hρ : ρ ≠ 0)
    {j k : ℕ}
    (hj : 1 ≤ j)
    (hk : 1 ≤ k)
    (hLower : OneModeTail.tau (j - 1) ≤ c ^ 2 / ρ ^ 2)
    (hUpper : c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau j) :
    OneModeKernel.term c ρ k ≤ OneModeKernel.term c ρ j := by
  have hScale : 0 ≤ c ^ 2 := sq_nonneg c
  rw [term_eq_csq_mul_normalized c ρ hρ, term_eq_csq_mul_normalized c ρ hρ]
  exact mul_le_mul_of_nonneg_left
    (OneModeTail.normalizedTerm_le_mode_of_tau_bounds
      (by positivity) hj hk hLower hUpper)
    hScale

end OneModeMax

end KorenblumPaper
