import KorenblumProofSearch3.OneModeTail

noncomputable section

namespace KorenblumProofSearch3

namespace OneModeTauWindow

theorem sq_div_sq_le_of_le
    {c x y : ℝ}
    (hx : 0 < x)
    (hxy : x ≤ y) :
    c ^ 2 / y ^ 2 ≤ c ^ 2 / x ^ 2 := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hy2 : 0 < y ^ 2 := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  exact div_le_div₀ (sq_nonneg c) le_rfl hx2 hsq

theorem sq_div_sq_bounds_of_mem_Icc
    {c start stop ρ : ℝ}
    (hstart : 0 < start)
    (hρ : ρ ∈ Set.Icc start stop) :
    c ^ 2 / stop ^ 2 ≤ c ^ 2 / ρ ^ 2 ∧
      c ^ 2 / ρ ^ 2 ≤ c ^ 2 / start ^ 2 := by
  constructor
  · exact sq_div_sq_le_of_le (lt_of_lt_of_le hstart hρ.1) hρ.2
  · exact sq_div_sq_le_of_le hstart hρ.1

theorem tau_bounds_of_mem_Icc
    {c start stop ρ : ℝ}
    {mode : ℕ}
    (hstart : 0 < start)
    (hρ : ρ ∈ Set.Icc start stop)
    (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / stop ^ 2)
    (hUpper : c ^ 2 / start ^ 2 ≤ OneModeTail.tau mode) :
    OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2 ∧
      c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode := by
  rcases sq_div_sq_bounds_of_mem_Icc hstart hρ with ⟨hlo, hhi⟩
  exact ⟨le_trans hLower hlo, le_trans hhi hUpper⟩

end OneModeTauWindow

end KorenblumProofSearch3
