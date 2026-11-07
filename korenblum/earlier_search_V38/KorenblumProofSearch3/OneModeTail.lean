import KorenblumProofSearch3.OneModeKernel

noncomputable section

namespace KorenblumProofSearch3

namespace OneModeTail

/--
The mode-transition threshold

`tau_j = j (j + 2) / (j + 1)^2 = 1 - 1 / (j + 1)^2`.
-/
def tau (j : ℕ) : ℝ :=
  ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) ^ 2)

/--
The normalized one-mode sequence `j/(j+1) * t^j` after factoring out the common
`c^2` term.
-/
def normalizedTerm (t : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) / (j + 1)) * t ^ j

theorem tau_eq_one_sub_inv_sq (j : ℕ) :
    tau j = 1 - 1 / (((j : ℝ) + 1) ^ 2) := by
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  unfold tau
  field_simp [hj1]
  ring

theorem tau_monotone : Monotone tau := by
  intro j k hjk
  rw [tau_eq_one_sub_inv_sq, tau_eq_one_sub_inv_sq]
  have hj1sq_pos : 0 < (((j : ℝ) + 1) ^ 2) := by positivity
  have hsq : (((j : ℝ) + 1) ^ 2) ≤ (((k : ℝ) + 1) ^ 2) := by
    have hlin : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hjk
    nlinarith
  have hdiv :
      1 / (((k : ℝ) + 1) ^ 2) ≤ 1 / (((j : ℝ) + 1) ^ 2) :=
    one_div_le_one_div_of_le hj1sq_pos hsq
  linarith

theorem tau_nonneg (j : ℕ) : 0 ≤ tau j := by
  rw [tau_eq_one_sub_inv_sq]
  have hsq : 1 ≤ (((j : ℝ) + 1) ^ 2) := by
    have hjnonneg : 0 ≤ (j : ℝ) := by positivity
    nlinarith
  have hdiv : 1 / (((j : ℝ) + 1) ^ 2) ≤ 1 := by
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by positivity) hsq)
  linarith

theorem tau_lt_one (j : ℕ) : tau j < 1 := by
  rw [tau_eq_one_sub_inv_sq]
  have hdivpos : 0 < 1 / (((j : ℝ) + 1) ^ 2) := by positivity
  linarith

theorem ratio_bound_ge_three
    {j : ℕ}
    (hj : 3 ≤ j) :
    15 * ((j : ℝ) + 1) ^ 2 ≤ 16 * (j : ℝ) * ((j : ℝ) + 2) := by
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

theorem normalizedTerm_succ_le_of_le_fifteen_sixteen
    {t : ℝ}
    (ht : 0 ≤ t)
    {j : ℕ}
    (hj : 3 ≤ j)
    (hbound : t ≤ 15 / 16) :
    normalizedTerm t (j + 1) ≤ normalizedTerm t j := by
  have hj1 : 0 < (j : ℝ) + 1 := by positivity
  have hj2 : 0 < (j : ℝ) + 2 := by positivity
  have htj : 0 ≤ t ^ j := pow_nonneg ht j
  have hratio :
      (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t ≤ (j : ℝ) / ((j : ℝ) + 1) := by
    have hpoly := ratio_bound_ge_three hj
    have hmain : ((j : ℝ) + 1) ^ 2 * t ≤ (j : ℝ) * ((j : ℝ) + 2) := by
      nlinarith
    have hden : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
    rw [show (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t =
        (((j : ℝ) + 1) ^ 2 * t) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne'],
      show (j : ℝ) / ((j : ℝ) + 1) =
        ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne']]
    exact div_le_div_of_nonneg_right hmain hden.le
  have hmul := mul_le_mul_of_nonneg_right hratio htj
  have hsucc :
      normalizedTerm t (j + 1) =
        ((((j : ℝ) + 1) / ((j : ℝ) + 2)) * t) * t ^ j := by
    unfold normalizedTerm
    rw [pow_succ]
    norm_num [Nat.cast_add]
    ring
  have hcurr :
      normalizedTerm t j =
        ((j : ℝ) / ((j : ℝ) + 1)) * t ^ j := by
    rfl
  rw [hsucc, hcurr]
  exact hmul

theorem normalizedTerm_succ_le_of_le_tau
    {t : ℝ}
    (ht : 0 ≤ t)
    {j : ℕ}
    (hj : 0 < j)
    (hbound : t ≤ tau j) :
    normalizedTerm t (j + 1) ≤ normalizedTerm t j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1 : 0 < (j : ℝ) + 1 := by positivity
  have hj2 : 0 < (j : ℝ) + 2 := by positivity
  have htj : 0 ≤ t ^ j := pow_nonneg ht j
  have hmain : ((j : ℝ) + 1) ^ 2 * t ≤ (j : ℝ) * ((j : ℝ) + 2) := by
    have hbound' : t ≤ ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) ^ 2) := by
      simpa [tau] using hbound
    have hj1sq_pos : 0 < (((j : ℝ) + 1) ^ 2) := by positivity
    have hscaled := (le_div_iff₀ hj1sq_pos).1 hbound'
    nlinarith
  have hratio :
      (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t ≤ (j : ℝ) / ((j : ℝ) + 1) := by
    have hden : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
    rw [show (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t =
        ((((j : ℝ) + 1) ^ 2) * t) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne'],
      show (j : ℝ) / ((j : ℝ) + 1) =
        ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne']]
    exact div_le_div_of_nonneg_right hmain hden.le
  have hmul := mul_le_mul_of_nonneg_right hratio htj
  have hsucc :
      normalizedTerm t (j + 1) =
        ((((j : ℝ) + 1) / ((j : ℝ) + 2)) * t) * t ^ j := by
    unfold normalizedTerm
    rw [pow_succ]
    norm_num [Nat.cast_add]
    ring
  have hcurr :
      normalizedTerm t j =
        ((j : ℝ) / ((j : ℝ) + 1)) * t ^ j := by
    rfl
  rw [hsucc, hcurr]
  exact hmul

theorem normalizedTerm_le_succ_of_tau_le
    {t : ℝ}
    (ht : 0 ≤ t)
    {j : ℕ}
    (hj : 0 < j)
    (hbound : tau j ≤ t) :
    normalizedTerm t j ≤ normalizedTerm t (j + 1) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1 : 0 < (j : ℝ) + 1 := by positivity
  have hj2 : 0 < (j : ℝ) + 2 := by positivity
  have htj : 0 ≤ t ^ j := pow_nonneg ht j
  have hmain : (j : ℝ) * ((j : ℝ) + 2) ≤ ((j : ℝ) + 1) ^ 2 * t := by
    have hbound' : ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) ^ 2) ≤ t := by
      simpa [tau] using hbound
    have hj1sq_pos : 0 < (((j : ℝ) + 1) ^ 2) := by positivity
    have hscaled := (div_le_iff₀ hj1sq_pos).1 hbound'
    nlinarith
  have hratio :
      (j : ℝ) / ((j : ℝ) + 1) ≤ (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t := by
    have hden : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
    rw [show (j : ℝ) / ((j : ℝ) + 1) =
        ((j : ℝ) * ((j : ℝ) + 2)) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne'],
      show (((j : ℝ) + 1) / ((j : ℝ) + 2)) * t =
        ((((j : ℝ) + 1) ^ 2) * t) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) by
          field_simp [hj1.ne', hj2.ne']]
    exact div_le_div_of_nonneg_right hmain hden.le
  have hmul := mul_le_mul_of_nonneg_right hratio htj
  have hsucc :
      normalizedTerm t (j + 1) =
        ((((j : ℝ) + 1) / ((j : ℝ) + 2)) * t) * t ^ j := by
    unfold normalizedTerm
    rw [pow_succ]
    norm_num [Nat.cast_add]
    ring
  have hcurr :
      normalizedTerm t j =
        ((j : ℝ) / ((j : ℝ) + 1)) * t ^ j := by
    rfl
  rw [hsucc, hcurr]
  exact hmul

theorem normalizedTerm_le_of_le_mode
    {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ {k j : ℕ}, 1 ≤ k → k ≤ j → tau (j - 1) ≤ t →
      normalizedTerm t k ≤ normalizedTerm t j
  | k, j, hk, hkj, hLower => by
      induction hkj with
      | refl =>
          exact le_rfl
      | @step j hkj ih =>
          have hjPos : 0 < j := by
            exact lt_of_lt_of_le (show 0 < k by exact Nat.succ_le_iff.mp hk) hkj
          have hPrev : tau (j - 1) ≤ t := by
            exact le_trans (tau_monotone (Nat.sub_le j 1)) hLower
          have hstep :
              normalizedTerm t j ≤ normalizedTerm t (j + 1) :=
            normalizedTerm_le_succ_of_tau_le ht hjPos hLower
          exact le_trans (ih hPrev) hstep

theorem normalizedTerm_le_of_mode_le
    {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ {j k : ℕ}, 1 ≤ j → j ≤ k → t ≤ tau j →
      normalizedTerm t k ≤ normalizedTerm t j
  | j, k, hj, hjk, hUpper => by
      induction hjk with
      | refl =>
          exact le_rfl
      | @step k hjk ih =>
          have hkPos : 0 < k := by exact Nat.succ_le_iff.mp (le_trans hj hjk)
          have hUpper' : t ≤ tau k := by
            exact le_trans hUpper (tau_monotone hjk)
          have hstep :
              normalizedTerm t (k + 1) ≤ normalizedTerm t k :=
            normalizedTerm_succ_le_of_le_tau ht hkPos hUpper'
          exact le_trans hstep ih

theorem normalizedTerm_le_mode_of_tau_bounds
    {t : ℝ}
    (ht : 0 ≤ t)
    {j k : ℕ}
    (hj : 1 ≤ j)
    (hk : 1 ≤ k)
    (hLower : tau (j - 1) ≤ t)
    (hUpper : t ≤ tau j) :
    normalizedTerm t k ≤ normalizedTerm t j := by
  rcases le_total k j with hkj | hjk
  · exact normalizedTerm_le_of_le_mode ht hk hkj hLower
  · exact normalizedTerm_le_of_mode_le ht hj hjk hUpper

end OneModeTail

end KorenblumProofSearch3
