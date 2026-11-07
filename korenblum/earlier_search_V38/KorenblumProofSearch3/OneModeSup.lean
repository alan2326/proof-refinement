import KorenblumProofSearch3.OneModeMax

noncomputable section

namespace KorenblumProofSearch3

namespace OneModeSup

/--
Positive mode indices `j >= 1`.
-/
abbrev PositiveMode := { j : ℕ // 1 ≤ j }

/--
The full one-mode coefficient kernel

`sup_{j >= 1} (j / (j + 1)) c^(2j+2) / ρ^(2j)`.
-/
def supSet (c ρ : ℝ) : Set ℝ :=
  Set.range (fun j : PositiveMode => OneModeKernel.term c ρ j.1)

def supKernel (c ρ : ℝ) : ℝ :=
  sSup (supSet c ρ)

theorem supSet_nonempty (c ρ : ℝ) : (supSet c ρ).Nonempty := by
  refine ⟨OneModeKernel.term c ρ 1, ?_⟩
  exact ⟨⟨1, by norm_num⟩, rfl⟩

theorem term_le_csq
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    {j : ℕ}
    (hj : 1 ≤ j) :
    OneModeKernel.term c ρ j ≤ c ^ 2 := by
  by_cases hρ0 : ρ = 0
  · have hc0 : c = 0 := by linarith
    subst hc0
    simp [OneModeKernel.term, OneModeKernel.weight, hρ0]
  have hρ : ρ ≠ 0 := hρ0
  have hρpos : 0 < ρ := by
    have hρnonneg : 0 ≤ ρ := le_trans hc hcρ
    exact lt_of_le_of_ne hρnonneg (ne_comm.mp hρ)
  have hρsqpos : 0 < ρ ^ 2 := by positivity
  have hc2ρ2 : c ^ 2 ≤ ρ ^ 2 := by nlinarith
  have ht0 : 0 ≤ c ^ 2 / ρ ^ 2 := by positivity
  have ht1 : c ^ 2 / ρ ^ 2 ≤ 1 := by
    exact (div_le_iff₀ hρsqpos).2 (by simpa using hc2ρ2)
  have hcoeffNonneg : 0 ≤ ((j : ℝ) / (j + 1)) := by positivity
  have hcoeffLe : ((j : ℝ) / (j + 1)) ≤ 1 := by
    have hj1pos : 0 < (j : ℝ) + 1 := by positivity
    exact (div_le_iff₀ hj1pos).2 (by nlinarith)
  have hpowLe : (c ^ 2 / ρ ^ 2) ^ j ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have hnormLe : OneModeTail.normalizedTerm (c ^ 2 / ρ ^ 2) j ≤ 1 := by
    unfold OneModeTail.normalizedTerm
    calc
      ((j : ℝ) / (j + 1)) * (c ^ 2 / ρ ^ 2) ^ j
          ≤ ((j : ℝ) / (j + 1)) * 1 := by
            exact mul_le_mul_of_nonneg_left hpowLe hcoeffNonneg
      _ ≤ 1 := by simpa using hcoeffLe
  calc
    OneModeKernel.term c ρ j
        = c ^ 2 * OneModeTail.normalizedTerm (c ^ 2 / ρ ^ 2) j := by
            exact OneModeMax.term_eq_csq_mul_normalized c ρ hρ
    _ ≤ c ^ 2 * 1 := by exact mul_le_mul_of_nonneg_left hnormLe (sq_nonneg c)
    _ = c ^ 2 := by ring

theorem supSet_bddAbove
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ) :
    BddAbove (supSet c ρ) := by
  refine ⟨c ^ 2, ?_⟩
  intro x hx
  rcases hx with ⟨j, rfl⟩
  exact term_le_csq hc hcρ j.2

theorem term_le_supKernel
    (c ρ : ℝ)
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    {j : ℕ}
    (hj : 1 ≤ j) :
    OneModeKernel.term c ρ j ≤ supKernel c ρ := by
  exact le_csSup (supSet_bddAbove hc hcρ) ⟨⟨j, hj⟩, rfl⟩

theorem supKernel_eq_term_of_tau_bounds
    {c ρ : ℝ}
    (hc : 0 ≤ c)
    (hcρ : c ≤ ρ)
    (hρ : ρ ≠ 0)
    {mode : ℕ}
    (hMode : 1 ≤ mode)
    (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / ρ ^ 2)
    (hUpper : c ^ 2 / ρ ^ 2 ≤ OneModeTail.tau mode) :
    supKernel c ρ = OneModeKernel.term c ρ mode := by
  apply le_antisymm
  · refine csSup_le (supSet_nonempty c ρ) ?_
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact OneModeMax.term_le_mode_of_tau_bounds hρ hMode j.2 hLower hUpper
  · exact term_le_supKernel c ρ hc hcρ hMode

theorem supKernel_pos
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : c < ρ) :
    0 < supKernel c ρ := by
  have hρpos : 0 < ρ := lt_trans hc hρ
  have hTerm :
      0 < OneModeKernel.term c ρ 1 := by
    rw [OneModeKernel.term_one_eq_branch2]
    unfold PaperAxioms.branch2SigmaKernel
    positivity
  exact lt_of_lt_of_le hTerm (term_le_supKernel c ρ hc.le hρ.le (show 1 ≤ 1 by norm_num))

theorem supKernel_ne_zero
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : c < ρ) :
    supKernel c ρ ≠ 0 :=
  ne_of_gt (supKernel_pos hc hρ)

end OneModeSup

end KorenblumProofSearch3
