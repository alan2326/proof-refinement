/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Taylor.lean — Step 6: Taylor remainder in `p`

For `f_z(p) := F_inv p z - sin z - p · ψ(z)` with
`ψ(z) := (z - H_eta η (sin z)) · cos z`:
* `f_z(0) = 0` and `f_z'(0) = 0`,
* `‖f_z''(q)‖ ≤ 2 · Cr_paper` for `q ∈ Ico 0 pr`,

A two-step boundary mean value inequality gives `‖f_z(p)‖ ≤ Cr_paper · p²`.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-- Two-step mean value inequality (the core algebraic lemma): a function
`f : ℝ → E` with `f(0) = 0`, `f'(0) = 0`, and `‖f''(t)‖ ≤ M` on `[0, p]`
satisfies `‖f(p)‖ ≤ M·p²/2`.

This is the tight `(n+1)!`-form of Lagrange's remainder for vector-valued
functions, derived via two applications of the boundary mean value
inequality (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`). -/
private lemma norm_le_half_M_p_sq_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' f'' : ℝ → E} {p M : ℝ} (hp : 0 < p) (hM_nn : 0 ≤ M)
    (hf_cont : ContinuousOn f (Set.Icc 0 p))
    (hf_deriv_right : ∀ t ∈ Set.Ico (0 : ℝ) p, HasDerivWithinAt f (f' t) (Set.Ici t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc 0 p))
    (hf'_deriv_right : ∀ t ∈ Set.Ico (0 : ℝ) p, HasDerivWithinAt f' (f'' t) (Set.Ici t) t)
    (hf_zero : f 0 = 0) (hf'_zero : f' 0 = 0)
    (h_bound : ∀ t ∈ Set.Ico (0 : ℝ) p, ‖f'' t‖ ≤ M) :
    ‖f p‖ ≤ M * p^2 / 2 := by
  have hp_nn : 0 ≤ p := le_of_lt hp
  -- Step A: ‖f'(t)‖ ≤ M·t for t ∈ Icc 0 p
  have h_step_A : ∀ t ∈ Set.Icc (0 : ℝ) p, ‖f' t‖ ≤ M * t := by
    intro t ht
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hf'_cont hf'_deriv_right
      h_bound t ht
    rw [hf'_zero, sub_zero, sub_zero] at h
    exact h
  -- Step B: ‖f(p)‖ ≤ M·p²/2 via boundary thm with B(t) := M·t²/2, B'(t) := M·t
  set B : ℝ → ℝ := fun t => M * t ^ 2 / 2 with hB_def
  set B' : ℝ → ℝ := fun t => M * t with hB'_def
  have hB_deriv : ∀ x, HasDerivAt B (B' x) x := by
    intro x
    have h_id : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h_sq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      have := h_id.pow 2
      simpa using this
    have h_M_sq : HasDerivAt (fun t : ℝ => M * t ^ 2) (M * (2 * x)) x := h_sq.const_mul M
    have h_div : HasDerivAt B (M * (2 * x) / 2) x := by
      have := h_M_sq.div_const 2
      simpa [hB_def] using this
    convert h_div using 1
    show M * x = M * (2 * x) / 2; ring
  have hf_a : ‖f 0‖ ≤ B 0 := by
    rw [hf_zero, norm_zero, hB_def]; simp
  have h_bound_f' : ∀ t ∈ Set.Ico (0 : ℝ) p, ‖f' t‖ ≤ B' t := fun t ht =>
    h_step_A t (Set.Ico_subset_Icc_self ht)
  have h_step_B : ∀ x ∈ Set.Icc (0 : ℝ) p, ‖f x‖ ≤ B x :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary hf_cont hf_deriv_right hf_a hB_deriv
      h_bound_f'
  have h_p := h_step_B p (right_mem_Icc.mpr hp_nn)
  show ‖f p‖ ≤ M * p^2 / 2
  rw [hB_def] at h_p
  exact h_p

/-! ## Helpers — converting `Ico 0 pr` derivatives to `Ici t` right-derivatives -/

/-- For `t ∈ Ico 0 pr`, the within-`Ico 0 pr` derivative restricts to the
within-`Ici t` derivative. We use this to feed `ContDiffOn`-derived
HasDerivWithinAt's into the boundary MVI lemma, which expects `Ici t`. -/
private lemma hasDerivWithinAt_Ici_of_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {pr t : ℝ}
    (h : HasDerivWithinAt f f' (Set.Ico (0 : ℝ) pr) t)
    (ht : t ∈ Set.Ico (0 : ℝ) pr) :
    HasDerivWithinAt f f' (Set.Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  -- Show: Ico 0 pr ∈ 𝓝[Ici t] t
  -- Take open nbd (-1, pr); then Ici t ∩ (-1, pr) = [t, pr) ⊆ Ico 0 pr.
  refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) pr, isOpen_Ioo, ⟨by linarith [ht.1], ht.2⟩, ?_⟩
  intro x hx
  have hx_ge : t ≤ x := hx.2
  have hx_lt : x < pr := hx.1.2
  exact ⟨by linarith [ht.1, hx_ge], hx_lt⟩

/-- **Step 6.** Lagrange Taylor remainder bound.

For each `z ∈ disk r`, the function `q ↦ F_inv q z` satisfies the
Taylor bound `‖F_inv p z − sin z − p·ψ(z)‖ ≤ Cr · p²` on `(0, pr)`,
given:
* `F_inv 0 z = sin z`,
* a right-derivative `ψ(z)` at `q = 0`,
* `C²` regularity in `q` on `[0, pr)`,
* a uniform bound `‖f''(t)‖ ≤ 2 · Cr` on `[0, pr)`.

Here `f(q) := F_inv q z - sin z - q · ψ(z)`, with `f(0) = 0`,
`f'(0) = 0`, and `f''(q) = ∂²_q F_inv q z`. The factor 2 in the
second-derivative bound cancels the Lagrange `1/2!` factor. -/
theorem taylor_remainder_p
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {Cr : ℝ} (hCr_nn : 0 ≤ Cr)
    (F_inv : ℝ → ℂ → ℂ)
    (h_F_inv_zero : ∀ z ∈ disk r, F_inv 0 z = Complex.sin z)
    (h_F_inv_first_deriv :
      ∀ z ∈ disk r,
        HasDerivWithinAt (fun q : ℝ => F_inv q z)
          ((z - H_eta η (Complex.sin z)) * Complex.cos z)
          (Set.Ici (0 : ℝ)) 0)
    (hu_C2 : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ico (0 : ℝ) pr))
    (h_second_deriv_bound :
      ∀ z ∈ disk r, ∀ t ∈ Set.Ico (0 : ℝ) pr,
        ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv q z) (Set.Ico (0 : ℝ) pr) t‖
          ≤ 2 * Cr) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖F_inv p z - Complex.sin z -
          ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
        ≤ Cr * p ^ 2 := by
  intro p hp z hz
  obtain ⟨hp_pos, hp_lt⟩ := hp
  -- Setup — the function and its derivatives
  set ψ : ℂ := (z - H_eta η (Complex.sin z)) * Complex.cos z with hψ_def
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set u' : ℝ → ℂ := derivWithin u (Set.Ico (0 : ℝ) pr) with hu'_def
  set u'' : ℝ → ℂ := iteratedDerivWithin 2 u (Set.Ico (0 : ℝ) pr) with hu''_def
  set f : ℝ → ℂ := fun q => u q - Complex.sin z - (q : ℂ) • ψ with hf_def
  set f' : ℝ → ℂ := fun q => u' q - ψ with hf'_def
  -- Hypotheses for u
  have hu_C2_z : ContDiffOn ℝ 2 u (Set.Ico (0 : ℝ) pr) := hu_C2 z hz
  have hu_C1_z : ContDiffOn ℝ 1 u (Set.Ico (0 : ℝ) pr) := hu_C2_z.of_le (by norm_num)
  have hu_C0_z : ContinuousOn u (Set.Ico (0 : ℝ) pr) := hu_C2_z.continuousOn
  have hu_zero : u 0 = Complex.sin z := h_F_inv_zero z hz
  have hu'_zero_eq_psi : HasDerivWithinAt u ψ (Set.Ici (0 : ℝ)) 0 :=
    h_F_inv_first_deriv z hz
  have hUnique : UniqueDiffOn ℝ (Set.Ico (0 : ℝ) pr) := uniqueDiffOn_Ico 0 pr
  -- HasDerivWithinAt u (u' t) (Ico 0 pr) t for t ∈ Ico 0 pr
  have hu_diffOn : DifferentiableOn ℝ u (Set.Ico (0 : ℝ) pr) :=
    hu_C2_z.differentiableOn (by norm_num)
  have hu_hasDeriv_Ico : ∀ t ∈ Set.Ico (0 : ℝ) pr,
      HasDerivWithinAt u (u' t) (Set.Ico (0 : ℝ) pr) t := by
    intro t ht
    have h := (hu_diffOn t ht).hasDerivWithinAt
    -- the (chosen) derivWithin equals derivWithin u (Ico 0 pr) t = u' t
    have hd : derivWithin u (Set.Ico (0 : ℝ) pr) t = u' t := rfl
    exact hd ▸ h
  -- u' is DifferentiableOn (Ico 0 pr) (since u is C² and Ico has UniqueDiffOn)
  have hu'_diffOn : DifferentiableOn ℝ u' (Set.Ico (0 : ℝ) pr) := by
    have h := hu_C2_z.differentiableOn_iteratedDerivWithin
      (m := 1) (by norm_cast) hUnique
    -- iteratedDerivWithin 1 u (Ico 0 pr) = derivWithin u (Ico 0 pr) = u'
    have heq : iteratedDerivWithin 1 u (Set.Ico (0 : ℝ) pr) = u' := by
      funext x
      rw [iteratedDerivWithin_one]
    exact heq ▸ h
  -- HasDerivWithinAt u' (u'' t) (Ico 0 pr) t for t ∈ Ico 0 pr
  have hu'_hasDeriv_Ico : ∀ t ∈ Set.Ico (0 : ℝ) pr,
      HasDerivWithinAt u' (u'' t) (Set.Ico (0 : ℝ) pr) t := by
    intro t ht
    have h := (hu'_diffOn t ht).hasDerivWithinAt
    have hd : u'' t = derivWithin u' (Set.Ico (0 : ℝ) pr) t := by
      rw [hu''_def, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    exact hd ▸ h
  -- Continuity of u' on Ico 0 pr (from ContDiffOn 2)
  have hu'_cont_Ico : ContinuousOn u' (Set.Ico (0 : ℝ) pr) := by
    have h := hu_C2_z.continuousOn_iteratedDerivWithin (m := 1) (by norm_cast) hUnique
    have heq : iteratedDerivWithin 1 u (Set.Ico (0 : ℝ) pr) = u' := by
      funext x; rw [iteratedDerivWithin_one]
    exact heq ▸ h
  -- Subset lemma: Icc 0 p ⊆ Ico 0 pr
  have hp_le : p ≤ pr := le_of_lt hp_lt
  have hIcc_subset : Set.Icc (0 : ℝ) p ⊆ Set.Ico (0 : ℝ) pr := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt hx.2 hp_lt⟩
  have hIco_subset : Set.Ico (0 : ℝ) p ⊆ Set.Ico (0 : ℝ) pr := by
    intro x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hp_le⟩
  -- f(0) = 0
  have hf_zero : f 0 = 0 := by
    show u 0 - Complex.sin z - (0 : ℝ) • ψ = 0
    rw [hu_zero]
    simp
  -- f'(0) = 0
  -- u'(0) is computed via derivWithin (Ico 0 pr) 0; and HasDerivWithinAt u ψ (Ici 0) 0 ⟹ HasDerivWithinAt u ψ (Ico 0 pr) 0
  --   since Ico 0 pr ⊆ Ici 0
  have hu_at_zero_Ico : HasDerivWithinAt u ψ (Set.Ico (0 : ℝ) pr) 0 := by
    apply hu'_zero_eq_psi.mono
    intro x hx
    exact hx.1
  have hu'_zero_val : u' 0 = ψ := by
    have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) pr := ⟨le_refl _, hpr_pos⟩
    rw [hu'_def]
    exact hu_at_zero_Ico.derivWithin (hUnique 0 h0_mem)
  have hf'_zero : f' 0 = 0 := by
    show u' 0 - ψ = 0
    rw [hu'_zero_val]; ring
  -- HasDerivWithinAt for f at every t ∈ Ico 0 p, w.r.t. (Ici t)
  -- f q = u q - sin z - q • ψ
  have hf_deriv_right : ∀ t ∈ Set.Ico (0 : ℝ) p,
      HasDerivWithinAt f (f' t) (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Ico (0 : ℝ) pr := hIco_subset ht
    have hu_t_Ico := hu_hasDeriv_Ico t ht'
    have hu_t : HasDerivWithinAt u (u' t) (Set.Ici t) t :=
      hasDerivWithinAt_Ici_of_Ico hu_t_Ico ht'
    have h_const : HasDerivWithinAt (fun _ : ℝ => Complex.sin z) 0 (Set.Ici t) t :=
      hasDerivWithinAt_const _ _ _
    have h_lin : HasDerivWithinAt (fun q : ℝ => (q : ℂ) • ψ) ψ (Set.Ici t) t := by
      have h_q : HasDerivWithinAt (fun q : ℝ => (q : ℂ)) 1 (Set.Ici t) t := by
        have := (Complex.ofRealCLM).hasDerivAt (x := t)
        exact this.hasDerivWithinAt
      have := h_q.smul_const ψ
      simpa using this
    have h_sub1 : HasDerivWithinAt (fun q : ℝ => u q - Complex.sin z) (u' t - 0) (Set.Ici t) t :=
      hu_t.sub h_const
    have h_sub2 :
        HasDerivWithinAt (fun q : ℝ => u q - Complex.sin z - (q : ℂ) • ψ)
          ((u' t - 0) - ψ) (Set.Ici t) t :=
      h_sub1.sub h_lin
    have hgoal : HasDerivWithinAt f (u' t - ψ) (Set.Ici t) t := by
      convert h_sub2 using 1
      ring
    exact hgoal
  -- Continuity of f on Icc 0 p
  have hf_cont : ContinuousOn f (Set.Icc 0 p) := by
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    · exact (hu_C0_z.mono hIcc_subset)
    · exact continuousOn_const
    · -- q ↦ q • ψ continuous
      have h_id : ContinuousOn (fun q : ℝ => (q : ℂ)) (Set.Icc 0 p) :=
        Complex.continuous_ofReal.continuousOn
      exact h_id.smul continuousOn_const
  -- HasDerivWithinAt for f' at every t ∈ Ico 0 p
  have hf'_deriv_right : ∀ t ∈ Set.Ico (0 : ℝ) p,
      HasDerivWithinAt f' (u'' t) (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Ico (0 : ℝ) pr := hIco_subset ht
    have hu'_t_Ico := hu'_hasDeriv_Ico t ht'
    have hu'_t : HasDerivWithinAt u' (u'' t) (Set.Ici t) t :=
      hasDerivWithinAt_Ici_of_Ico hu'_t_Ico ht'
    have h_const : HasDerivWithinAt (fun _ : ℝ => ψ) 0 (Set.Ici t) t :=
      hasDerivWithinAt_const _ _ _
    have h := hu'_t.sub h_const
    have hgoal : HasDerivWithinAt f' (u'' t) (Set.Ici t) t := by
      convert h using 1
      simp
    exact hgoal
  -- Continuity of f' on Icc 0 p (from continuity of u' on Ico 0 pr ⊃ Icc 0 p)
  have hf'_cont : ContinuousOn f' (Set.Icc 0 p) := by
    apply ContinuousOn.sub
    · exact hu'_cont_Ico.mono hIcc_subset
    · exact continuousOn_const
  -- Bound: ‖u''(t)‖ ≤ 2 Cr for t ∈ Ico 0 p ⊆ Ico 0 pr
  have h_bound : ∀ t ∈ Set.Ico (0 : ℝ) p, ‖u'' t‖ ≤ 2 * Cr := by
    intro t ht
    exact h_second_deriv_bound z hz t (hIco_subset ht)
  -- Apply the aux lemma
  have h2Cr_nn : 0 ≤ 2 * Cr := by linarith
  have h_main := norm_le_half_M_p_sq_aux (E := ℂ) (f := f) (f' := f') (f'' := u'')
    hp_pos h2Cr_nn hf_cont hf_deriv_right hf'_cont hf'_deriv_right hf_zero hf'_zero h_bound
  -- Final: ‖f p‖ = ‖F_inv p z - sin z - p · ψ‖ ≤ 2·Cr · p²/2 = Cr · p²
  have h_eq_smul : (p : ℂ) • ψ = (p : ℂ) * ψ := by
    rw [smul_eq_mul]
  have h_lhs_eq :
      f p = F_inv p z - Complex.sin z - (p : ℂ) * ψ := by
    show u p - Complex.sin z - (p : ℂ) • ψ = F_inv p z - Complex.sin z - (p : ℂ) * ψ
    rw [h_eq_smul]
  have h_rhs_eq : (2 * Cr) * p ^ 2 / 2 = Cr * p ^ 2 := by ring
  rw [h_lhs_eq] at h_main
  rw [h_rhs_eq] at h_main
  exact h_main

end Braverman.Paper
