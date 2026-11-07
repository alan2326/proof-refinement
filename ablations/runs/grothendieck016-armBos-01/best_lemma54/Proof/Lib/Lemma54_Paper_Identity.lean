/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Identity.lean — Step 4: identity (75)

Differentiating `F_p η p (F_inv p z) = z` in `p` at fixed `z` gives the
paper's identity (75):

  `∂_p F_inv = -(H_η - H_0)(F_inv) / F_p'(F_inv)`

The right-hand side is well-defined whenever `F_p'(F_inv z) ≠ 0`, which
holds on `disk r` for `p` small enough (proved via the Cauchy bound on
`∂_z F_inv` from Step 3, combined with the chain-rule identity
`F_p'(F_inv z) · ∂_z F_inv z = 1`).

This file proves the identity in `HasDerivAt`-form, taking the
parameterised family `F_inv : ℝ → ℂ → ℂ` as a hypothesis.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Cauchy

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-! ## F_p' lower bound at F_inv -/

/-- Lower bound on `‖F_p'(F_inv p z)‖` for `z ∈ disk r`, derived from
the Cauchy first-derivative bound on `F_inv` (Step 3) and the chain-rule
identity `F_p'(F_inv z) · ∂_z F_inv z = 1`. Specifically,

  `‖F_p'(F_inv p z)‖ ≥ (1-r) / (2 R_val_paper r)`. -/
theorem F_p_deriv_lower_bound_at_F_inv
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      (1 - r) / (2 * R_val_paper r) ≤ ‖deriv (F_p η p) (F_inv p z)‖ := by
  intro p hp z hz
  -- z ∈ disk r₁ since disk r ⊆ disk r₁
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  -- F_inv p is analytic on disk r₁
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  -- F_inv p is differentiable at z (open disk r₁ contains z)
  have hF_inv_diff : HasDerivAt (F_inv p) (deriv (F_inv p) z) z :=
    ((hF_an_p z hz_r1).differentiableAt).hasDerivAt
  -- F_p η p is differentiable at F_inv p z (F_inv p z ∈ S, F_p η p analytic on S)
  have hFpz_S : F_inv p z ∈ S := hF_S p hp z hz_r1
  have hFp_diff_at : DifferentiableAt ℂ (F_p η p) (F_inv p z) := by
    have hH0 : DifferentiableAt ℂ H0 (F_inv p z) :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hFpz_S)
    have hHe : DifferentiableAt ℂ (H_eta η) (F_inv p z) :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hFpz_S)
    change DifferentiableAt ℂ
      (fun w => (1 - ↑p) * H0 w + ↑p * H_eta η w) (F_inv p z)
    exact (hH0.const_mul _).add (hHe.const_mul _)
  have hFp_hasDerivAt :
      HasDerivAt (F_p η p) (deriv (F_p η p) (F_inv p z)) (F_inv p z) :=
    hFp_diff_at.hasDerivAt
  -- Chain rule: HasDerivAt (F_p η p ∘ F_inv p) (F_p'(F_inv p z) · F_inv'(z)) z
  have h_chain : HasDerivAt (fun w => F_p η p (F_inv p w))
      (deriv (F_p η p) (F_inv p z) * deriv (F_inv p) z) z :=
    hFp_hasDerivAt.comp z hF_inv_diff
  -- The composed function is locally id on disk r₁
  have h_comp_eq : ∀ w ∈ disk (r1 r), F_p η p (F_inv p w) = w := hF_inv_eq p hp
  have h_evt : (fun w => F_p η p (F_inv p w)) =ᶠ[nhds z] id := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨disk (r1 r), (disk_isOpen _).mem_nhds hz_r1, ?_⟩
    intro w hw
    exact h_comp_eq w hw
  -- Hence the derivative of the composition at z equals 1
  have h_id_deriv : HasDerivAt (id : ℂ → ℂ) 1 z := hasDerivAt_id z
  have h_chain_eq : HasDerivAt (fun w => F_p η p (F_inv p w)) 1 z := by
    apply HasDerivAt.congr_of_eventuallyEq h_id_deriv
    exact h_evt
  -- By uniqueness of derivative
  have h_prod_eq_one :
      deriv (F_p η p) (F_inv p z) * deriv (F_inv p) z = 1 :=
    h_chain.unique h_chain_eq
  -- Now bound: ‖F_inv'(z)‖ ≤ 2R/(1-r) from Cauchy
  have h_finv_bound : ‖deriv (F_inv p) z‖ ≤ 2 * R_val_paper r / (1 - r) := by
    have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r :=
      fun z' hz' => hF_R p hp z' hz'
    exact F_inv_first_deriv_bound_core hr0 hr1 hF_an_p hF_R_p z hz
  -- ‖F_p'(F_inv) · F_inv'(z)‖ = 1, so ‖F_p'(F_inv)‖ · ‖F_inv'(z)‖ = 1
  have h_norm_prod : ‖deriv (F_p η p) (F_inv p z)‖ * ‖deriv (F_inv p) z‖ = 1 := by
    have := congrArg norm h_prod_eq_one
    rw [norm_mul] at this
    simpa using this
  -- And ‖F_p'(F_inv)‖ ≥ 1 / ‖F_inv'(z)‖
  -- We need ‖F_inv'(z)‖ > 0 (else 1 = 0).
  have h_finv_norm_pos : 0 < ‖deriv (F_inv p) z‖ := by
    by_contra h
    push_neg at h
    have h_eq_zero : ‖deriv (F_inv p) z‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [h_eq_zero, mul_zero] at h_norm_prod
    norm_num at h_norm_prod
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have h_2R_pos : 0 < 2 * R_val_paper r := by linarith
  have h_one_sub_r : 0 < 1 - r := by linarith
  have h_invFp_pos : 0 < 2 * R_val_paper r / (1 - r) := by positivity
  -- Convert to: ‖F_p'‖ = 1/‖F_inv'(z)‖ ≥ 1/(2R/(1-r)) = (1-r)/(2R)
  -- From ‖F_p'‖ · ‖F_inv'(z)‖ = 1: ‖F_p'‖ = 1/‖F_inv'(z)‖
  have h_Fp_eq : ‖deriv (F_p η p) (F_inv p z)‖ = 1 / ‖deriv (F_inv p) z‖ := by
    field_simp
    linarith [h_norm_prod]
  rw [h_Fp_eq]
  -- Want: (1-r)/(2R) ≤ 1/‖F_inv'(z)‖
  -- Equivalently: ‖F_inv'(z)‖/(2R) ≤ 1/(1-r) — but cleaner: cross multiply.
  have h_step : (1 - r) * ‖deriv (F_inv p) z‖ ≤ 2 * R_val_paper r := by
    have hmul := mul_le_mul_of_nonneg_left h_finv_bound h_one_sub_r.le
    have hsimp : (1 - r) * (2 * R_val_paper r / (1 - r)) = 2 * R_val_paper r := by
      field_simp
    linarith [hsimp ▸ hmul]
  -- 1 / ‖F_inv'(z)‖ ≥ (1-r)/(2R) ↔ (1-r) · ‖F_inv'(z)‖ ≤ 2R
  rw [le_div_iff₀ h_finv_norm_pos, div_mul_eq_mul_div, div_le_one h_2R_pos]
  linarith [h_step]

/-! ## Identity (75) -/

/-- **Step 4. Identity (75).** Differentiating `F_p η p (F_inv q z) = z`
in `q` gives `∂_p F_inv = -(H_η - H_0)(F_inv) / F_p'(F_inv)`.

Hypotheses encode:
* a parameterised analytic right-inverse `F_inv : ℝ → ℂ → ℂ` on
  `disk r₁` for each `p ∈ (0, pr)`,
* the right-inverse identity `F_p η p (F_inv p z) = z`,
* `F_inv p z ∈ S`,
* joint differentiability of `q ↦ F_inv q z` in `q` at `p`,
* non-vanishing of `F_p'` at `F_inv p z` for `z ∈ disk r`. -/
theorem identity_75
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_p_diff : ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z) p)
    (hF_p_deriv_ne_zero : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk r, deriv (F_p η p) (F_inv p z) ≠ 0) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      HasDerivAt (fun q : ℝ => F_inv q z)
        (-(H_eta η (F_inv p z) - H0 (F_inv p z)) /
          deriv (F_p η p) (F_inv p z)) p := by
  intro p hp z hz
  set w₀ := F_inv p z with hw₀_def
  -- z ∈ disk r₁
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  -- w₀ = F_inv p z ∈ S
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  -- u(q) := F_inv q z is differentiable at p
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  have hu_diff : DifferentiableAt ℝ u p := hF_p_diff p hp z hz
  set u' := deriv u p with hu'_def
  have hu_hasDeriv : HasDerivAt u u' p := hu_diff.hasDerivAt
  -- H_0 is ℂ-differentiable at w₀
  have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
    H0_analyticOnNhd.differentiableOn.differentiableAt
      (S_isOpen.mem_nhds hw₀_S)
  have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
    hH0_diff_C.hasDerivAt
  -- H_eta η is ℂ-differentiable at w₀
  have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
    (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
      (S_isOpen.mem_nhds hw₀_S)
  have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
    hHe_diff_C.hasDerivAt
  -- Apply scalar comp to A(q) := H_0(u(q)) — ℝ-derivative via .scomp
  have hA : HasDerivAt (fun q : ℝ => H0 (u q)) (u' * deriv H0 w₀) p := by
    have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
    have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  -- Similarly for B(q) := H_eta η (u(q))
  have hB : HasDerivAt (fun q : ℝ => H_eta η (u q)) (u' * deriv (H_eta η) w₀) p := by
    have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
    have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  -- The function (1 - ↑q) — ℝ → ℂ
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  -- (1 - ↑q) · A(q): product rule
  have h1subA : HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * H0 (u q))
      (-1 * H0 w₀ + ((1 : ℂ) - ↑p) * (u' * deriv H0 w₀)) p :=
    h_one_sub_q.mul hA
  -- ↑q · B(q): product rule
  have hqB : HasDerivAt (fun q : ℝ => (↑q : ℂ) * H_eta η (u q))
      (1 * H_eta η w₀ + ↑p * (u' * deriv (H_eta η) w₀)) p :=
    h_ofReal_q.mul hB
  -- Sum
  have hL : HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * H0 (u q) +
                                       (↑q : ℂ) * H_eta η (u q))
      (-1 * H0 w₀ + ((1 : ℂ) - ↑p) * (u' * deriv H0 w₀) +
        (1 * H_eta η w₀ + ↑p * (u' * deriv (H_eta η) w₀))) p :=
    h1subA.add hqB
  -- Identify with F_p η q (F_inv q z)
  have hL_eq : (fun q : ℝ => ((1 : ℂ) - ↑q) * H0 (u q) + (↑q : ℂ) * H_eta η (u q))
      = (fun q : ℝ => F_p η q (F_inv q z)) := by
    funext q; rfl
  rw [hL_eq] at hL
  -- L(q) := F_p η q (F_inv q z) equals z near p (constant)
  have hL_const : (fun q : ℝ => F_p η q (F_inv q z)) =ᶠ[nhds p] (fun _ => z) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, isOpen_Ioo.mem_nhds hp, ?_⟩
    intro q hq
    exact hF_inv_eq q hq z hz_r1
  have hL_zero : HasDerivAt (fun q : ℝ => F_p η q (F_inv q z)) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p z)
    exact hL_const
  -- Equate the two derivatives
  have h_deriv_eq :
      -1 * H0 w₀ + ((1 : ℂ) - ↑p) * (u' * deriv H0 w₀) +
        (1 * H_eta η w₀ + ↑p * (u' * deriv (H_eta η) w₀)) = 0 :=
    hL.unique hL_zero
  -- Simplify: this is (H_eta η w₀ - H_0 w₀) + u' · F_p'(w₀) = 0
  have hFp'_eq :
      deriv (F_p η p) w₀ = (1 - ↑p) * deriv H0 w₀ + ↑p * deriv (H_eta η) w₀ :=
    F_p_deriv η p w₀ hw₀_S
  have h_simp :
      (H_eta η w₀ - H0 w₀) + u' * deriv (F_p η p) w₀ = 0 := by
    rw [hFp'_eq]
    linear_combination h_deriv_eq
  -- Solve: u' = -(H_eta η w₀ - H_0 w₀) / deriv (F_p η p) w₀
  have hFp_ne : deriv (F_p η p) w₀ ≠ 0 := hF_p_deriv_ne_zero p hp z hz
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    have : u' * deriv (F_p η p) w₀ = -(H_eta η w₀ - H0 w₀) := by
      linear_combination h_simp
    field_simp [hFp_ne] at this ⊢
    linear_combination this
  rw [← hu'_value]
  exact hu_hasDeriv

end Braverman.Paper
