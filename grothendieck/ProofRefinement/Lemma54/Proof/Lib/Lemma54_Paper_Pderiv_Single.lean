/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Pderiv_Single.lean — Step 5 paper-faithful (single-M)

The paper-faithful version of Step 5: bound on `‖∂²_p F_inv‖` in terms of
a single sup-norm bound `M ≥ max{|H_0|, |H_η|, |H_0'|, |H_η'|}` on the
F_inv-image envelope.

The strategy:
1. **Auxiliary z-identity**: From the chain rule on `F_p ∘ F_inv = id`,
   `D · h = 1` (first deriv) and `DD · h² + D · u_zz = 0` (second deriv),
   where `D = (∂_w F_p)(F_inv)`, `DD = (∂²_w F_p)(F_inv)`,
   `h = ∂_z F_inv`, `u_zz = ∂²_z F_inv`.
2. **Form-A → Form-B norm bound** (via aux z-identity): The form-A bound
   `‖D‖ ‖u''‖ ≤ 2 ‖Φ'‖ ‖u'‖ + ‖DD‖ ‖u'‖²` combined with
   `‖DD‖ ‖u'‖² = ‖D‖ ‖u_zz‖ ‖Φ‖²` gives
   `‖u''‖ ≤ 2 ‖Φ'‖ ‖Φ‖ / ‖D‖² + ‖u_zz‖ ‖Φ‖²`.
3. **Apply M and Cauchy bounds**: `‖Φ‖, ‖Φ'‖ ≤ 2M` (triangle);
   `1/‖D‖ ≤ 2R/(1-r)`, `‖u_zz‖ ≤ 8R/(1-r)²` (recentred Cauchy).
   Yields `‖u''‖ ≤ 32 M² R (R+1) / (1-r)²`.
4. **Algebraic step**: `(2R+1)(1-r)³ ≤ 16R` for `r ∈ (0,1)`,
   `R = sinh((3+r)/4) ≥ 3/4 > 1/14`, finishing
   `32 M² R (R+1) / (1-r)² ≤ 2 · Cr_paper r M R`.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Cauchy
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Identity
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-! ## Auxiliary z-identity: `DD · h² + D · u_zz = 0`

Differentiating `F_p η p (F_inv p w) = w` once in `w` gives `D · h = 1`;
differentiating again gives `DD · h² + D · u_zz = 0`. -/

/-- The chain-rule identity `D · h = 1`: first-order. -/
private theorem Dh_eq_one
    (η : ℝ) {r : ℝ} (hr1 : r < 1)
    {pr : ℝ}
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk (r1 r),
      deriv (F_p η p) (F_inv p z) * deriv (F_inv p) z = 1 := by
  intro p hp z hz
  have hF_inv_diff : HasDerivAt (F_inv p) (deriv (F_inv p) z) z :=
    ((hF_an p hp z hz).differentiableAt).hasDerivAt
  have hFw_S : F_inv p z ∈ S := hF_S p hp z hz
  have hFp_diff_at : DifferentiableAt ℂ (F_p η p) (F_inv p z) := by
    have hH0 : DifferentiableAt ℂ H0 (F_inv p z) :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hFw_S)
    have hHe : DifferentiableAt ℂ (H_eta η) (F_inv p z) :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hFw_S)
    change DifferentiableAt ℂ (fun w => (1 - ↑p) * H0 w + ↑p * H_eta η w) (F_inv p z)
    exact (hH0.const_mul _).add (hHe.const_mul _)
  have hFp_hasDerivAt :
      HasDerivAt (F_p η p) (deriv (F_p η p) (F_inv p z)) (F_inv p z) :=
    hFp_diff_at.hasDerivAt
  have h_chain : HasDerivAt (fun w => F_p η p (F_inv p w))
      (deriv (F_p η p) (F_inv p z) * deriv (F_inv p) z) z :=
    hFp_hasDerivAt.comp z hF_inv_diff
  have h_evt : (fun w => F_p η p (F_inv p w)) =ᶠ[nhds z] id := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨disk (r1 r), (disk_isOpen _).mem_nhds hz, ?_⟩
    intro w hw
    exact hF_inv_eq p hp w hw
  have h_id_deriv : HasDerivAt (id : ℂ → ℂ) 1 z := hasDerivAt_id z
  have h_chain_id : HasDerivAt (fun w => F_p η p (F_inv p w)) 1 z :=
    h_id_deriv.congr_of_eventuallyEq h_evt
  exact h_chain.unique h_chain_id

/-- Auxiliary z-identity: `DD · h² + D · u_zz = 0`. -/
theorem F_inv_aux_z_identity
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ}
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 +
        deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z = 0 := by
  intro p hp z hz
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hOpen_r1 : IsOpen (disk (r1 r)) := disk_isOpen _
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  -- F_p η p analytic at any w ∈ S
  have hFp_an_at : ∀ w ∈ S, AnalyticAt ℂ (F_p η p) w := by
    intro w hw
    have hH0 : AnalyticAt ℂ H0 w := H0_analyticOnNhd w hw
    have hHe : AnalyticAt ℂ (H_eta η) w := (H_eta_analyticOnNhd η) w hw
    change AnalyticAt ℂ (fun w' => (1 - ↑p) * H0 w' + ↑p * H_eta η w') w
    exact (analyticAt_const.mul hH0).add (analyticAt_const.mul hHe)
  -- f(w) := D(w) · h(w) where D(w) = deriv (F_p η p) (F_inv p w), h(w) = deriv (F_inv p) w.
  set h_z : ℂ → ℂ := fun w => deriv (F_inv p) w with hh_def
  set D_z : ℂ → ℂ := fun w => deriv (F_p η p) (F_inv p w) with hD_def
  -- f =ᶠ const 1 on disk r₁ via Dh_eq_one
  have hf_evt_const :
      (fun w => D_z w * h_z w) =ᶠ[nhds z] (fun _ => (1 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨disk (r1 r), hOpen_r1.mem_nhds hz_r1, ?_⟩
    intro w hw
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp w hw
  have hf_deriv_zero : HasDerivAt (fun w => D_z w * h_z w) 0 z := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const z (1 : ℂ))
    exact hf_evt_const
  -- Compute deriv f via product rule.
  have hF_inv_diff_z : HasDerivAt (F_inv p) (h_z z) z :=
    ((hF_an_p z hz_r1).differentiableAt).hasDerivAt
  have hFw₀_S : F_inv p z ∈ S := hF_S p hp z hz_r1
  have hderivFp_an_at : AnalyticAt ℂ (deriv (F_p η p)) (F_inv p z) := by
    have h_an_on : AnalyticOnNhd ℂ (F_p η p) S := by
      intro w hw; exact hFp_an_at w hw
    exact h_an_on.deriv (F_inv p z) hFw₀_S
  have hderivFp_diff_at : DifferentiableAt ℂ (deriv (F_p η p)) (F_inv p z) :=
    hderivFp_an_at.differentiableAt
  have h_iter2_eq : iteratedDeriv 2 (F_p η p) (F_inv p z) =
      deriv (deriv (F_p η p)) (F_inv p z) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderivFp_hasDerivAt :
      HasDerivAt (deriv (F_p η p))
        (iteratedDeriv 2 (F_p η p) (F_inv p z)) (F_inv p z) := by
    rw [h_iter2_eq]
    exact hderivFp_diff_at.hasDerivAt
  have hD_hasDerivAt : HasDerivAt D_z
      (iteratedDeriv 2 (F_p η p) (F_inv p z) * h_z z) z := by
    have h := hderivFp_hasDerivAt.comp z hF_inv_diff_z
    have hsmul : (h_z z • iteratedDeriv 2 (F_p η p) (F_inv p z) : ℂ) =
        iteratedDeriv 2 (F_p η p) (F_inv p z) * h_z z := by
      rw [smul_eq_mul]; ring
    simpa [Function.comp, hsmul] using h
  have h_iter2_finv : iteratedDeriv 2 (F_inv p) z = deriv (deriv (F_inv p)) z := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hh_an_at : AnalyticAt ℂ (deriv (F_inv p)) z :=
    hF_an_p.deriv z hz_r1
  have hh_diff_at : DifferentiableAt ℂ (deriv (F_inv p)) z :=
    hh_an_at.differentiableAt
  have hh_hasDerivAt :
      HasDerivAt h_z (iteratedDeriv 2 (F_inv p) z) z := by
    rw [h_iter2_finv]
    exact hh_diff_at.hasDerivAt
  have hf_prod : HasDerivAt (fun w => D_z w * h_z w)
      (iteratedDeriv 2 (F_p η p) (F_inv p z) * h_z z * h_z z +
        D_z z * iteratedDeriv 2 (F_inv p) z) z := by
    have h := hD_hasDerivAt.mul hh_hasDerivAt
    convert h using 1
  have h_eq := hf_prod.unique hf_deriv_zero
  -- Substitute h_z z = deriv (F_inv p) z and D_z z = deriv (F_p η p) (F_inv p z)
  show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 +
        deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z = 0
  have h_eq' : iteratedDeriv 2 (F_p η p) (F_inv p z) * deriv (F_inv p) z * deriv (F_inv p) z +
        deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z = 0 := h_eq
  linear_combination h_eq'

/-! ## Algebraic step: `(2R+1)(1-r)³ ≤ 16R` for `r ∈ (0,1)`, `R = sinh((3+r)/4)` -/

private theorem alg_step_paper {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (2 * R_val_paper r + 1) * (1 - r) ^ 3 ≤ 16 * R_val_paper r := by
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_le1 : 1 - r ≤ 1 := by linarith
  have h1mr3_le1 : (1 - r) ^ 3 ≤ 1 := by
    have h := pow_le_pow_left₀ h1mr_pos.le h1mr_le1 3
    simpa using h
  -- R = sinh((3+r)/4) ≥ (3+r)/4 ≥ 3/4
  have h_arg_pos : 0 < (3 + r) / 4 := by linarith
  have h_arg_ge_34 : (3 : ℝ) / 4 ≤ (3 + r) / 4 := by linarith
  have hR_ge_arg : (3 + r) / 4 ≤ R_val_paper r := by
    show (3 + r) / 4 ≤ Real.sinh ((3 + r) / 4)
    exact Real.self_le_sinh_iff.mpr h_arg_pos.le
  have hR_ge_34 : (3 : ℝ) / 4 ≤ R_val_paper r := le_trans h_arg_ge_34 hR_ge_arg
  have h_2R_p1_nn : 0 ≤ 2 * R_val_paper r + 1 := by
    have := R_val_paper_nonneg hr0
    linarith
  -- (2R+1)(1-r)³ ≤ 2R+1 ≤ 16R (since R ≥ 3/4 ≥ 1/14)
  have h_step1 : (2 * R_val_paper r + 1) * (1 - r) ^ 3 ≤ 2 * R_val_paper r + 1 := by
    nlinarith [h1mr3_le1, h_2R_p1_nn]
  have h_step2 : 2 * R_val_paper r + 1 ≤ 16 * R_val_paper r := by
    -- 14R ≥ 14·(3/4) = 21/2 ≥ 1, so 2R+1 ≤ 14R + 2R = 16R
    linarith
  linarith

/-! ## Main: paper-faithful Step 5 bound -/

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful).** Bound on `‖∂²_p F_inv‖` using the
single sup-norm hypothesis on `H_0, H_η, H_0', H_η'` over the F_inv envelope.

The bound is `2 · Cr_paper r M R` so that the Lagrange `1/2!` factor in
Step 6 (Taylor remainder) absorbs the `2`. -/
theorem F_inv_p_second_deriv_bound_paper
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M : ℝ} (hM_nn : 0 ≤ M)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_H0_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H0 (F_inv p z)‖ ≤ M)
    (h_M_He_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z)‖ ≤ M)
    (h_M_H0p_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv H0 (F_inv p z)‖ ≤ M)
    (h_M_Hep_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z)‖ ≤ M) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_paper r M (R_val_paper r) := by
  intro p hp z hz
  -- Triangle bounds: ‖Φ‖ ≤ 2M, ‖Φ'‖ ≤ 2M
  have h2M_nn : 0 ≤ 2 * M := by linarith
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set invFp := 2 * R / (1 - r) with hinvFp_def
  have hinvFp_pos : 0 < invFp := by simp [hinvFp_def]; positivity
  have hinvFp_nn : 0 ≤ invFp := le_of_lt hinvFp_pos
  -- u(q) := F_inv q z; u'(p) = deriv u p; u'' = iteratedDeriv 2 u p.
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  -- u is C² on (0, pr)
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  -- identity_75: deriv u q = -(H_eta(u q) - H_0(u q)) / F_p'(u q)
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  -- u'' from C²
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  -- Set-up algebraic letters: Φ, Φ', D, DD, h, u_zz
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- Bounds
  have h_Φ_bound : ‖Φ‖ ≤ 2 * M := by
    show ‖H_eta η w₀ - H0 w₀‖ ≤ 2 * M
    calc ‖H_eta η w₀ - H0 w₀‖
        ≤ ‖H_eta η w₀‖ + ‖H0 w₀‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (h_M_He_bound p hp z hz) (h_M_H0_bound p hp z hz)
      _ = 2 * M := by ring
  have h_Φ'_bound : ‖Φ'‖ ≤ 2 * M := by
    show ‖deriv (H_eta η) w₀ - deriv H0 w₀‖ ≤ 2 * M
    calc ‖deriv (H_eta η) w₀ - deriv H0 w₀‖
        ≤ ‖deriv (H_eta η) w₀‖ + ‖deriv H0 w₀‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (h_M_Hep_bound p hp z hz) (h_M_H0p_bound p hp z hz)
      _ = 2 * M := by ring
  have hD_lower : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_div_iff₀ hD_pos h1mr_pos]
    have hstep : (1 - r) ≤ ‖D‖ * (2 * R) := by
      have hmul := mul_le_mul_of_nonneg_right hD_lower (by positivity : (0 : ℝ) ≤ 2 * R)
      have hsimp : (1 - r) / (2 * R) * (2 * R) = 1 - r := by field_simp
      linarith [hsimp ▸ hmul]
    linarith
  -- ‖h_z‖ = 1/‖D‖ from D · h_z = 1 (chain rule)
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  -- ‖h_z‖ ≤ invFp
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  -- Cauchy: ‖u_zz‖ ≤ 8R/(1-r)²
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hu_zz_bound : ‖u_zz‖ ≤ 8 * R / (1 - r) ^ 2 :=
    F_inv_second_deriv_bound_core hr0 hr1 hF_an_p hF_R_p z hz
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  -- Cauchy: ‖h_z‖ ≤ 2R/(1-r) (we already have via Dh_eq_one — same value)
  -- Aux z-identity: DD · h_z² + D · u_zz = 0
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  -- Take norms: ‖DD‖ · ‖h_z‖² = ‖D‖ · ‖u_zz‖
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  -- Now derive form-A: D u'' + 2 Φ' u' + DD · u'² = 0
  -- We do this by showing K(q) = 0 has derivative 0 at p, where
  -- K(q) := H_eta η (u q) - H_0 (u q) + F_p'(u q) · deriv u q.
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  -- Derive HasDerivAt K p with explicit formula via product/chain rule.
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  -- Substitute DD = (1-p) iter2 H_0 + p iter2 H_eta
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  -- form-A equation: 2 Φ' u' + DD u'² + D u'' = 0
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  -- D u'' = -(2 Φ' u' + DD u'²)
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  -- ‖D‖ · ‖u''‖ ≤ 2 ‖Φ'‖ ‖u'‖ + ‖DD‖ ‖u'‖²
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  -- ‖u'‖ = ‖Φ‖ / ‖D‖
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  -- ‖u'‖ = ‖Φ‖ * ‖h_z‖ (using ‖h_z‖ = 1/‖D‖)
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  -- ‖DD‖ ‖u'‖² = ‖D‖ ‖u_zz‖ ‖Φ‖² (key reduction via aux z-identity)
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    -- (‖Φ‖ * ‖h_z‖)² = ‖Φ‖² * ‖h_z‖²
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    -- ‖DD‖ * (‖Φ‖² * ‖h_z‖²) = (‖DD‖ * ‖h_z‖²) * ‖Φ‖² = ‖D‖ * ‖u_zz‖ * ‖Φ‖²
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  -- form-A bound substituted: ‖D‖ ‖u''‖ ≤ 2 ‖Φ'‖ (‖Φ‖ * ‖h_z‖) + ‖D‖ ‖u_zz‖ ‖Φ‖²
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  -- Divide by ‖D‖: ‖u''‖ ≤ 2 ‖Φ'‖ ‖Φ‖ ‖h_z‖ / ‖D‖ + ‖u_zz‖ ‖Φ‖²
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  -- Use 1/‖D‖ ≤ invFp:
  -- 2 ‖Φ'‖ (‖Φ‖ ‖h_z‖) / ‖D‖ ≤ 2 ‖Φ'‖ ‖Φ‖ ‖h_z‖ · invFp
  -- and ‖h_z‖ ≤ invFp, so ‖h_z‖/‖D‖ ≤ invFp · invFp = invFp²
  -- Wait actually ‖h_z‖ = 1/‖D‖ so ‖h_z‖/‖D‖ = 1/‖D‖² = ‖h_z‖² ≤ invFp²
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  -- Re-arrange: 2 ‖Φ'‖ (‖Φ‖ ‖h_z‖)/‖D‖ = 2 ‖Φ'‖ ‖Φ‖ · (‖h_z‖/‖D‖) = 2 ‖Φ'‖ ‖Φ‖ · ‖h_z‖²
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  -- Use ‖h_z‖² ≤ invFp²
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  -- Apply M bounds: ‖Φ‖ ≤ 2M, ‖Φ'‖ ≤ 2M
  have h_step_c : 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ (2 * M) * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * (2 * M) := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * (2 * M) := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * (2 * M) ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_M :
      ‖u''‖ ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) + ‖u_zz‖ * (2 * M) ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  -- Apply Cauchy bound on u_zz: ‖u_zz‖ ≤ 8R/(1-r)²
  have h_step_e : ‖u_zz‖ * (2 * M) ^ 2 ≤ (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound
    positivity
  have h_bound_RM :
      ‖u''‖ ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) + (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 := by
    linarith
  -- Simplify: 8M² invFp² + 32 M² R/(1-r)² = 8M² · 4R²/(1-r)² + 32 M² R/(1-r)²
  -- Compute invFp² = 4R²/(1-r)²:
  have h_invFp_sq : invFp ^ 2 = 4 * R ^ 2 / (1 - r) ^ 2 := by
    rw [hinvFp_def]
    field_simp
    ring
  have h_arith :
      2 * (2 * M) * ((2 * M) * invFp ^ 2) + (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 =
        32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2 := by
    rw [h_invFp_sq]
    field_simp
    ring
  rw [h_arith] at h_bound_RM
  -- Final: 32 M² R (R+1) / (1-r)² ≤ 2 · Cr_paper r M R
  -- 2 · Cr_paper r M R = 16 M² R / (1-r)² · (1 + 16R/(1-r)³)
  -- Need: 32 M² R (R+1) / (1-r)² ≤ 16 M² R / (1-r)² · (1 + 16R/(1-r)³)
  -- ↔ 2(R+1) ≤ 1 + 16R/(1-r)³ (after dividing by 16 M² R / (1-r)²)
  -- ↔ (2R+1)(1-r)³ ≤ 16R (with hM = 0 case handled separately for division)
  -- Use alg_step_paper.
  have h_alg : (2 * R + 1) * (1 - r) ^ 3 ≤ 16 * R := alg_step_paper hr0 hr1
  have h_target :
      32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2 ≤ 2 * Cr_paper r M R := by
    -- 2 · Cr_paper = 16 M² R/(1-r)² · (1 + 16R/(1-r)³) = 16 M² R/(1-r)² + 256 M² R²/(1-r)⁵
    have h_def_Cr : 2 * Cr_paper r M R =
        2 * (8 * M ^ 2 * R / (1 - r) ^ 2 * (1 + 16 * R / (1 - r) ^ 3)) := by
      rw [show Cr_paper r M R = 8 * M ^ 2 * R / (1 - r) ^ 2 * (1 + 16 * R / (1 - r) ^ 3) from rfl]
    rw [h_def_Cr]
    -- Multiply both sides by (1-r)⁵ to clear denominators (positive)
    have h1mr5_pos : 0 < (1 - r) ^ 5 := by positivity
    have h_lhs : 32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2 =
        32 * M ^ 2 * R * (R + 1) * (1 - r) ^ 3 / (1 - r) ^ 5 := by
      have h_pow : (1 - r) ^ 5 = (1 - r) ^ 2 * (1 - r) ^ 3 := by ring
      rw [h_pow]
      field_simp
    have h_rhs : 2 * (8 * M ^ 2 * R / (1 - r) ^ 2 * (1 + 16 * R / (1 - r) ^ 3)) =
        (16 * M ^ 2 * R * (1 - r) ^ 3 + 256 * M ^ 2 * R ^ 2) / (1 - r) ^ 5 := by
      have h_pow : (1 - r) ^ 5 = (1 - r) ^ 2 * (1 - r) ^ 3 := by ring
      rw [h_pow]
      field_simp
      ring
    rw [h_lhs, h_rhs]
    rw [div_le_div_iff₀ h1mr5_pos h1mr5_pos]
    -- Need: 32 M² R (R+1) (1-r)³ * (1-r)⁵ ≤ (16 M² R (1-r)³ + 256 M² R²) * (1-r)⁵
    -- Cancel (1-r)⁵ (positive): 32 M² R (R+1) (1-r)³ ≤ 16 M² R (1-r)³ + 256 M² R²
    -- Factor 16 M² R: 2 (R+1) (1-r)³ ≤ (1-r)³ + 16R
    -- Equivalent to: (2R+1)(1-r)³ ≤ 16R. This is alg_step_paper (multiplied by 16 M² R).
    have h_simp : 32 * M ^ 2 * R * (R + 1) * (1 - r) ^ 3 ≤
        16 * M ^ 2 * R * (1 - r) ^ 3 + 256 * M ^ 2 * R ^ 2 := by
      -- = 16 M² R · (2(R+1)(1-r)³) ≤ 16 M² R · ((1-r)³ + 16R) = 16 M² R (1-r)³ + 256 M² R²
      have h_factor : 16 * M ^ 2 * R * (2 * (R + 1) * (1 - r) ^ 3) =
          32 * M ^ 2 * R * (R + 1) * (1 - r) ^ 3 := by ring
      have h_factor2 : 16 * M ^ 2 * R * ((1 - r) ^ 3 + 16 * R) =
          16 * M ^ 2 * R * (1 - r) ^ 3 + 256 * M ^ 2 * R ^ 2 := by ring
      have h_inner : 2 * (R + 1) * (1 - r) ^ 3 ≤ (1 - r) ^ 3 + 16 * R := by
        nlinarith [h_alg]
      have h_16M2R_nn : 0 ≤ 16 * M ^ 2 * R := by positivity
      have := mul_le_mul_of_nonneg_left h_inner h_16M2R_nn
      linarith [this, h_factor, h_factor2]
    nlinarith [h_simp]
  linarith [h_bound_RM, h_target]

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, tight form).** Same hypothesis bundle as
`F_inv_p_second_deriv_bound_paper`, but with the conclusion stated in terms
of `Cr_tight r M R`, the constant the proof actually establishes before the
loose `(2R+1)(1-r)³ ≤ 16R` algebraic step is applied. Concretely:

    ‖∂²_p F_inv‖ ≤ 32 M² R (R + 1) / (1 - r)² = 2 · Cr_tight r M R.

The proof body is a copy of `F_inv_p_second_deriv_bound_paper`'s, truncated
at the `rw [h_arith]` line: `h_bound_RM` already has the tight RHS, so we
only need to rewrite `2 * Cr_tight r M R` into the same shape via
`unfold Cr_tight`. The Lagrange `1/2!` factor is absorbed in Step 6 by
calling `taylor_remainder_p` with `Cr := Cr_tight r M R`. -/
theorem F_inv_p_second_deriv_bound_tight
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M : ℝ} (hM_nn : 0 ≤ M)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_H0_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H0 (F_inv p z)‖ ≤ M)
    (h_M_He_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z)‖ ≤ M)
    (h_M_H0p_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv H0 (F_inv p z)‖ ≤ M)
    (h_M_Hep_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z)‖ ≤ M) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_tight r M (R_val_paper r) := by
  intro p hp z hz
  -- Triangle bounds: ‖Φ‖ ≤ 2M, ‖Φ'‖ ≤ 2M
  have h2M_nn : 0 ≤ 2 * M := by linarith
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set invFp := 2 * R / (1 - r) with hinvFp_def
  have hinvFp_pos : 0 < invFp := by simp [hinvFp_def]; positivity
  have hinvFp_nn : 0 ≤ invFp := le_of_lt hinvFp_pos
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  have h_Φ_bound : ‖Φ‖ ≤ 2 * M := by
    show ‖H_eta η w₀ - H0 w₀‖ ≤ 2 * M
    calc ‖H_eta η w₀ - H0 w₀‖
        ≤ ‖H_eta η w₀‖ + ‖H0 w₀‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (h_M_He_bound p hp z hz) (h_M_H0_bound p hp z hz)
      _ = 2 * M := by ring
  have h_Φ'_bound : ‖Φ'‖ ≤ 2 * M := by
    show ‖deriv (H_eta η) w₀ - deriv H0 w₀‖ ≤ 2 * M
    calc ‖deriv (H_eta η) w₀ - deriv H0 w₀‖
        ≤ ‖deriv (H_eta η) w₀‖ + ‖deriv H0 w₀‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (h_M_Hep_bound p hp z hz) (h_M_H0p_bound p hp z hz)
      _ = 2 * M := by ring
  have hD_lower : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_div_iff₀ hD_pos h1mr_pos]
    have hstep : (1 - r) ≤ ‖D‖ * (2 * R) := by
      have hmul := mul_le_mul_of_nonneg_right hD_lower (by positivity : (0 : ℝ) ≤ 2 * R)
      have hsimp : (1 - r) / (2 * R) * (2 * R) = 1 - r := by field_simp
      linarith [hsimp ▸ hmul]
    linarith
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hu_zz_bound : ‖u_zz‖ ≤ 8 * R / (1 - r) ^ 2 :=
    F_inv_second_deriv_bound_core hr0 hr1 hF_an_p hF_R_p z hz
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  have h_step_c : 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ (2 * M) * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * (2 * M) := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * (2 * M) := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * (2 * M) ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_M :
      ‖u''‖ ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) + ‖u_zz‖ * (2 * M) ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  have h_step_e : ‖u_zz‖ * (2 * M) ^ 2 ≤ (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound
    positivity
  have h_bound_RM :
      ‖u''‖ ≤ 2 * (2 * M) * ((2 * M) * invFp ^ 2) + (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 := by
    linarith
  have h_invFp_sq : invFp ^ 2 = 4 * R ^ 2 / (1 - r) ^ 2 := by
    rw [hinvFp_def]
    field_simp
    ring
  have h_arith :
      2 * (2 * M) * ((2 * M) * invFp ^ 2) + (8 * R / (1 - r) ^ 2) * (2 * M) ^ 2 =
        32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2 := by
    rw [h_invFp_sq]
    field_simp
    ring
  rw [h_arith] at h_bound_RM
  -- Final: convert `32 M² R (R+1) / (1-r)² = 2 · Cr_tight r M R`.
  have h_target_eq :
      2 * Cr_tight r M R = 32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2 := by
    unfold Cr_tight
    have h1mr_ne : (1 - r) ^ 2 ≠ 0 := ne_of_gt h1mr_sq_pos
    field_simp
    ring
  rw [h_target_eq]
  exact h_bound_RM

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, η-aware form).** Same proof structure as
`F_inv_p_second_deriv_bound_tight`, but the two triangle bounds
`‖Φ‖ ≤ 2M` and `‖Φ'‖ ≤ 2M` (which lose a factor of ≈ 36× at η = 1/100)
are replaced by direct η-aware sup-norm hypotheses
`h_M_phi_bound : ‖Φ‖ = ‖H_η − H_0‖ ≤ M_phi` and
`h_M_phi_prime_bound : ‖Φ'‖ = ‖H_η' − H_0'‖ ≤ M_phi_prime` (typically
two orders of magnitude tighter at small η). The Cauchy step
`‖u_zz‖ ≤ 8R/(1-r)²` is retained directly (the implicit-function chain
via `M_pp · invFp³` would be worse at the candidate's parameters).

Concretely:
    ‖∂²_p F_inv‖ ≤ 2 · M_phi_prime · M_phi · invFp²
                    + (8R/(1-r)²) · M_phi²
                = 2 · Cr_phi r M_phi M_phi_prime R.

The single-`M` arguments `M`, `hM_nn`, `h_M_*_bound` are dropped. -/
theorem F_inv_p_second_deriv_bound_phi
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_phi M_phi_prime : ℝ} (hM_phi_nn : 0 ≤ M_phi)
    (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_phi_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_phi)
    (h_M_phi_prime_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)‖ ≤ M_phi_prime) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi r M_phi M_phi_prime (R_val_paper r) := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set invFp := 2 * R / (1 - r) with hinvFp_def
  have hinvFp_pos : 0 < invFp := by simp [hinvFp_def]; positivity
  have hinvFp_nn : 0 ≤ invFp := le_of_lt hinvFp_pos
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- η-aware bounds (replace the triangle steps used in `_tight`).
  have h_Φ_bound : ‖Φ‖ ≤ M_phi := h_M_phi_bound p hp z hz
  have h_Φ'_bound : ‖Φ'‖ ≤ M_phi_prime := h_M_phi_prime_bound p hp z hz
  have hD_lower : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_div_iff₀ hD_pos h1mr_pos]
    have hstep : (1 - r) ≤ ‖D‖ * (2 * R) := by
      have hmul := mul_le_mul_of_nonneg_right hD_lower (by positivity : (0 : ℝ) ≤ 2 * R)
      have hsimp : (1 - r) / (2 * R) * (2 * R) = 1 - r := by field_simp
      linarith [hsimp ▸ hmul]
    linarith
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hu_zz_bound : ‖u_zz‖ ≤ 8 * R / (1 - r) ^ 2 :=
    F_inv_second_deriv_bound_core hr0 hr1 hF_an_p hF_R_p z hz
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  -- Apply η-aware M_phi / M_phi_prime bounds (instead of triangle).
  have h_step_c :
      2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ M_phi * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * M_phi_prime := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * M_phi_prime := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * M_phi ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_Mphi :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) + ‖u_zz‖ * M_phi ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  -- Apply Cauchy bound on u_zz: ‖u_zz‖ ≤ 8R/(1-r)²
  have h_step_e : ‖u_zz‖ * M_phi ^ 2 ≤ (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound
    positivity
  have h_bound_RM :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) +
                (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    linarith
  -- Final: convert RHS to `2 · Cr_phi r M_phi M_phi_prime R`.
  have h_target_eq :
      2 * Cr_phi r M_phi M_phi_prime R =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    show 2 * Cr_phi r M_phi M_phi_prime R = _
    unfold Cr_phi
    have h1mr_ne : (1 - r) ^ 2 ≠ 0 := ne_of_gt h1mr_sq_pos
    show 2 * (M_phi * M_phi_prime * (2 * R / (1 - r)) ^ 2 +
              (4 * R / (1 - r) ^ 2) * M_phi ^ 2) =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          (8 * R / (1 - r) ^ 2) * M_phi ^ 2
    rw [hinvFp_def]
    field_simp
    ring
  rw [h_target_eq]
  exact h_bound_RM

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, η-aware form, oracle-supplied `1/‖D‖`).**

Same proof structure as `F_inv_p_second_deriv_bound_phi`, but the loose
paper bound `1/‖D‖ ≤ 2R/(1−r)` (derived via
`F_p_deriv_lower_bound_at_F_inv` from the Cauchy first-derivative
estimate) is replaced by an *abstract* parameter `inv_F_p_z` together
with an oracle hypothesis `h_invD_bound : 1 ≤ ‖D‖ · inv_F_p_z`. At
candidate parameters `inv_F_p_z ≈ 2` (versus the paper bound ≈ 28.75),
giving a ~14× tightening of `invFp` (~196× of `invFp²`) and reducing
the `M_phi · M_phi_prime · invFp²` term-1 by the same factor.

Concretely:
    ‖∂²_p F_inv‖ ≤ 2 · M_phi_prime · M_phi · inv_F_p_z²
                    + (8R/(1−r)²) · M_phi²
                = 2 · Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z. -/
theorem F_inv_p_second_deriv_bound_phi_invD
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_phi M_phi_prime : ℝ} (hM_phi_nn : 0 ≤ M_phi)
    (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_phi_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_phi)
    (h_M_phi_prime_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)‖ ≤ M_phi_prime)
    (h_invD_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        1 ≤ ‖deriv (F_p η p) (F_inv p z)‖ * inv_F_p_z) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_invD r M_phi M_phi_prime (R_val_paper r) inv_F_p_z := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  -- The new `invFp` is the abstract `inv_F_p_z` parameter.
  set invFp := inv_F_p_z with hinvFp_def
  have hinvFp_nn : 0 ≤ invFp := h_inv_F_p_z_nn
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  -- `hF_p_ne_zero` is still derived from the paper Cauchy lower bound
  -- (`F_p_deriv_lower_bound_at_F_inv`); we only use the new oracle for
  -- `h_invD_le_invFp` further down.
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- η-aware bounds.
  have h_Φ_bound : ‖Φ‖ ≤ M_phi := h_M_phi_bound p hp z hz
  have h_Φ'_bound : ‖Φ'‖ ≤ M_phi_prime := h_M_phi_prime_bound p hp z hz
  -- ‖D‖ > 0 derived from the paper Cauchy bound (same as `_phi`).
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  -- The new step: `1/‖D‖ ≤ invFp` from the oracle hypothesis directly.
  have h_invD_oracle : 1 ≤ ‖D‖ * inv_F_p_z := h_invD_bound p hp z hz
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    -- From `1 ≤ ‖D‖ * inv_F_p_z` and `‖D‖ > 0`, derive `1/‖D‖ ≤ inv_F_p_z`.
    rw [div_le_iff₀ hD_pos]
    linarith [h_invD_oracle]
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hu_zz_bound : ‖u_zz‖ ≤ 8 * R / (1 - r) ^ 2 :=
    F_inv_second_deriv_bound_core hr0 hr1 hF_an_p hF_R_p z hz
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  -- Apply η-aware M_phi / M_phi_prime bounds (instead of triangle).
  have h_step_c :
      2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ M_phi * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * M_phi_prime := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * M_phi_prime := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * M_phi ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_Mphi :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) + ‖u_zz‖ * M_phi ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  -- Apply Cauchy bound on u_zz: ‖u_zz‖ ≤ 8R/(1-r)²
  have h_step_e : ‖u_zz‖ * M_phi ^ 2 ≤ (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound
    positivity
  have h_bound_RM :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) +
                (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    linarith
  -- Final: convert RHS to `2 · Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z`.
  have h_target_eq :
      2 * Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          (8 * R / (1 - r) ^ 2) * M_phi ^ 2 := by
    show 2 * Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z = _
    unfold Cr_phi_invD
    have h1mr_ne : (1 - r) ^ 2 ≠ 0 := ne_of_gt h1mr_sq_pos
    show 2 * (M_phi * M_phi_prime * inv_F_p_z ^ 2 +
              (4 * R / (1 - r) ^ 2) * M_phi ^ 2) =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          (8 * R / (1 - r) ^ 2) * M_phi ^ 2
    rw [hinvFp_def]
    field_simp
    ring
  rw [h_target_eq]
  exact h_bound_RM

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, η-aware form, oracle-supplied `1/‖D‖` AND
`‖DD‖`).**

Same proof structure as `F_inv_p_second_deriv_bound_phi_invD`, but the
recentred-Cauchy bound on `‖u_zz‖`
(`‖u_zz‖ ≤ 8R/(1-r)²` via `F_inv_second_deriv_bound_core`) is replaced
by an aux-z-identity-driven bound
`‖u_zz‖ ≤ M_pp · inv_F_p_z³`
sourced from the identity `DD · h² + D · u_zz = 0`
(`F_inv_aux_z_identity`) together with the oracle hypotheses
`‖DD‖ ≤ M_pp` and `1 ≤ ‖D‖ · inv_F_p_z`. At candidate parameters
`M_pp ≈ 56.08` and `inv_F_p_z = 2`, giving `‖u_zz‖ ≤ 449` versus the
paper Cauchy bound ≈ 1393 — a 3.1× tightening on the dominant
term-2 chunk.

Concretely:
    ‖∂²_p F_inv‖ ≤ 2 · M_phi_prime · M_phi · inv_F_p_z²
                    + M_pp · inv_F_p_z³ · M_phi²
                = 2 · Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp. -/
theorem F_inv_p_second_deriv_bound_phi_uzz
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_phi M_phi_prime : ℝ} (hM_phi_nn : 0 ≤ M_phi)
    (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (M_pp : ℝ) (h_M_pp_nn : 0 ≤ M_pp)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_phi_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_phi)
    (h_M_phi_prime_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)‖ ≤ M_phi_prime)
    (h_invD_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        1 ≤ ‖deriv (F_p η p) (F_inv p z)‖ * inv_F_p_z)
    (h_M_pp_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖ ≤ M_pp) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  -- The new `invFp` is the abstract `inv_F_p_z` parameter.
  set invFp := inv_F_p_z with hinvFp_def
  have hinvFp_nn : 0 ≤ invFp := h_inv_F_p_z_nn
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- η-aware bounds.
  have h_Φ_bound : ‖Φ‖ ≤ M_phi := h_M_phi_bound p hp z hz
  have h_Φ'_bound : ‖Φ'‖ ≤ M_phi_prime := h_M_phi_prime_bound p hp z hz
  -- Oracle bound on ‖DD‖ (the M_pp oracle).
  have h_DD_bound : ‖DD‖ ≤ M_pp := h_M_pp_bound p hp z hz
  -- ‖D‖ > 0 derived from the paper Cauchy bound (same as `_phi_invD`).
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  -- The new step: `1/‖D‖ ≤ invFp` from the oracle hypothesis directly.
  have h_invD_oracle : 1 ≤ ‖D‖ * inv_F_p_z := h_invD_bound p hp z hz
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_iff₀ hD_pos]
    linarith [h_invD_oracle]
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  -- NEW: derive `‖u_zz‖ ≤ M_pp * invFp ^ 3` from `hAux_norm`,
  -- `‖DD‖ ≤ M_pp`, and `‖h_z‖ ≤ invFp`.
  -- Step: ‖u_zz‖ = ‖DD‖ * ‖h_z‖^2 / ‖D‖ = ‖DD‖ * ‖h_z‖^3 (since ‖h_z‖ = 1/‖D‖)
  --                ≤ M_pp * invFp^3.
  have h_uzz_eq_div : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    field_simp
    linarith [hAux_norm]
  have h_hz_cube : ‖h_z‖ ^ 2 / ‖D‖ = ‖h_z‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  have h_uzz_eq_cube : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 3 := by
    rw [h_uzz_eq_div]
    have : ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ = ‖DD‖ * (‖h_z‖ ^ 2 / ‖D‖) := by ring
    rw [this, h_hz_cube]
  have h_DD_nn : 0 ≤ ‖DD‖ := norm_nonneg _
  have h_invFp_cube_bound : ‖h_z‖ ^ 3 ≤ invFp ^ 3 := by
    have h_pow := pow_le_pow_left₀ hh_z_nn hh_z_bound 3
    exact h_pow
  have h_invFp_cube_nn : 0 ≤ invFp ^ 3 := by positivity
  have hu_zz_bound : ‖u_zz‖ ≤ M_pp * invFp ^ 3 := by
    rw [h_uzz_eq_cube]
    have h1 : ‖DD‖ * ‖h_z‖ ^ 3 ≤ ‖DD‖ * invFp ^ 3 :=
      mul_le_mul_of_nonneg_left h_invFp_cube_bound h_DD_nn
    have h2 : ‖DD‖ * invFp ^ 3 ≤ M_pp * invFp ^ 3 :=
      mul_le_mul_of_nonneg_right h_DD_bound h_invFp_cube_nn
    linarith
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  -- Apply η-aware M_phi / M_phi_prime bounds (instead of triangle).
  have h_step_c :
      2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ M_phi * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * M_phi_prime := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * M_phi_prime := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * M_phi ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_Mphi :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) + ‖u_zz‖ * M_phi ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  -- NEW: Apply aux-z-identity-driven bound on u_zz: ‖u_zz‖ ≤ M_pp · invFp³
  have h_M_phi_sq_nn : 0 ≤ M_phi ^ 2 := by positivity
  have h_step_e : ‖u_zz‖ * M_phi ^ 2 ≤ M_pp * invFp ^ 3 * M_phi ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound h_M_phi_sq_nn
  have h_bound_RM :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) +
                M_pp * invFp ^ 3 * M_phi ^ 2 := by
    linarith
  -- Final: convert RHS to `2 · Cr_phi_uzz r M_phi M_phi_prime invFp M_pp`.
  have h_target_eq :
      2 * Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          M_pp * invFp ^ 3 * M_phi ^ 2 := by
    show 2 * Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp = _
    unfold Cr_phi_uzz
    show 2 * (M_phi * M_phi_prime * inv_F_p_z ^ 2 +
              (1 / 2) * M_pp * inv_F_p_z ^ 3 * M_phi ^ 2) =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          M_pp * invFp ^ 3 * M_phi ^ 2
    rw [hinvFp_def]
    ring
  rw [h_target_eq]
  exact h_bound_RM

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, η-aware form, oracle-supplied direct
`‖u_zz‖` bound).**

Same proof structure as `F_inv_p_second_deriv_bound_phi_uzz`, but
instead of consuming TWO oracle hypotheses (`‖DD‖ ≤ M_pp` and
`1 ≤ ‖D‖ · inv_F_p_z`) and combining them into the loose triangle
bound `‖u_zz‖ ≤ M_pp · inv_F_p_z³`, this version consumes a SINGLE
oracle hypothesis on the joint analytic quotient
`‖DD‖ ≤ ‖D‖³ · u_zz_bound`. By `‖u_zz‖ = ‖DD‖/‖D‖³` (from the aux
z-identity together with `‖h_z‖ = 1/‖D‖`), this directly gives
`‖u_zz‖ ≤ u_zz_bound`. The `inv_F_p_z` parameter is still needed
for the term-1 chunk (which tracks the first-derivative bound on
`F_inv`), but the term-2 chunk is one factor simpler.

At candidate parameters `u_zz_bound ≈ 1.55` versus the V11
`M_pp · inv_F_p_z³ ≈ 449` — a ~289× tightening on the dominant
term-2 chunk.

Concretely:
    ‖∂²_p F_inv‖ ≤ 2 · M_phi_prime · M_phi · inv_F_p_z²
                    + u_zz_bound · M_phi²
                = 2 · Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound. -/
theorem F_inv_p_second_deriv_bound_phi_uzz_direct
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_phi M_phi_prime : ℝ} (hM_phi_nn : 0 ≤ M_phi)
    (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (u_zz_bound : ℝ) (h_u_zz_nn : 0 ≤ u_zz_bound)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_phi_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_phi)
    (h_M_phi_prime_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)‖ ≤ M_phi_prime)
    (h_invD_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        1 ≤ ‖deriv (F_p η p) (F_inv p z)‖ * inv_F_p_z)
    (h_u_zz_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * u_zz_bound) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  -- The new `invFp` is the abstract `inv_F_p_z` parameter.
  set invFp := inv_F_p_z with hinvFp_def
  have hinvFp_nn : 0 ≤ invFp := h_inv_F_p_z_nn
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- η-aware bounds.
  have h_Φ_bound : ‖Φ‖ ≤ M_phi := h_M_phi_bound p hp z hz
  have h_Φ'_bound : ‖Φ'‖ ≤ M_phi_prime := h_M_phi_prime_bound p hp z hz
  -- ‖D‖ > 0 derived from the paper Cauchy bound.
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  -- The new step: `1/‖D‖ ≤ invFp` from the oracle hypothesis directly.
  have h_invD_oracle : 1 ≤ ‖D‖ * inv_F_p_z := h_invD_bound p hp z hz
  have h_invD_le_invFp : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_iff₀ hD_pos]
    linarith [h_invD_oracle]
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_bound : ‖h_z‖ ≤ invFp := by
    rw [hh_z_norm]
    exact h_invD_le_invFp
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  -- NEW (direct): derive `‖u_zz‖ ≤ u_zz_bound` from
  -- `h_u_zz_bound : ‖DD‖ ≤ ‖D‖^3 · u_zz_bound`, the aux-z identity
  -- `‖DD‖ * ‖h_z‖^2 = ‖D‖ * ‖u_zz‖`, and `‖h_z‖ = 1/‖D‖`.
  --
  -- Rearrange aux-z: ‖u_zz‖ = ‖DD‖ * ‖h_z‖^2 / ‖D‖
  --                          = ‖DD‖ / ‖D‖^3   (substituting ‖h_z‖² = 1/‖D‖²)
  --                          ≤ (‖D‖^3 · u_zz_bound) / ‖D‖^3 = u_zz_bound.
  have h_DD_oracle : ‖DD‖ ≤ ‖D‖ ^ 3 * u_zz_bound := by
    show ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖ ≤
      ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * u_zz_bound
    exact h_u_zz_bound p hp z hz
  have h_DD_nn : 0 ≤ ‖DD‖ := norm_nonneg _
  -- ‖u_zz‖ = ‖DD‖ * ‖h_z‖^2 / ‖D‖ (rearrangement of hAux_norm).
  have h_uzz_eq_div : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    field_simp
    linarith [hAux_norm]
  -- ‖h_z‖^2 / ‖D‖ = ‖h_z‖^3 (since ‖h_z‖ = 1/‖D‖).
  have h_hz_cube : ‖h_z‖ ^ 2 / ‖D‖ = ‖h_z‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  -- ‖u_zz‖ = ‖DD‖ * ‖h_z‖^3.
  have h_uzz_eq_cube : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 3 := by
    rw [h_uzz_eq_div]
    have : ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ = ‖DD‖ * (‖h_z‖ ^ 2 / ‖D‖) := by ring
    rw [this, h_hz_cube]
  -- ‖h_z‖^3 = 1/‖D‖^3.
  have h_hz_cube_inv : ‖h_z‖ ^ 3 = 1 / ‖D‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  -- ‖u_zz‖ = ‖DD‖ / ‖D‖^3.
  have h_uzz_eq_quot : ‖u_zz‖ = ‖DD‖ / ‖D‖ ^ 3 := by
    rw [h_uzz_eq_cube, h_hz_cube_inv]
    ring
  -- Now apply h_DD_oracle: ‖u_zz‖ ≤ u_zz_bound.
  have hD_cube_pos : 0 < ‖D‖ ^ 3 := by positivity
  have hu_zz_bound : ‖u_zz‖ ≤ u_zz_bound := by
    rw [h_uzz_eq_quot]
    rw [div_le_iff₀ hD_cube_pos]
    linarith [h_DD_oracle]
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have h_form_A_norm : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have hh : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hh]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  have h_form_AB : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm
    rw [hu'_norm_h] at h
    rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) from rfl]
    have h_DD_sub : ‖DD‖ * (‖Φ‖ * ‖h_z‖) ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [h_sq]
      have : ‖DD‖ * (‖h_z‖ ^ 2 * ‖Φ‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
      rw [this, hAux_norm]
    rw [h_DD_sub] at h
    exact h
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [this]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  have h_hz_sq_bound : ‖h_z‖ ^ 2 ≤ invFp ^ 2 := by
    apply pow_le_pow_left₀ hh_z_nn hh_z_bound
  have h_inner_eq : ‖Φ‖ * ‖h_z‖ / ‖D‖ = ‖Φ‖ * ‖h_z‖ ^ 2 := by
    rw [hh_z_norm]
    field_simp
  have h_bound_intermediate :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_bound_divD
    have h_eq_frac :
        2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) := by
      rw [show 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖) / ‖D‖ = 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ / ‖D‖) by ring]
      rw [h_inner_eq]
    linarith [h_eq_frac ▸ h]
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΦ'_nn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_step_a : ‖Φ‖ * ‖h_z‖ ^ 2 ≤ ‖Φ‖ * invFp ^ 2 :=
    mul_le_mul_of_nonneg_left h_hz_sq_bound hΦ_nn
  have h_step_b : 2 * ‖Φ'‖ * (‖Φ‖ * ‖h_z‖ ^ 2) ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_step_a
    have : 0 ≤ 2 * ‖Φ'‖ := by linarith
    exact this
  have h_bound_invFp :
      ‖u''‖ ≤ 2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) + ‖u_zz‖ * ‖Φ‖ ^ 2 :=
    le_trans h_bound_intermediate (by linarith)
  -- Apply η-aware M_phi / M_phi_prime bounds.
  have h_step_c :
      2 * ‖Φ'‖ * (‖Φ‖ * invFp ^ 2) ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) := by
    have h1 : ‖Φ‖ * invFp ^ 2 ≤ M_phi * invFp ^ 2 := by
      apply mul_le_mul_of_nonneg_right h_Φ_bound (by positivity)
    have h2 : 2 * ‖Φ'‖ ≤ 2 * M_phi_prime := by linarith
    have h_inner_nn : 0 ≤ ‖Φ‖ * invFp ^ 2 := by positivity
    have h_outer_nn : 0 ≤ 2 * M_phi_prime := by linarith
    exact mul_le_mul h2 h1 h_inner_nn h_outer_nn
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ ‖u_zz‖ * M_phi ^ 2 := by
    have h := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    apply mul_le_mul_of_nonneg_left h hu_zz_nn
  have h_bound_Mphi :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) + ‖u_zz‖ * M_phi ^ 2 := by
    linarith [h_bound_invFp, h_step_c, h_step_d]
  -- Apply the direct u_zz_bound: ‖u_zz‖ ≤ u_zz_bound (the new step).
  have h_M_phi_sq_nn : 0 ≤ M_phi ^ 2 := by positivity
  have h_step_e : ‖u_zz‖ * M_phi ^ 2 ≤ u_zz_bound * M_phi ^ 2 := by
    apply mul_le_mul_of_nonneg_right hu_zz_bound h_M_phi_sq_nn
  have h_bound_RM :
      ‖u''‖ ≤ 2 * M_phi_prime * (M_phi * invFp ^ 2) +
                u_zz_bound * M_phi ^ 2 := by
    linarith
  -- Final: convert RHS to `2 · Cr_phi_uzz_direct r M_phi M_phi_prime invFp u_zz_bound`.
  have h_target_eq :
      2 * Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          u_zz_bound * M_phi ^ 2 := by
    show 2 * Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound = _
    unfold Cr_phi_uzz_direct
    show 2 * (M_phi * M_phi_prime * inv_F_p_z ^ 2 +
              (1 / 2) * u_zz_bound * M_phi ^ 2) =
        2 * M_phi_prime * (M_phi * invFp ^ 2) +
          u_zz_bound * M_phi ^ 2
    rw [hinvFp_def]
    ring
  rw [h_target_eq]
  exact h_bound_RM

set_option maxHeartbeats 1600000 in
/-- **Step 5 (paper-faithful, η-aware form, oracle-supplied joint
`‖Phi · Phi' / D²‖` bound + direct ‖u_zz‖ bound).**

Same proof structure as `F_inv_p_second_deriv_bound_phi_uzz_direct`,
but instead of consuming THREE oracle hypotheses for term-1 (`‖Phi‖ ≤
M_phi`, `‖Phi'‖ ≤ M_phi_prime`, `1 ≤ ‖D‖ · inv_F_p_z`) and combining
them into the loose triangle bound `M_phi · M_phi_prime · inv_F_p_z²`,
this version consumes a SINGLE oracle hypothesis on the joint
analytic quotient `‖Phi · Phi'‖ ≤ ‖D‖² · joint_phi_phip_invD2`. By
the joint sup binding at a single (p, w) rather than separate suprema
each binding at potentially different (p, w), this is fundamentally
tighter than the product. The term-2 chunk (using `h_M_phi_bound`
and `h_u_zz_bound`) is byte-identical.

Concretely:
    ‖∂²_p F_inv‖ ≤ 2 · joint_phi_phip_invD2 + u_zz_bound · M_phi²
                = 2 · Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound. -/
theorem F_inv_p_second_deriv_bound_phi_uzz_direct_joint
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_phi : ℝ} (hM_phi_nn : 0 ≤ M_phi)
    (joint_phi_phip_invD2 : ℝ) (h_joint_nn : 0 ≤ joint_phi_phip_invD2)
    (u_zz_bound : ℝ) (h_u_zz_nn : 0 ≤ u_zz_bound)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_M_phi_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_phi)
    (h_joint_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖(H_eta η (F_inv p z) - H0 (F_inv p z)) *
          (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 2 * joint_phi_phip_invD2)
    (h_u_zz_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * u_zz_bound) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- η-aware bounds.
  have h_Φ_bound : ‖Φ‖ ≤ M_phi := h_M_phi_bound p hp z hz
  -- ‖D‖ > 0 derived from the paper Cauchy bound.
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  -- Direct: derive `‖u_zz‖ ≤ u_zz_bound` from
  -- `h_u_zz_bound : ‖DD‖ ≤ ‖D‖^3 · u_zz_bound`, the aux-z identity
  -- `‖DD‖ * ‖h_z‖^2 = ‖D‖ * ‖u_zz‖`, and `‖h_z‖ = 1/‖D‖`.
  have h_DD_oracle : ‖DD‖ ≤ ‖D‖ ^ 3 * u_zz_bound := by
    show ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖ ≤
      ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * u_zz_bound
    exact h_u_zz_bound p hp z hz
  have h_DD_nn : 0 ≤ ‖DD‖ := norm_nonneg _
  have h_uzz_eq_div : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    field_simp
    linarith [hAux_norm]
  have h_hz_cube : ‖h_z‖ ^ 2 / ‖D‖ = ‖h_z‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  have h_uzz_eq_cube : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 3 := by
    rw [h_uzz_eq_div]
    have : ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ = ‖DD‖ * (‖h_z‖ ^ 2 / ‖D‖) := by ring
    rw [this, h_hz_cube]
  have h_hz_cube_inv : ‖h_z‖ ^ 3 = 1 / ‖D‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  have h_uzz_eq_quot : ‖u_zz‖ = ‖DD‖ / ‖D‖ ^ 3 := by
    rw [h_uzz_eq_cube, h_hz_cube_inv]
    ring
  have hD_cube_pos : 0 < ‖D‖ ^ 3 := by positivity
  have hu_zz_bound : ‖u_zz‖ ≤ u_zz_bound := by
    rw [h_uzz_eq_quot]
    rw [div_le_iff₀ hD_cube_pos]
    linarith [h_DD_oracle]
  -- Joint oracle bound: ‖Φ · Φ'‖ ≤ ‖D‖² · joint_phi_phip_invD2.
  have h_joint_oracle : ‖Φ * Φ'‖ ≤ ‖D‖ ^ 2 * joint_phi_phip_invD2 := by
    show ‖(H_eta η (F_inv p z) - H0 (F_inv p z)) *
          (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))‖ ≤
        ‖deriv (F_p η p) (F_inv p z)‖ ^ 2 * joint_phi_phip_invD2
    exact h_joint_bound p hp z hz
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  -- Now bound ‖D‖ * ‖u''‖, but use a JOINT bound on ‖Φ' * Φ‖ rather
  -- than splitting into ‖Φ'‖ * ‖Φ‖.
  -- Using u' = -Φ/D (i.e. ‖u'‖ = ‖Φ‖/‖D‖), we have
  -- 2 * Φ' * u' = -2 * Φ' * Φ / D, hence ‖2 * Φ' * u'‖ = 2 * ‖Φ' * Φ‖ / ‖D‖.
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  -- term-1 norm: 2 * Φ' * u' = -2 * Φ' * Φ / D, so ‖2 * Φ' * u'‖ = 2 * ‖Φ' * Φ‖ / ‖D‖.
  have h_term1_norm : ‖2 * Φ' * u'‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ := by
    have hu'_eq : u' = -Φ / D := hu'_value
    have h1 : (2 * Φ' * u' : ℂ) = -(2 * (Φ * Φ') / D) := by
      rw [hu'_eq]
      field_simp
    rw [h1, norm_neg]
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    rw [show (2 * (Φ * Φ') / D : ℂ) = (2 : ℂ) * (Φ * Φ') / D by ring]
    rw [norm_div, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
  -- Combine: ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖DD‖ * ‖u'‖^2.
  have h_form_A_norm_joint : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ := h_term1_norm
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  -- Substitute h_DD_u'_sq into h_form_A_norm_joint.
  have h_form_AB_joint : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm_joint
    rw [h_DD_u'_sq] at h
    exact h
  -- Divide by ‖D‖ to get the bound on ‖u''‖.
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB_joint hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have ht1 : (2 * ‖Φ * Φ'‖ / ‖D‖) / ‖D‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 := by
        rw [div_div, sq]
      have ht2 : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [ht1, ht2]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  -- Apply joint oracle: ‖Φ * Φ'‖ ≤ ‖D‖² * joint_phi_phip_invD2.
  -- Hence 2 * ‖Φ * Φ'‖ / ‖D‖² ≤ 2 * joint_phi_phip_invD2.
  have hD_sq_pos : 0 < ‖D‖ ^ 2 := by positivity
  have h_term1_joint_bound : 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 ≤ 2 * joint_phi_phip_invD2 := by
    rw [div_le_iff₀ hD_sq_pos]
    have h_norm_nn : 0 ≤ ‖Φ * Φ'‖ := norm_nonneg _
    have : 2 * ‖Φ * Φ'‖ ≤ 2 * (‖D‖ ^ 2 * joint_phi_phip_invD2) := by
      linarith [h_joint_oracle]
    linarith
  -- Apply ‖u_zz‖ * ‖Φ‖² ≤ u_zz_bound * M_phi².
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have h_M_phi_sq_nn : 0 ≤ M_phi ^ 2 := by positivity
  have h_step_d : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ u_zz_bound * M_phi ^ 2 := by
    have h1 : ‖Φ‖ ^ 2 ≤ M_phi ^ 2 := pow_le_pow_left₀ hΦ_nn h_Φ_bound 2
    have h2 : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ u_zz_bound * ‖Φ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right hu_zz_bound (by positivity)
    have h3 : u_zz_bound * ‖Φ‖ ^ 2 ≤ u_zz_bound * M_phi ^ 2 := by
      apply mul_le_mul_of_nonneg_left h1 h_u_zz_nn
    linarith
  have h_bound_RM :
      ‖u''‖ ≤ 2 * joint_phi_phip_invD2 + u_zz_bound * M_phi ^ 2 := by
    linarith [h_bound_divD, h_term1_joint_bound, h_step_d]
  -- Final: convert RHS to `2 · Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound`.
  have h_target_eq :
      2 * Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound =
        2 * joint_phi_phip_invD2 + u_zz_bound * M_phi ^ 2 := by
    show 2 * Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound = _
    unfold Cr_phi_uzz_direct_joint
    ring
  rw [h_target_eq]
  exact h_bound_RM

/-- **Term-1 + term-2 joint variant.** Replaces V14's term-2 triangle
product `u_zz_bound · M_phi²` with a single direct oracle on the joint
analytic quantity `‖DD · Phi² / D³‖` (which equals `‖u_zz · Phi²‖` via
the aux-z identity). Bounds `‖∂²_p F_inv‖ ≤ 2 ·
Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq`. -/
theorem F_inv_p_second_deriv_bound_phi_uzz_direct_joint2
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    (joint_phi_phip_invD2 : ℝ) (h_joint_nn : 0 ≤ joint_phi_phip_invD2)
    (uzz_phi_sq : ℝ) (h_uzz_phi_sq_nn : 0 ≤ uzz_phi_sq)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_joint_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖(H_eta η (F_inv p z) - H0 (F_inv p z)) *
          (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 2 * joint_phi_phip_invD2)
    (h_uzz_phi_sq_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖iteratedDeriv 2 (F_p η p) (F_inv p z) *
          (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * uzz_phi_sq) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  set h_z := deriv (F_inv p) z with hhz_def
  set u_zz := iteratedDeriv 2 (F_inv p) z with huzz_def
  -- ‖D‖ > 0 derived from the paper Cauchy bound.
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have h_Dh_eq_one : D * h_z = 1 := by
    show deriv (F_p η p) w₀ * deriv (F_inv p) z = 1
    exact Dh_eq_one η hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz_r1
  have hh_z_norm : ‖h_z‖ = 1 / ‖D‖ := by
    have h := congrArg norm h_Dh_eq_one
    rw [norm_mul] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1] at h
    field_simp
    linarith
  have hh_z_nn : 0 ≤ ‖h_z‖ := norm_nonneg _
  have hu_zz_nn : 0 ≤ ‖u_zz‖ := norm_nonneg _
  have hAux := F_inv_aux_z_identity η hr0 hr1 F_inv hF_an hF_inv_eq hF_S p hp z hz
  have hAux_norm : ‖DD‖ * ‖h_z‖ ^ 2 = ‖D‖ * ‖u_zz‖ := by
    have hrearrange : DD * h_z ^ 2 = -(D * u_zz) := by
      show iteratedDeriv 2 (F_p η p) (F_inv p z) * (deriv (F_inv p) z) ^ 2 =
        -(deriv (F_p η p) (F_inv p z) * iteratedDeriv 2 (F_inv p) z)
      linear_combination hAux
    have hnorm := congrArg norm hrearrange
    rw [norm_neg, norm_mul, norm_mul, norm_pow] at hnorm
    exact hnorm
  -- ‖u_zz‖ = ‖DD‖ / ‖D‖³ via the aux-z identity (kept for the
  -- ‖u_zz‖ * ‖Φ‖² rewrite below, even though the final term-2 bound
  -- comes via the joint oracle on ‖DD * Φ²‖ directly).
  have h_DD_nn : 0 ≤ ‖DD‖ := norm_nonneg _
  have h_uzz_eq_div : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    field_simp
    linarith [hAux_norm]
  have h_hz_cube : ‖h_z‖ ^ 2 / ‖D‖ = ‖h_z‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  have h_uzz_eq_cube : ‖u_zz‖ = ‖DD‖ * ‖h_z‖ ^ 3 := by
    rw [h_uzz_eq_div]
    have : ‖DD‖ * ‖h_z‖ ^ 2 / ‖D‖ = ‖DD‖ * (‖h_z‖ ^ 2 / ‖D‖) := by ring
    rw [this, h_hz_cube]
  have h_hz_cube_inv : ‖h_z‖ ^ 3 = 1 / ‖D‖ ^ 3 := by
    rw [hh_z_norm]
    field_simp
  have h_uzz_eq_quot : ‖u_zz‖ = ‖DD‖ / ‖D‖ ^ 3 := by
    rw [h_uzz_eq_cube, h_hz_cube_inv]
    ring
  have hD_cube_pos : 0 < ‖D‖ ^ 3 := by positivity
  -- Joint oracle bound for term-1:
  -- ‖Φ · Φ'‖ ≤ ‖D‖² * joint_phi_phip_invD2.
  have h_joint_oracle : ‖Φ * Φ'‖ ≤ ‖D‖ ^ 2 * joint_phi_phip_invD2 := by
    show ‖(H_eta η (F_inv p z) - H0 (F_inv p z)) *
          (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))‖ ≤
        ‖deriv (F_p η p) (F_inv p z)‖ ^ 2 * joint_phi_phip_invD2
    exact h_joint_bound p hp z hz
  -- New joint oracle bound for term-2:
  -- ‖DD · Φ²‖ ≤ ‖D‖³ * uzz_phi_sq.
  have h_uzz_phi_sq_oracle : ‖DD * Φ ^ 2‖ ≤ ‖D‖ ^ 3 * uzz_phi_sq := by
    show ‖iteratedDeriv 2 (F_p η p) (F_inv p z) *
          (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖ ≤
        ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * uzz_phi_sq
    exact h_uzz_phi_sq_bound p hp z hz
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  -- Now bound ‖D‖ * ‖u''‖, but use a JOINT bound on ‖Φ' * Φ‖ rather
  -- than splitting into ‖Φ'‖ * ‖Φ‖.
  -- Using u' = -Φ/D (i.e. ‖u'‖ = ‖Φ‖/‖D‖), we have
  -- 2 * Φ' * u' = -2 * Φ' * Φ / D, hence ‖2 * Φ' * u'‖ = 2 * ‖Φ' * Φ‖ / ‖D‖.
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  have hu'_norm_h : ‖u'‖ = ‖Φ‖ * ‖h_z‖ := by
    rw [hu'_norm, hh_z_norm]
    field_simp
  have h_DD_u'_sq : ‖DD‖ * ‖u'‖ ^ 2 = ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    rw [hu'_norm_h]
    have h_sq : (‖Φ‖ * ‖h_z‖) ^ 2 = ‖Φ‖ ^ 2 * ‖h_z‖ ^ 2 := by ring
    rw [h_sq]
    have h_step : ‖DD‖ * (‖Φ‖ ^ 2 * ‖h_z‖ ^ 2) = ‖DD‖ * ‖h_z‖ ^ 2 * ‖Φ‖ ^ 2 := by ring
    rw [h_step, hAux_norm]
  -- term-1 norm: 2 * Φ' * u' = -2 * Φ' * Φ / D, so ‖2 * Φ' * u'‖ = 2 * ‖Φ' * Φ‖ / ‖D‖.
  have h_term1_norm : ‖2 * Φ' * u'‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ := by
    have hu'_eq : u' = -Φ / D := hu'_value
    have h1 : (2 * Φ' * u' : ℂ) = -(2 * (Φ * Φ') / D) := by
      rw [hu'_eq]
      field_simp
    rw [h1, norm_neg]
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    rw [show (2 * (Φ * Φ') / D : ℂ) = (2 : ℂ) * (Φ * Φ') / D by ring]
    rw [norm_div, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
  -- Combine: ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖DD‖ * ‖u'‖^2.
  have h_form_A_norm_joint : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖DD‖ * ‖u'‖ ^ 2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ := h_term1_norm
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖ ^ 2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  -- Substitute h_DD_u'_sq into h_form_A_norm_joint.
  have h_form_AB_joint : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have h := h_form_A_norm_joint
    rw [h_DD_u'_sq] at h
    exact h
  -- Divide by ‖D‖ to get the bound on ‖u''‖.
  have h_bound_divD :
      ‖u''‖ ≤ 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
    have hD_ne_real : ‖D‖ ≠ 0 := ne_of_gt hD_pos
    have h_step1 : ‖D‖ * ‖u''‖ / ‖D‖ ≤
        (2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ :=
      div_le_div_of_nonneg_right h_form_AB_joint hD_pos.le
    have h_lhs : ‖D‖ * ‖u''‖ / ‖D‖ = ‖u''‖ := by
      field_simp
    have h_rhs :
        (2 * ‖Φ * Φ'‖ / ‖D‖ + ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2) / ‖D‖ =
          2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 + ‖u_zz‖ * ‖Φ‖ ^ 2 := by
      rw [add_div]
      have ht1 : (2 * ‖Φ * Φ'‖ / ‖D‖) / ‖D‖ = 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 := by
        rw [div_div, sq]
      have ht2 : ‖D‖ * ‖u_zz‖ * ‖Φ‖ ^ 2 / ‖D‖ = ‖u_zz‖ * ‖Φ‖ ^ 2 := by
        field_simp
      rw [ht1, ht2]
    linarith [h_lhs ▸ h_step1, h_rhs ▸ h_step1]
  -- Apply joint oracle: ‖Φ * Φ'‖ ≤ ‖D‖² * joint_phi_phip_invD2.
  -- Hence 2 * ‖Φ * Φ'‖ / ‖D‖² ≤ 2 * joint_phi_phip_invD2.
  have hD_sq_pos : 0 < ‖D‖ ^ 2 := by positivity
  have h_term1_joint_bound : 2 * ‖Φ * Φ'‖ / ‖D‖ ^ 2 ≤ 2 * joint_phi_phip_invD2 := by
    rw [div_le_iff₀ hD_sq_pos]
    have h_norm_nn : 0 ≤ ‖Φ * Φ'‖ := norm_nonneg _
    have : 2 * ‖Φ * Φ'‖ ≤ 2 * (‖D‖ ^ 2 * joint_phi_phip_invD2) := by
      linarith [h_joint_oracle]
    linarith
  -- Bound term-2 directly via the joint oracle:
  -- ‖DD · Phi² / D³‖ ≤ uzz_phi_sq, equivalently ‖DD · Phi²‖ ≤ ‖D‖³ · uzz_phi_sq.
  -- Rewrite the LHS ‖u_zz‖ · ‖Φ‖² in the form ‖DD · Φ²‖ / ‖D‖³.
  have h_term2_eq_quot : ‖u_zz‖ * ‖Φ‖ ^ 2 = ‖DD * Φ ^ 2‖ / ‖D‖ ^ 3 := by
    rw [norm_mul, norm_pow, h_uzz_eq_quot]
    ring
  have h_term2_le : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ uzz_phi_sq := by
    rw [h_term2_eq_quot]
    rw [div_le_iff₀ hD_cube_pos]
    linarith [h_uzz_phi_sq_oracle]
  have h_bound_RM :
      ‖u''‖ ≤ 2 * joint_phi_phip_invD2 + uzz_phi_sq := by
    linarith [h_bound_divD, h_term1_joint_bound, h_term2_le]
  -- Final: convert RHS to `2 · Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq`.
  have h_target_eq :
      2 * Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq =
        2 * joint_phi_phip_invD2 + uzz_phi_sq := by
    show 2 * Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq = _
    unfold Cr_phi_uzz_direct_joint2
    ring
  rw [h_target_eq]
  exact h_bound_RM

/-- **Merged-numerator variant.** Replaces V23's two-oracle triangle
product `Cr_phi_uzz_direct_joint2 joint uzz = joint + (1/2)·uzz` with
a single direct oracle on the *exact* `|u''|` quotient
`‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³`.

The form-A identity (`h_form_A_eq`) combined with `u' = -Phi/D`
gives `D · u'' = -(2·Phi'·u' + DD·u'·u') = -(−2·Phi·Phi'/D + DD·Phi²/D²)
= (2·Phi·Phi'·D − DD·Phi²) / D²`, hence `D³ · u'' = 2·Phi·Phi'·D −
DD·Phi²` and ‖u''‖ = ‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³ exactly. The
merged oracle hypothesis `‖2·Phi·Phi'·D − DD·Phi²‖ ≤ ‖D‖³ ·
merged_uderiv` then gives `‖u''‖ ≤ merged_uderiv`, equivalently
`‖u''‖ ≤ 2 · Cr_phi_uzz_merged merged_uderiv` (since
`Cr_phi_uzz_merged = (1/2) · merged_uderiv`). -/
theorem F_inv_p_second_deriv_bound_phi_uzz_merged
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    (merged_uderiv : ℝ) (h_merged_nn : 0 ≤ merged_uderiv)
    (F_inv : ℝ → ℂ → ℂ)
    (hF_an : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)))
    (hF_inv_eq : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_p η p (F_inv p z) = z)
    (hF_S : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), F_inv p z ∈ S)
    (hF_R : ∀ p ∈ Set.Ioo (0 : ℝ) pr,
      ∀ z ∈ disk (r1 r), ‖F_inv p z‖ ≤ R_val_paper r)
    (hF_p_contdiff : ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q z) (Set.Ioo (0 : ℝ) pr))
    (h_merged_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖2 * (H_eta η (F_inv p z) - H0 (F_inv p z)) *
            (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)) *
            deriv (F_p η p) (F_inv p z)
          - iteratedDeriv 2 (F_p η p) (F_inv p z) *
            (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖
          ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * merged_uderiv) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_phi_uzz_merged merged_uderiv := by
  intro p hp z hz
  -- Constants
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hR_nn : 0 ≤ R_val_paper r := le_of_lt hRpos
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  set R := R_val_paper r with hR_def
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) := hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  have hF_p_ne_zero : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      deriv (F_p η p') (F_inv p' z') ≠ 0 := by
    intro p' hp' z' hz'
    have hbound :=
      F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq
        hF_S hF_R p' hp' z' hz'
    intro hzero
    rw [hzero, norm_zero] at hbound
    have : (1 - r) / (2 * R_val_paper r) > 0 := by positivity
    linarith
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    exact (hId75 q hq z hz).deriv
  have hu_hasDeriv : HasDerivAt u (deriv u p) p := (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  have hderiv_u_in_set : DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    have hEq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
        iteratedDerivWithin 1 u (Set.Ioo 0 pr) q = deriv u q := by
      intro q hq
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hOpen hq]
    intro q hq
    have h_d := h1 q hq
    have h_eq_evt : (deriv u) =ᶠ[nhdsWithin q (Set.Ioo 0 pr)]
        (iteratedDerivWithin 1 u (Set.Ioo 0 pr)) := by
      apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioo 0 pr))
      intro q' hq'; exact (hEq q' hq').symm
    exact h_d.congr_of_eventuallyEq h_eq_evt (hEq q hq).symm
  have hderiv_u_diff_at : DifferentiableAt ℝ (deriv u) p :=
    (hderiv_u_in_set p hp).differentiableAt (hOpen.mem_nhds hp)
  set u'' := deriv (deriv u) p with hu''_def
  have hderiv_u_hasDeriv : HasDerivAt (deriv u) u'' p :=
    hderiv_u_diff_at.hasDerivAt
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  -- ‖D‖ > 0 derived from the paper Cauchy bound.
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have hD_cube_pos : 0 < ‖D‖ ^ 3 := by positivity
  -- Merged oracle bound:
  -- ‖2·Φ·Φ'·D − DD·Φ²‖ ≤ ‖D‖³ * merged_uderiv.
  have h_merged_oracle :
      ‖2 * Φ * Φ' * D - DD * Φ ^ 2‖ ≤ ‖D‖ ^ 3 * merged_uderiv := by
    show ‖2 * (H_eta η (F_inv p z) - H0 (F_inv p z)) *
            (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)) *
            deriv (F_p η p) (F_inv p z)
          - iteratedDeriv 2 (F_p η p) (F_inv p z) *
            (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖ ≤
        ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * merged_uderiv
    exact h_merged_bound p hp z hz
  -- Now derive the form-A identity: 2·Φ'·u' + DD·u'·u' + D·u'' = 0.
  have hF_an_p : AnalyticOnNhd ℂ (F_inv p) (disk (r1 r)) := hF_an p hp
  have hF_R_p : ∀ z' ∈ disk (r1 r), ‖F_inv p z'‖ ≤ R_val_paper r := fun z' hz' =>
    hF_R p hp z' hz'
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_diff_C : DifferentiableAt ℂ (H_eta η) w₀ :=
      (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hHe_hasDeriv_C : HasDerivAt (H_eta η) (deriv (H_eta η) w₀) w₀ :=
      hHe_diff_C.hasDerivAt
    have hH0_diff_C : DifferentiableAt ℂ H0 w₀ :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw₀_S)
    have hH0_hasDeriv_C : HasDerivAt H0 (deriv H0 w₀) w₀ :=
      hH0_diff_C.hasDerivAt
    have hHe_comp : HasDerivAt (fun q : ℝ => H_eta η (u q))
        (u' * deriv (H_eta η) w₀) p := by
      have h := hHe_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv (H_eta η) w₀ : ℂ) = u' * deriv (H_eta η) w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have hH0_comp : HasDerivAt (fun q : ℝ => H0 (u q))
        (u' * deriv H0 w₀) p := by
      have h := hH0_hasDeriv_C.scomp p hu_hasDeriv
      have hsmul : (u' • deriv H0 w₀ : ℂ) = u' * deriv H0 w₀ := by
        rw [smul_eq_mul]
      simpa [Function.comp, hsmul] using h
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) w₀ :=
    H0_analyticOnNhd.deriv w₀ hw₀_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    hderiv_H0_an_at.differentiableAt
  have h_id_H0 : iteratedDeriv 2 H0 w₀ = deriv (deriv H0) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_H0_hasDeriv : HasDerivAt (deriv H0) (iteratedDeriv 2 H0 w₀) w₀ := by
    rw [h_id_H0]; exact hderiv_H0_diff.hasDerivAt
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p := by
    have h := hderiv_H0_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 H0 w₀ : ℂ) = u' * iteratedDeriv 2 H0 w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have hderiv_He_an_at : AnalyticAt ℂ (deriv (H_eta η)) w₀ :=
    (H_eta_analyticOnNhd η).deriv w₀ hw₀_S
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    hderiv_He_an_at.differentiableAt
  have h_id_He : iteratedDeriv 2 (H_eta η) w₀ = deriv (deriv (H_eta η)) w₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_He_hasDeriv : HasDerivAt (deriv (H_eta η))
      (iteratedDeriv 2 (H_eta η) w₀) w₀ := by
    rw [h_id_He]; exact hderiv_He_diff.hasDerivAt
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p := by
    have h := hderiv_He_hasDeriv.scomp p hu_hasDeriv
    have hsmul : (u' • iteratedDeriv 2 (H_eta η) w₀ : ℂ) =
        u' * iteratedDeriv 2 (H_eta η) w₀ := by
      rw [smul_eq_mul]
    simpa [Function.comp, hsmul] using h
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  have h_Fp'_evt :
      (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                     (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        =ᶠ[nhds p] (fun q : ℝ => deriv (F_p η q) (F_inv q z)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    have hu_q_S : F_inv q z ∈ S := hF_S q hq z hz_r1
    show ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) + (↑q : ℂ) * deriv (H_eta η) (F_inv q z)
        = deriv (F_p η q) (F_inv q z)
    rw [F_p_deriv η q (F_inv q z) hu_q_S]
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  have h_eq := h_K.unique h_K_zero
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
    show iteratedDeriv 2 (F_p η p) w₀ = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_evt : (deriv (F_p η p)) =ᶠ[nhds w₀]
        (fun w' => (1 - ↑p) * deriv H0 w' + ↑p * deriv (H_eta η) w') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, S_isOpen.mem_nhds hw₀_S, ?_⟩
      intro w' hw'
      exact F_p_deriv η p w' hw'
    rw [h_evt.deriv_eq]
    have hH0' : DifferentiableAt ℂ (deriv H0) w₀ :=
      (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
    have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
      ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
    have hd1 : deriv (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ =
        (1 - ↑p) * deriv (deriv H0) w₀ := deriv_const_mul _ hH0'
    have hd2 : deriv (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ =
        ↑p * deriv (deriv (H_eta η)) w₀ := deriv_const_mul _ hHe'
    have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑p : ℂ) * deriv H0 w') w₀ :=
      hH0'.const_mul _
    have h_diff2 : DifferentiableAt ℂ (fun w' => (↑p : ℂ) * deriv (H_eta η) w') w₀ :=
      hHe'.const_mul _
    rw [show (fun w' => (1 - ↑p : ℂ) * deriv H0 w' + ↑p * deriv (H_eta η) w')
        = (fun w' => (1 - ↑p : ℂ) * deriv H0 w') + (fun w' => ↑p * deriv (H_eta η) w')
        from rfl]
    rw [deriv_add h_diff1 h_diff2, hd1, hd2]
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  -- Substitute u' = -Φ/D into the form-A identity to get
  -- D³ · u'' = 2·Φ·Φ'·D − DD·Φ².
  have hu'_eq : u' = -Φ / D := hu'_value
  -- D³ · u'' + 2·Φ'·u'·D³ + DD·u'·u'·D³ = 0 (multiply form-A by D²).
  -- 2·Φ'·u'·D³ = 2·Φ'·(-Φ/D)·D³ = -2·Φ·Φ'·D²; hmm, we want simpler.
  -- Cleanly: from form-A `D * u'' = -(2 * Φ' * u' + DD * u' * u')` and `u' = -Φ/D`:
  --   2·Φ'·u' = 2·Φ'·(-Φ/D) = -2·Φ·Φ'/D
  --   DD·u'·u' = DD·Φ²/D²
  -- Multiply by D²: 2·Φ'·u'·D² = -2·Φ·Φ'·D, DD·u'·u'·D² = DD·Φ².
  -- Hence (D · u'') · D² = -(−2·Φ·Φ'·D + DD·Φ²) = 2·Φ·Φ'·D − DD·Φ².
  have h_solved_cubed : D ^ 3 * u'' = 2 * Φ * Φ' * D - DD * Φ ^ 2 := by
    -- From form-A: 2·Φ'·u' + DD·u'·u' + D·u'' = 0, with u' = -Φ/D.
    -- Multiply by D² to clear denominators:
    --   D²·(2·Φ'·u') + D²·(DD·u'·u') + D³·u'' = 0
    --   D²·2·Φ'·(-Φ/D) + D²·DD·(-Φ/D)·(-Φ/D) + D³·u'' = 0
    --   -2·Φ·Φ'·D + DD·Φ² + D³·u'' = 0
    --   D³·u'' = 2·Φ·Φ'·D − DD·Φ².
    have hD_ne : D ≠ 0 := hD_ne
    have h_form_with_D2 :
        D ^ 2 * (2 * Φ' * u' + DD * u' * u' + D * u'') = D ^ 2 * 0 := by
      rw [h_form_A_eq]
    have h_lhs_expand :
        D ^ 2 * (2 * Φ' * u' + DD * u' * u' + D * u'') =
        -2 * Φ * Φ' * D + DD * Φ ^ 2 + D ^ 3 * u'' := by
      rw [hu'_eq]
      field_simp
    have h_zero : -2 * Φ * Φ' * D + DD * Φ ^ 2 + D ^ 3 * u'' = 0 := by
      have := h_lhs_expand ▸ h_form_with_D2
      linear_combination this
    linear_combination h_zero
  -- Take norms: ‖D‖³ · ‖u''‖ = ‖2·Φ·Φ'·D − DD·Φ²‖.
  have h_norm_eq : ‖D‖ ^ 3 * ‖u''‖ = ‖2 * Φ * Φ' * D - DD * Φ ^ 2‖ := by
    have h := congrArg norm h_solved_cubed
    rw [norm_mul, norm_pow] at h
    exact h
  -- Apply merged oracle: ‖2·Φ·Φ'·D − DD·Φ²‖ ≤ ‖D‖³ · merged_uderiv,
  -- so ‖D‖³ · ‖u''‖ ≤ ‖D‖³ · merged_uderiv,
  -- and since ‖D‖³ > 0, ‖u''‖ ≤ merged_uderiv.
  have h_uder_bound : ‖u''‖ ≤ merged_uderiv := by
    have h1 : ‖D‖ ^ 3 * ‖u''‖ ≤ ‖D‖ ^ 3 * merged_uderiv := by
      rw [h_norm_eq]
      exact h_merged_oracle
    exact le_of_mul_le_mul_left h1 hD_cube_pos
  -- Convert merged_uderiv to 2 * Cr_phi_uzz_merged merged_uderiv.
  have h_target_eq :
      2 * Cr_phi_uzz_merged merged_uderiv = merged_uderiv := by
    show 2 * Cr_phi_uzz_merged merged_uderiv = _
    unfold Cr_phi_uzz_merged
    ring
  rw [h_target_eq]
  exact h_uder_bound

end Braverman.Paper
