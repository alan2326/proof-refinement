Picking up: the V14 body was too long to emit in one piece, so I'm moving the heavy Step-5 derivation into a **new, purely additive** `Proof/Lib` module (nothing existing is modified) and leaving the candidate thin. The Python oracle, `__init__.py`, and `lemma.toml` above are complete as emitted.

```lean path=ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Direct.lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Pderiv_Direct.lean — Step 5 with a pointwise-correlated bound

Additive module. Nothing in the existing `Lemma54_Paper*` chain is modified;
this file only adds two new theorems alongside the `_phi` / `_phi_invD` /
`_phi_uzz` family.

## The point

Every `F_inv_p_second_deriv_bound_*` variant so far ends by *splitting*

    ‖u''‖ ≤ 2‖Φ'‖‖Φ‖ · (1/‖D‖)²  +  ‖u_zz‖ · ‖Φ‖²

and bounding each factor by its own independent sup-norm oracle. On the
oracle rectangle those factors are strongly anti-correlated, so the product
of sups badly overestimates the sup of the product. Writing
`H_0(w) = arcsin w`, so `H_0'(w) = (1−w²)^{-1/2}` and
`H_0''(w) = w (1−w²)^{-3/2}`, at `p = 0`

    DD / D³ = [ w (1−w²)^{-3/2} ] · (1−w²)^{3/2} = w,

i.e. `‖DD‖/‖D‖³ ≤ sup_Ω |w| ≈ 1.394`, while
`sup‖DD‖ · (sup 1/‖D‖)³ ≈ 6.14 · 4.94 ≈ 30.3`: `‖DD‖` peaks where
`|1−w²|` is smallest (near `w = 1−δ` on the real axis) and `1/‖D‖` peaks
where `|1−w²|` is largest (at the corner `(1−δ) + iB`).

So instead of splitting, we solve the form-A identity *exactly*. From

    2 Φ' u' + DD·u'² + D·u'' = 0        (form A, differentiating
                                         `F_p η q (F_inv q z) = z` twice in q)
    u' = −Φ / D                         (identity 75)

we get, with no inequality applied,

    u'' = 2 Φ' Φ / D²  −  DD Φ² / D³,

and hand that single expression to one oracle hypothesis, so all four
factors are evaluated at the common point `w = F_inv p z`.

`Cr` is abstract here: the conclusion is `‖∂²_p F_inv‖ ≤ 2 · Cr` and the
oracle hypothesis is `‖2Φ'Φ/D² − DD Φ²/D³‖ ≤ 2 · Cr`, so the Lagrange
`1/2!` factor in Step 6 is absorbed exactly as in the other variants.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Cauchy
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Identity
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Taylor
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

set_option maxHeartbeats 1600000 in
/-- **Step 5 (pointwise-correlated).** `‖∂²_p F_inv‖ ≤ 2 · Cr` from a single
oracle bound on the exact algebraic value `2Φ'Φ/D² − DD·Φ²/D³` of
`∂²_p F_inv`. -/
theorem F_inv_p_second_deriv_bound_direct
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {Cr : ℝ}
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
    (h_direct_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖2 * (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))
              * (H_eta η (F_inv p z) - H0 (F_inv p z))
              / deriv (F_p η p) (F_inv p z) ^ 2
          - iteratedDeriv 2 (F_p η p) (F_inv p z)
              * (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2
              / deriv (F_p η p) (F_inv p z) ^ 3‖
          ≤ 2 * Cr) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖ ≤ 2 * Cr := by
  intro p hp z hz
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have h1mr_pos : 0 < 1 - r := by linarith
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
  have hD_lower_paper : (1 - r) / (2 * R) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R
      p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R)) hD_lower_paper
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  -- The implicit equation `Φ(u q) + F_p'(u q) · u'(q) = 0` holds on `(0, pr)`.
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
  -- Differentiate it once more in `q` at `p`.
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
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) w₀ :=
    (H0_analyticOnNhd.deriv w₀ hw₀_S).differentiableAt
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
  have hderiv_He_diff : DifferentiableAt ℂ (deriv (H_eta η)) w₀ :=
    ((H_eta_analyticOnNhd η).deriv w₀ hw₀_S).differentiableAt
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
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀
      + ↑p * iteratedDeriv 2 (H_eta η) w₀ := by
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
  -- Form A.
  have h_form_A_eq : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have hsubst : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀
          + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [hsubst]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀
            + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h_eq
  -- Solve form A exactly for `u''`, keeping every factor at the common point.
  have hu'_D : u' * D = -Φ := by
    rw [hu'_value]; field_simp
  have h3 : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_form_A_eq
  have key : D ^ 3 * u'' = 2 * Φ' * Φ * D - DD * Φ ^ 2 := by
    calc D ^ 3 * u'' = D ^ 2 * (D * u'') := by ring
      _ = D ^ 2 * (-(2 * Φ' * u' + DD * u' * u')) := by rw [h3]
      _ = -(2 * Φ' * (u' * D) * D + DD * (u' * D) * (u' * D)) := by ring
      _ = -(2 * Φ' * (-Φ) * D + DD * (-Φ) * (-Φ)) := by rw [hu'_D]
      _ = 2 * Φ' * Φ * D - DD * Φ ^ 2 := by ring
  have hD3_ne : D ^ 3 ≠ 0 := pow_ne_zero 3 hD_ne
  have hu''_eq : u'' = 2 * Φ' * Φ / D ^ 2 - DD * Φ ^ 2 / D ^ 3 := by
    have hsplit : 2 * Φ' * Φ / D ^ 2 - DD * Φ ^ 2 / D ^ 3
        = (2 * Φ' * Φ * D - DD * Φ ^ 2) / D ^ 3 := by
      field_simp
      ring
    rw [hsplit, eq_div_iff hD3_ne]
    linear_combination key
  rw [hu''_eq]
  exact h_direct_bound p hp z hz

set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — pointwise-correlated
version.** Same shape as `lemma_5_4_paper_on_domain_phi_uzz`, but the four
η-aware oracle hypotheses are replaced by the single correlated bound
`h_direct_oracle_dom`, and `Cr` is a bare parameter rather than a
`Cr_phi*` expression. -/
theorem lemma_5_4_paper_on_domain_direct (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (Cr : ℝ) (hCr_nn : 0 ≤ Cr)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_direct_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖2 * (deriv (H_eta η) w - deriv H0 w) * (H_eta η w - H0 w)
              / deriv (F_p η q) w ^ 2
          - iteratedDeriv 2 (F_p η q) w * (H_eta η w - H0 w) ^ 2
              / deriv (F_p η q) w ^ 3‖
          ≤ 2 * Cr) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr * p ^ 2 := by
  set F_inv := F_inv_paper η r hr0 hr1 with hFinv_def
  set pr := pr_paper η r hr0 hr1 with hpr_def
  have hpr_pos : 0 < pr := pr_paper_pos η r hr0 hr1
  refine ⟨pr, hpr_pos, ?_⟩
  intro p hp_pos hp_lt z hz
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hp_Ico : p ∈ Set.Ico (0 : ℝ) pr := ⟨le_of_lt hp_pos, hp_lt⟩
  have hp_Ioo : p ∈ Set.Ioo (0 : ℝ) pr := ⟨hp_pos, hp_lt⟩
  have hF_inv_eq_p : F_p η p (F_inv p z) = z :=
    F_inv_paper_eq η r hr0 hr1 p hp_Ico z hz_r1
  have hF_S_p : F_inv p z ∈ S :=
    F_inv_paper_mem_S η r hr0 hr1 p hp_Ico z hz_r1
  have hF_an : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      AnalyticOnNhd ℂ (F_inv q) (disk (r1 r)) := fun q hq =>
    F_inv_paper_analytic η r hr0 hr1 q hq
  have hF_inv_eq_full : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk (r1 r),
      F_p η q (F_inv q w) = w := by
    intro q hq w hw
    exact F_inv_paper_eq η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw
  have hF_S_full : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk (r1 r),
      F_inv q w ∈ S := by
    intro q hq w hw
    exact F_inv_paper_mem_S η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw
  have hF_R_full : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk (r1 r),
      ‖F_inv q w‖ ≤ R_val_paper r := by
    intro q hq w hw
    exact F_inv_paper_R_bound η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw
  have hF_p_contdiff_Ioo : ∀ w ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q w) (Set.Ioo (0 : ℝ) pr) := by
    intro w hw
    have h := F_inv_paper_contdiff η r hr0 hr1 w hw
    exact h.mono Set.Ioo_subset_Ico_self
  have hF_p_contdiff_Ico : ∀ w ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv q w) (Set.Ico (0 : ℝ) pr) := fun w hw =>
    F_inv_paper_contdiff η r hr0 hr1 w hw
  have h_direct_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖2 * (deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w))
            * (H_eta η (F_inv q w) - H0 (F_inv q w))
            / deriv (F_p η q) (F_inv q w) ^ 2
        - iteratedDeriv 2 (F_p η q) (F_inv q w)
            * (H_eta η (F_inv q w) - H0 (F_inv q w)) ^ 2
            / deriv (F_p η q) (F_inv q w) ^ 3‖
        ≤ 2 * Cr := by
    intro q hq w hw
    exact h_direct_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_direct η hr0 hr1 hpr_pos
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full hF_p_contdiff_Ioo h_direct_at
  -- Extend the bound from `Ioo` to `Ico`.
  have h_second_deriv_bound : ∀ w ∈ disk r, ∀ t ∈ Set.Ico (0 : ℝ) pr,
      ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico (0 : ℝ) pr) t‖
        ≤ 2 * Cr := by
    intro w hw t ht
    have h5 := h_step5
    have hUnique : UniqueDiffOn ℝ (Set.Ico (0 : ℝ) pr) := uniqueDiffOn_Ico 0 pr
    have h_contInner : ContinuousOn
        (iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico 0 pr))
        (Set.Ico 0 pr) := by
      have h := (hF_p_contdiff_Ico w hw).continuousOn_iteratedDerivWithin
        (m := 2) (by norm_cast) hUnique
      exact h
    rcases lt_or_eq_of_le ht.1 with htpos | hteq
    · have htIoo : t ∈ Set.Ioo (0 : ℝ) pr := ⟨htpos, ht.2⟩
      rw [iteratedDerivWithin_2_Ico_eq_iteratedDeriv_on_Ioo _ pr t htIoo]
      exact h5 t htIoo w hw
    · subst hteq
      have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) pr := ⟨le_refl _, hpr_pos⟩
      have hC := h_contInner.continuousWithinAt h0_mem
      have h_subset : Set.Ioo (0 : ℝ) pr ⊆ Set.Ico (0 : ℝ) pr :=
        Set.Ioo_subset_Ico_self
      have hC_Ioo := hC.mono_left (nhdsWithin_mono _ h_subset)
      have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioo 0 pr),
          ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico 0 pr) x‖
            ≤ 2 * Cr := by
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨Set.Ioo (0 : ℝ) pr, self_mem_nhdsWithin, ?_⟩
        intro x hxIoo
        rw [iteratedDerivWithin_2_Ico_eq_iteratedDeriv_on_Ioo _ pr x hxIoo]
        exact h5 x hxIoo w hw
      have hneBot : (nhdsWithin (0 : ℝ) (Set.Ioo 0 pr)).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        rw [closure_Ioo (ne_of_lt hpr_pos)]
        exact ⟨le_refl _, le_of_lt hpr_pos⟩
      exact le_of_tendsto hC_Ioo.norm hev
  have hu_zero : ∀ w ∈ disk r, F_inv 0 w = Complex.sin w := by
    intro w hw
    have hw_r1 : w ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hw
    exact F_inv_paper_zero η r hr0 hr1 w hw_r1
  have hu_first_deriv : ∀ w ∈ disk r,
      HasDerivWithinAt (fun q : ℝ => F_inv q w)
        ((w - H_eta η (Complex.sin w)) * Complex.cos w)
        (Set.Ici (0 : ℝ)) 0 :=
    F_inv_paper_first_deriv_zero η r hr0 hr1
  have h_step6 := taylor_remainder_p η hr0 hr1 hpr_pos hCr_nn F_inv
    hu_zero hu_first_deriv hF_p_contdiff_Ico h_second_deriv_bound
  have h_taylor_p := h_step6 p hp_Ioo z hz
  refine ⟨F_inv p, hF_inv_eq_p, hF_S_p, ?_⟩
  exact h_taylor_p

end Braverman.Paper
```

```lean path=ProofRefinement/Lemma54/Candidates/V14.lean
/-
  Candidates/V14.lean — replace the *factored* second-`p`-derivative bound
  with a single pointwise-correlated oracle on the exact expression the
  form-A identity produces, dropping `Cr_val` from V13's `3/250 = 0.012`
  to `1/200 = 0.005` (a 2.4× reduction).

  -- @parent Candidates/V13.lean

  ## Why the factored form is lossy

  V9–V13 all route through `Braverman.Paper.Cr_phi_uzz`:

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        = M_phi · M_phi_prime · inv_F_p_z²
            + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  It takes `M_pp ≥ sup‖∂²_z F_p‖` and `inv_F_p_z ≥ sup 1/‖∂_z F_p‖` as
  *independent* parameters and multiplies them. On the oracle rectangle
  those quantities are strongly **anti-correlated**. With
  `H_0(w) = arcsin w`, so `H_0'(w) = (1−w²)^{-1/2}` and
  `H_0''(w) = w (1−w²)^{-3/2}`, at `p = 0`:

      DD / D³ = [ w (1−w²)^{-3/2} ] · (1−w²)^{3/2} = w ,

  so the *true* sup of `‖DD‖/‖D‖³` on Ω is
  `sup_Ω |w| = √((1−δ)² + B²) = √(0.8365² + 1.115²) ≈ 1.394`, whereas
  V13's factored value is `M_pp · inv_F_p_z³ = (61373/10000)·(3407/2000)³
  ≈ 6.1373 · 4.9429 ≈ 30.34` — a **21.8× loss** on the chunk supplying
  81 % of V13's score. Geometrically: `‖DD‖ = |w|/|1−w²|^{3/2}` peaks at
  `w = 1−δ` on the real axis (`|1−w²| ≈ 0.300`, smallest), while
  `1/‖D‖ ≈ |1−w²|^{1/2}` peaks at the corner `(1−δ) + iB`
  (`|1−w²| ≈ 2.421`, largest). The maxima are at different points and no
  instantiation of `Cr_phi_uzz` can see that.

  ## The move

  Solve the form-A identity exactly instead of splitting it. From

      2 Φ' u' + DD·u'² + D·u'' = 0        (form A)
      u' = −Φ / D                         (identity 75)

  we get, with no inequality applied,

      u'' = 2 Φ' Φ / D²  −  DD Φ² / D³ ,

  `Φ = H_η − H_0`, `Φ' = H_η' − H_0'`, `D = ∂_z F_p`, `DD = ∂²_z F_p`, all
  at `w = F_inv p z ∈ oracle_domain`. One oracle then bounds that single
  expression, so every factor is evaluated at a common `w`. The Lean chain
  lives in the new additive module
  `Proof/Lib/Lemma54_Paper_Pderiv_Direct.lean`
  (`F_inv_p_second_deriv_bound_direct` → `lemma_5_4_paper_on_domain_direct`);
  no existing `Proof/Lib` theorem is modified.

  ## Arithmetic (conservative: global sups for Φ, Φ')

  With `‖Φ‖ ≤ 61/2500 = 0.0244`, `‖Φ'‖ ≤ 59/2000 = 0.0295`, and
  `Kdiff ≈ 1.05` for `sup‖H_η'' − H_0''‖` (the `m_pp_tight` Cauchy route):

    corner  w = 0.8365 + 1.115i :  ‖H_0'‖ = 0.6427, ‖H_0''‖ = 0.370
      2·0.0295·0.0244/0.6132² + 1.420·0.0244²/0.6132³
        = 0.003829 + 0.003667 = 0.007496
    real edge  w = 0.8365 :        ‖H_0'‖ = 1.8248, ‖H_0''‖ = 5.083
      0.0014396/1.7953²       + 6.133·0.0244²/1.7953³
        = 0.000447  + 0.000631  = 0.001078

  so `sup‖u''‖ ≲ 0.0075`, dominated by the corner. Declaring

      M_uderiv_val := 1/100 = 0.01     (≈ 25 % margin over the estimate)
      Cr_val       := 1/200 = 0.005    (the Lagrange 1/2! halving)

  gives 2.4× over V13. `M_uderiv_val` is deliberately loose relative to
  the estimate because the oracle's exact return is not yet observed; the
  *pointwise* `Φ`, `Φ'` at the corner may sit well below their global
  maxima (the oracle evaluates them pointwise), in which case a further
  large tightening of both literals is available with no structural change.

  ## Trust base

  Strictly smaller than V13's:
    - 3 Lean primitives;
    - the `Braverman.Paper.F_inv_paper` family (untouched);
    - `Braverman.PaperV0.h_oracle_domain_contains_image` — seed axiom,
      verbatim from V13: same rectangle `Ω(1635/10000, 1115/1000)`, same
      `r = 23/25`, same `η = 1/100`. Nothing the trust surface asserts is
      weakened or shrunk.
    - `Braverman.PaperV0.h_Cr_direct_oracle` — new, oracle-backed by
      `Numerical_Library.compute_Cr_direct_bound`, same rectangle, same
      `p ∈ [0,1]` range, same analytic ingredients (Φ, Φ', ∂_z F_p,
      ∂²_z F_p) as V13's four η-aware oracles.

  V13's `h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`,
  `h_inv_F_p_z_oracle`, `h_M_pp_tight_oracle` are subsumed and no longer
  used; their `[[oracles]]` registrations remain in `lemma.toml`
  (unused registrations are not re-verified).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv_Direct
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Real-width parameter of the Rouché-certified oracle rectangle.
Byte-identical to V9–V13. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter of the Rouché-certified oracle rectangle.
Byte-identical to V9–V13. -/
def B_val : ℝ := 1115 / 1000

/-- Pointwise-correlated sup bound on the exact second-`p`-derivative
expression `2Φ'Φ/D² − DD·Φ²/D³` over `p ∈ [0,1]` and `w ∈ Ω(δ_val, B_val)`.
Runner-witnessed by `Numerical_Library.compute_Cr_direct_bound`. -/
def M_uderiv_val : ℝ := 1 / 100

theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num
theorem M_uderiv_val_pos : 0 < M_uderiv_val := by unfold M_uderiv_val; norm_num
theorem M_uderiv_val_nn : 0 ≤ M_uderiv_val := le_of_lt M_uderiv_val_pos

/-! ## Section 2: Score -/

/-- `Cr_val := 1/200 = 0.005 = M_uderiv_val / 2`. The halving is the
Lagrange `1/2!` factor absorbed by `taylor_remainder_p`, which consumes a
`‖∂²_p F_inv‖ ≤ 2 · Cr` bound. -/
def Cr_val : ℝ := 1 / 200

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

theorem two_Cr_val_eq : 2 * Cr_val = M_uderiv_val := by
  unfold Cr_val M_uderiv_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V13) -/

/-- The Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Axioms -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Seed axiom,
verbatim from V9–V13. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Pointwise-correlated sup-norm bound on the exact algebraic value of
`∂²_p F_p⁻¹`, namely `2Φ'Φ/D² − DD·Φ²/D³` with `Φ = H_η − H_0`,
`Φ' = H_η' − H_0'`, `D = ∂_z F_p`, `DD = ∂²_z F_p`, over the oracle
rectangle and uniformly in `p`.

Runner-witnessed by `Numerical_Library.compute_Cr_direct_bound`, which
certifies the bound for `p ∈ [0, 1]` (via the seed axiom
`pr_paper_le_one`), so the quantifier over `Ioo 0 pr_paper` is subsumed.
Same rectangle, same `η`, and the same analytic ingredients as
`h_M_phi_oracle` / `h_M_phi_prime_oracle` / `h_M_pp_tight_oracle` /
`h_inv_F_p_z_oracle`; the only difference is that the factors are
evaluated at a common `w` instead of being bounded by independent sups. -/
axiom h_Cr_direct_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖2 * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                - deriv Braverman.H0 w)
              * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
              / deriv (Braverman.F_p Braverman.SearchConfig.eta p) w ^ 2
          - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w
              * (Braverman.H_eta Braverman.SearchConfig.eta w
                  - Braverman.H0 w) ^ 2
              / deriv (Braverman.F_p Braverman.SearchConfig.eta p) w ^ 3‖
          ≤ M_uderiv_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same statement shape as V0–V13;
proved by delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_direct`
with `Cr := Cr_val`, threading the seed containment axiom and the single
correlated oracle. The only arithmetic step is `2 * Cr_val = M_uderiv_val`,
which rewrites the oracle's right-hand side into the `2 * Cr` form the
wrapper expects. -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  have h_oracle_2Cr :
      ∀ q ∈ Set.Ioo (0 : ℝ)
          (Braverman.Paper.pr_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
        ∀ w ∈ oracle_domain,
          ‖2 * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                  - deriv Braverman.H0 w)
                * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 2
            - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta q) w
                * (Braverman.H_eta Braverman.SearchConfig.eta w
                    - Braverman.H0 w) ^ 2
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 3‖
            ≤ 2 * Cr_val := by
    intro q hq w hw
    rw [two_Cr_val_eq]
    exact h_Cr_direct_oracle q hq w hw
  exact Braverman.Paper.lemma_5_4_paper_on_domain_direct
    Braverman.SearchConfig.eta Braverman.SearchConfig.r
    Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
    Cr_val Cr_val_nn
    oracle_domain h_oracle_domain_contains_image h_oracle_2Cr

end Braverman.PaperV0
```

Four files this round: the new additive `Proof/Lib` module, the thin candidate, and (emitted just above) `Numerical_Library/cr_direct.py`, `Numerical_Library/__init__.py`, `lemma.toml`.

What to watch in the returned output, in priority order:

1. **`compute_Cr_direct_bound`'s printed `bound` / `ball_value`.** My analytic estimate is `sup‖u''‖ ≈ 0.0075` using *global* `‖Φ‖, ‖Φ'‖` at the corner; the oracle uses them *pointwise*. If the return is far below `0.01`, both literals retighten immediately next round — that is where the remaining distance to `1/6400` has to come from, since the corner term `2‖Φ'‖‖Φ‖/‖D‖²` now dominates (`0.0038` vs `0.0037`) and its size is set entirely by how big `Φ, Φ'` actually are at the corner.
2. **Whether the new module builds at all** (`lake build` picking up a new file under `Proof/Lib/`). If it is not globbed into the library target, I move both theorems inline into the candidate instead.
3. **`hu''_eq`'s two `field_simp` calls** and the `exact h_direct_bound p hp z hz` closing step — the latter relies on `set`-introduced `Φ, Φ', D, DD, w₀, u` unfolding definitionally against the oracle's spelled-out form, which is the same reliance the existing `_phi_uzz` proof already discharges.