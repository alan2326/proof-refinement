/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Pderiv.lean — Step 5: bound on ∂²_p F_inv

Differentiating the implicit equation `phi(u(q)) + F_p'(u(q)) · u'(q) = 0`
once more in `q` gives
`F_p'(u) · u'' = -[2 phi'(u) · u' + F_p''_z(u) · (u')²]`,
where `u(q) := F_inv q z`, `phi := H_η - H_0`, `F_p'(w) := deriv (F_p η q) w`,
and `F_p''_z(w) := iteratedDeriv 2 (F_p η q) w`.

Taking norms and using `‖u'(p)‖ = ‖phi(u(p))‖ / ‖F_p'(u(p))‖ ≤ M_diff · invFp`,
we obtain `‖u''(p)‖ ≤ 2 M_diff M_diffp invFp² + M_pp M_diff² invFp³ = 2 · Cr_refined`.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Identity

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-- For `q ↦ deriv H_0 (u q)` at `q = p`, with `u(p) ∈ S` and
`u` ℝ-differentiable at `p`, we have `HasDerivAt` with derivative
`deriv u p * iteratedDeriv 2 H0 (u p)`. -/
private lemma hasDerivAt_derivH0_comp
    {u : ℝ → ℂ} {p : ℝ} (hu : HasDerivAt u (deriv u p) p)
    (hu_S : u p ∈ S) :
    HasDerivAt (fun q : ℝ => deriv H0 (u q))
      (deriv u p * iteratedDeriv 2 H0 (u p)) p := by
  -- deriv H_0 is analytic on S (deriv of analytic-on-S is analytic-on-S)
  have hderiv_H0_an_at : AnalyticAt ℂ (deriv H0) (u p) :=
    H0_analyticOnNhd.deriv (u p) hu_S
  have hderiv_H0_diff : DifferentiableAt ℂ (deriv H0) (u p) :=
    hderiv_H0_an_at.differentiableAt
  have hderiv_H0_hasDeriv :
      HasDerivAt (deriv H0) (deriv (deriv H0) (u p)) (u p) :=
    hderiv_H0_diff.hasDerivAt
  -- iteratedDeriv 2 H0 = deriv (deriv H0)
  have h_id : iteratedDeriv 2 H0 (u p) = deriv (deriv H0) (u p) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_id]
  have h := hderiv_H0_hasDeriv.scomp p hu
  have hsmul : (deriv u p • deriv (deriv H0) (u p) : ℂ) =
      deriv u p * deriv (deriv H0) (u p) := (smul_eq_mul (α := ℂ) _ _)
  simpa [Function.comp, hsmul] using h

private lemma hasDerivAt_derivHe_comp
    {η : ℝ} {u : ℝ → ℂ} {p : ℝ} (hu : HasDerivAt u (deriv u p) p)
    (hu_S : u p ∈ S) :
    HasDerivAt (fun q : ℝ => deriv (H_eta η) (u q))
      (deriv u p * iteratedDeriv 2 (H_eta η) (u p)) p := by
  have hderiv_an_at : AnalyticAt ℂ (deriv (H_eta η)) (u p) :=
    (H_eta_analyticOnNhd η).deriv (u p) hu_S
  have hderiv_diff : DifferentiableAt ℂ (deriv (H_eta η)) (u p) :=
    hderiv_an_at.differentiableAt
  have hderiv_hasDeriv :
      HasDerivAt (deriv (H_eta η)) (deriv (deriv (H_eta η)) (u p)) (u p) :=
    hderiv_diff.hasDerivAt
  have h_id : iteratedDeriv 2 (H_eta η) (u p) = deriv (deriv (H_eta η)) (u p) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_id]
  have h := hderiv_hasDeriv.scomp p hu
  have hsmul : (deriv u p • deriv (deriv (H_eta η)) (u p) : ℂ) =
      deriv u p * deriv (deriv (H_eta η)) (u p) := (smul_eq_mul (α := ℂ) _ _)
  simpa [Function.comp, hsmul] using h

private lemma hasDerivAt_H0_comp
    {u : ℝ → ℂ} {p : ℝ} (hu : HasDerivAt u (deriv u p) p) (hu_S : u p ∈ S) :
    HasDerivAt (fun q : ℝ => H0 (u q)) (deriv u p * deriv H0 (u p)) p := by
  have hH0_diff : DifferentiableAt ℂ H0 (u p) :=
    H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hu_S)
  have hH0_hasDeriv : HasDerivAt H0 (deriv H0 (u p)) (u p) :=
    hH0_diff.hasDerivAt
  have h := hH0_hasDeriv.scomp p hu
  have hsmul : (deriv u p • deriv H0 (u p) : ℂ) =
      deriv u p * deriv H0 (u p) := (smul_eq_mul (α := ℂ) _ _)
  simpa [Function.comp, hsmul] using h

private lemma hasDerivAt_He_comp
    {η : ℝ} {u : ℝ → ℂ} {p : ℝ} (hu : HasDerivAt u (deriv u p) p)
    (hu_S : u p ∈ S) :
    HasDerivAt (fun q : ℝ => H_eta η (u q))
      (deriv u p * deriv (H_eta η) (u p)) p := by
  have hHe_diff : DifferentiableAt ℂ (H_eta η) (u p) :=
    (H_eta_analyticOnNhd η).differentiableOn.differentiableAt
      (S_isOpen.mem_nhds hu_S)
  have hHe_hasDeriv : HasDerivAt (H_eta η) (deriv (H_eta η) (u p)) (u p) :=
    hHe_diff.hasDerivAt
  have h := hHe_hasDeriv.scomp p hu
  have hsmul : (deriv u p • deriv (H_eta η) (u p) : ℂ) =
      deriv u p * deriv (H_eta η) (u p) := (smul_eq_mul (α := ℂ) _ _)
  simpa [Function.comp, hsmul] using h

/-- `iteratedDeriv 2 (F_p η q) w = (1-q) · iteratedDeriv 2 H_0 w + q · iteratedDeriv 2 (H_eta η) w`
for `w ∈ S`. -/
private lemma iteratedDeriv_2_F_p_eq (η : ℝ) (q : ℝ) (w : ℂ) (hw : w ∈ S) :
    iteratedDeriv 2 (F_p η q) w =
      (1 - ↑q) * iteratedDeriv 2 H0 w + ↑q * iteratedDeriv 2 (H_eta η) w := by
  -- iteratedDeriv 2 = deriv ∘ deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- We want: deriv (deriv (F_p η q)) w = (1-q) deriv (deriv H_0) w + q deriv (deriv (H_eta η)) w
  -- Strategy: deriv (F_p η q) = (1-q) deriv H_0 + q deriv (H_eta η) on S, take deriv again.
  -- Use eventuallyEq on S (open neighborhood of w)
  have h_evt : (deriv (F_p η q)) =ᶠ[nhds w]
      (fun w' => (1 - ↑q) * deriv H0 w' + ↑q * deriv (H_eta η) w') := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨S, S_isOpen.mem_nhds hw, ?_⟩
    intro w' hw'
    exact F_p_deriv η q w' hw'
  rw [h_evt.deriv_eq]
  have hH0' : DifferentiableAt ℂ (deriv H0) w :=
    (H0_analyticOnNhd.deriv w hw).differentiableAt
  have hHe' : DifferentiableAt ℂ (deriv (H_eta η)) w :=
    ((H_eta_analyticOnNhd η).deriv w hw).differentiableAt
  -- Compute: deriv (fun w' => c * f w' + d * g w') w = c * deriv f w + d * deriv g w
  have hd1 : deriv (fun w' => (1 - ↑q : ℂ) * deriv H0 w') w =
      (1 - ↑q) * deriv (deriv H0) w :=
    deriv_const_mul _ hH0'
  have hd2 : deriv (fun w' => (↑q : ℂ) * deriv (H_eta η) w') w =
      ↑q * deriv (deriv (H_eta η)) w :=
    deriv_const_mul _ hHe'
  have h_diff1 : DifferentiableAt ℂ (fun w' => (1 - ↑q : ℂ) * deriv H0 w') w :=
    hH0'.const_mul _
  have h_diff2 : DifferentiableAt ℂ (fun w' => (↑q : ℂ) * deriv (H_eta η) w') w :=
    hHe'.const_mul _
  rw [show (fun w' => (1 - ↑q : ℂ) * deriv H0 w' + ↑q * deriv (H_eta η) w')
      = (fun w' => (1 - ↑q : ℂ) * deriv H0 w') + (fun w' => ↑q * deriv (H_eta η) w')
      from rfl]
  rw [deriv_add h_diff1 h_diff2, hd1, hd2]

/-- **Step 5.** Bound on `‖∂²_p F_inv‖` in terms of the sup-norm
hypotheses. The bound is `2 · Cr_refined r M_diff M_diffp M_pp R` so that
the Lagrange `1/2!` factor in Step 6 absorbs the `2`. -/
theorem F_inv_p_second_deriv_bound
    (η : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {pr : ℝ} (hpr_pos : 0 < pr)
    {M_diff M_diffp M_pp : ℝ}
    (hMdiff_nn : 0 ≤ M_diff) (hMdiffp_nn : 0 ≤ M_diffp) (hMpp_nn : 0 ≤ M_pp)
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
    (h_M_diff_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖H_eta η (F_inv p z) - H0 (F_inv p z)‖ ≤ M_diff)
    (h_M_diffp_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z)‖ ≤ M_diffp)
    (h_M_pp_bound :
      ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
        ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖ ≤ M_pp) :
    ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r,
      ‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖
        ≤ 2 * Cr_refined r M_diff M_diffp M_pp (R_val_paper r) := by
  intro p hp z hz
  -- Setup
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have h1mr_pos : 0 < 1 - r := by linarith
  set invFp := 2 * R_val_paper r / (1 - r) with hinvFp_def
  have hinvFp_pos : 0 < invFp := by simp [hinvFp_def]; positivity
  set u : ℝ → ℂ := fun q => F_inv q z with hu_def
  set w₀ := u p with hw₀_def
  -- Hypotheses derived
  have hz_r1 : z ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hz
  have hw₀_S : w₀ ∈ S := hF_S p hp z hz_r1
  -- u is C² on (0, pr)
  have hU_C2 : ContDiffOn ℝ 2 u (Set.Ioo 0 pr) := hF_p_contdiff z hz
  have hU_C1 : ContDiffOn ℝ 1 u (Set.Ioo 0 pr) :=
    hU_C2.of_le (by norm_num)
  have hOpen : IsOpen (Set.Ioo (0 : ℝ) pr) := isOpen_Ioo
  have hU_diff_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, DifferentiableAt ℝ u q := by
    intro q hq
    exact (hU_C1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hq)
  -- F_p'(F_inv) ≠ 0 on (0,pr) × disk r
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
  -- DifferentiableAt for fun q' => F_inv q' z' for any z' ∈ disk r — for identity_75
  have hF_p_diff_all : ∀ p' ∈ Set.Ioo (0 : ℝ) pr, ∀ z' ∈ disk r,
      DifferentiableAt ℝ (fun q : ℝ => F_inv q z') p' := by
    intro p' hp' z' hz'
    have hC1 : ContDiffOn ℝ 1 (fun q : ℝ => F_inv q z') (Set.Ioo 0 pr) :=
      (hF_p_contdiff z' hz').of_le (by norm_num)
    exact (hC1.differentiableOn (by norm_num)).differentiableAt (hOpen.mem_nhds hp')
  -- Apply identity_75 to extract the formula for deriv u
  have hId75 := identity_75 η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S
                  hF_p_diff_all hF_p_ne_zero
  -- For each q ∈ (0, pr): deriv u q = -(H_eta(u(q)) - H_0(u(q)))/F_p'(u(q))
  have hu_deriv_eq : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      deriv u q = -(H_eta η (F_inv q z) - H0 (F_inv q z)) /
        deriv (F_p η q) (F_inv q z) := by
    intro q hq
    have h := hId75 q hq z hz
    exact h.deriv
  -- Derive the implicit equation: phi(u(q)) + F_p'(u(q)) · deriv u q = 0
  --   where phi(w) := H_eta η w - H_0 w
  -- Equivalent to: K(q) = 0 where K(q) := H_eta η (u q) - H_0 (u q) + F_p'(u(q)) · deriv u q
  have hK_zero_pointwise : ∀ q ∈ Set.Ioo (0 : ℝ) pr,
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q = 0 := by
    intro q hq
    have hne : deriv (F_p η q) (F_inv q z) ≠ 0 := hF_p_ne_zero q hq z hz
    rw [hu_deriv_eq q hq]
    field_simp
    ring
  -- K =ᶠ 0 on a neighborhood of p (in fact on (0,pr))
  have hK_evt_zero : (fun q : ℝ =>
      H_eta η (F_inv q z) - H0 (F_inv q z) +
        deriv (F_p η q) (F_inv q z) * deriv u q) =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) pr, hOpen.mem_nhds hp, ?_⟩
    intro q hq
    exact hK_zero_pointwise q hq
  -- HasDerivAt for u at p, with u'(p) = deriv u p
  have hu_hasDeriv : HasDerivAt u (deriv u p) p :=
    (hU_diff_at p hp).hasDerivAt
  set u' := deriv u p with hu'_def
  -- u' = -phi(w₀)/F_p'(w₀)
  have hu'_value : u' = -(H_eta η w₀ - H0 w₀) / deriv (F_p η p) w₀ := by
    show deriv u p = _
    exact hu_deriv_eq p hp
  -- HasDerivAt for deriv u at p (from ContDiffOn 2)
  -- iteratedDerivWithin 1 u (Ioo 0 pr) =ᶠ deriv u on (Ioo 0 pr), and is differentiable on (Ioo 0 pr)
  have hu_diff_in_set : DifferentiableOn ℝ u (Set.Ioo 0 pr) :=
    hU_C2.differentiableOn (by norm_num)
  have hderiv_u_in_set :
      DifferentiableOn ℝ (deriv u) (Set.Ioo 0 pr) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 u (Set.Ioo 0 pr))
        (Set.Ioo 0 pr) := hU_C2.differentiableOn_iteratedDerivWithin
      (by norm_cast) (uniqueDiffOn_Ioo 0 pr)
    -- iteratedDerivWithin 1 = deriv on open set (use ContDiffAt 1)
    have hUnique : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) pr) := uniqueDiffOn_Ioo 0 pr
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
  -- iteratedDeriv 2 u p = u''
  have hIterDeriv2 : iteratedDeriv 2 u p = u'' := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hIterDeriv2]
  -- Now compute HasDerivAt for K(q) = H_eta η (u q) - H_0 (u q) + F_p'(u(q)) · deriv u q
  -- We need to express K in a form that the Lean derivative library can handle.
  -- Step A: phi(u(q)) := H_eta η (u(q)) - H_0(u(q)) — chain rule
  have h_phi_deriv :
      HasDerivAt (fun q : ℝ => H_eta η (F_inv q z) - H0 (F_inv q z))
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀)) p := by
    have hHe_comp := hasDerivAt_He_comp (η := η) hu_hasDeriv hw₀_S
    have hH0_comp := hasDerivAt_H0_comp hu_hasDeriv hw₀_S
    have h := hHe_comp.sub hH0_comp
    convert h using 1
    ring
  -- Step B: deriv (F_p η q) (u q) = (1-q) deriv H_0 (u q) + q deriv (H_eta η) (u q)
  -- on a neighborhood of p, using F_p_deriv applied to u q ∈ S.
  -- We want HasDerivAt for q ↦ F_p'(u(q)) · deriv u q.
  -- Let's express F_p'(u(q)) := (1-q) deriv H_0 (u(q)) + q deriv (H_eta η) (u(q))
  -- which equals the actual derivative on a neighborhood of p.
  -- Differentiate explicitly.
  have h_ofReal_q : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := p)
    convert h using 1
  have h_one_sub_q : HasDerivAt (fun q : ℝ => (1 : ℂ) - ↑q) (-1) p := by
    have := (hasDerivAt_const p (1 : ℂ)).sub h_ofReal_q
    simpa using this
  -- HasDerivAt for q ↦ deriv H_0 (u q) at p
  have h_H0' : HasDerivAt (fun q : ℝ => deriv H0 (F_inv q z))
      (u' * iteratedDeriv 2 H0 w₀) p :=
    hasDerivAt_derivH0_comp hu_hasDeriv hw₀_S
  -- HasDerivAt for q ↦ deriv (H_eta η) (u q) at p
  have h_He' : HasDerivAt (fun q : ℝ => deriv (H_eta η) (F_inv q z))
      (u' * iteratedDeriv 2 (H_eta η) w₀) p :=
    hasDerivAt_derivHe_comp hu_hasDeriv hw₀_S
  -- HasDerivAt for q ↦ (1 - q) · deriv H_0 (u q) (product rule)
  have h_term1 :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀)) p :=
    h_one_sub_q.mul h_H0'
  -- HasDerivAt for q ↦ q · deriv (H_eta η) (u q) (product rule)
  have h_term2 :
      HasDerivAt (fun q : ℝ => (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀)) p :=
    h_ofReal_q.mul h_He'
  -- Sum: HasDerivAt for q ↦ (1-q) deriv H_0 (u q) + q deriv (H_eta η) (u q)
  have h_Fp'_sum :
      HasDerivAt (fun q : ℝ => ((1 : ℂ) - ↑q) * deriv H0 (F_inv q z) +
                                (↑q : ℂ) * deriv (H_eta η) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_term1.add h_term2
  -- Equality of the function we differentiated and `q ↦ deriv (F_p η q) (u q)` near p
  -- Note: deriv (F_p η q) (u q) = (1-q) deriv H_0 (u q) + q deriv (H_eta η) (u q)
  -- when u q ∈ S. We have u q ∈ S for q ∈ (0, pr).
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
  -- HasDerivAt for q ↦ deriv (F_p η q) (u(q)) at p — same derivative value
  have h_Fp' :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z))
        (-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) p :=
    h_Fp'_sum.congr_of_eventuallyEq h_Fp'_evt.symm
  -- HasDerivAt for q ↦ deriv (F_p η q) (u(q)) · deriv u q at p (product rule)
  have h_prod :
      HasDerivAt (fun q : ℝ => deriv (F_p η q) (F_inv q z) * deriv u q)
        ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
          (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
            + deriv (F_p η p) w₀ * u'') p :=
    h_Fp'.mul hderiv_u_hasDeriv
  -- HasDerivAt for K(q) = phi(u(q)) + F_p'(u(q)) · deriv u q at p
  have h_K :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q)
        (u' * (deriv (H_eta η) w₀ - deriv H0 w₀) +
          ((-1 * deriv H0 w₀ + ((1 : ℂ) - ↑p) * (u' * iteratedDeriv 2 H0 w₀) +
            (1 * deriv (H_eta η) w₀ + ↑p * (u' * iteratedDeriv 2 (H_eta η) w₀))) * u'
              + deriv (F_p η p) w₀ * u'')) p :=
    h_phi_deriv.add h_prod
  -- HasDerivAt for the constant 0 function
  have h_K_zero :
      HasDerivAt (fun q : ℝ =>
          H_eta η (F_inv q z) - H0 (F_inv q z) +
            deriv (F_p η q) (F_inv q z) * deriv u q) 0 p := by
    apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const p (0 : ℂ))
    exact hK_evt_zero
  -- Equate: deriv K p = 0
  have h_eq := h_K.unique h_K_zero
  -- Set notation
  set Φ : ℂ := H_eta η w₀ - H0 w₀ with hΦ_def
  set Φ' : ℂ := deriv (H_eta η) w₀ - deriv H0 w₀ with hΦ'_def
  set D : ℂ := deriv (F_p η p) w₀ with hD_def
  set DD : ℂ := iteratedDeriv 2 (F_p η p) w₀ with hDD_def
  have hDD_eq : DD = (1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀ :=
    iteratedDeriv_2_F_p_eq η p w₀ hw₀_S
  -- Rearrange h_eq: 2 Φ' u' + DD u'² + D u'' = 0
  have h_eq_simp : 2 * Φ' * u' + DD * u' * u' + D * u'' = 0 := by
    have h := h_eq
    -- Substitute DD's value
    have : DD * u' * u' =
        ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' := by
      rw [hDD_eq]
    rw [this]
    show 2 * (deriv (H_eta η) w₀ - deriv H0 w₀) * u' +
          ((1 - ↑p) * iteratedDeriv 2 H0 w₀ + ↑p * iteratedDeriv 2 (H_eta η) w₀) * u' * u' +
          deriv (F_p η p) w₀ * u'' = 0
    linear_combination h
  -- D · u'' = -2 Φ' u' - DD u'²
  have h_solved : D * u'' = -(2 * Φ' * u' + DD * u' * u') := by
    linear_combination h_eq_simp
  -- Take norms: ‖D‖ · ‖u''‖ ≤ 2 ‖Φ'‖ ‖u'‖ + ‖DD‖ ‖u'‖²
  have h_norm_bound : ‖D‖ * ‖u''‖ ≤ 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖^2 := by
    have h1 : ‖D * u''‖ = ‖D‖ * ‖u''‖ := norm_mul _ _
    have h2 : ‖D * u''‖ = ‖2 * Φ' * u' + DD * u' * u'‖ := by
      rw [h_solved, norm_neg]
    have h3 : ‖2 * Φ' * u' + DD * u' * u'‖ ≤ ‖2 * Φ' * u'‖ + ‖DD * u' * u'‖ :=
      norm_add_le _ _
    have h4 : ‖2 * Φ' * u'‖ = 2 * ‖Φ'‖ * ‖u'‖ := by
      rw [show (2 * Φ' * u' : ℂ) = (2 : ℂ) * (Φ' * u') by ring, norm_mul, norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]; ring
    have h5 : ‖DD * u' * u'‖ = ‖DD‖ * ‖u'‖^2 := by
      rw [show (DD * u' * u' : ℂ) = DD * (u' * u') by ring, norm_mul, norm_mul]
      ring
    linarith [h1, h2, h3, h4, h5]
  -- Lower bound on ‖D‖
  have hD_lower : (1 - r) / (2 * R_val_paper r) ≤ ‖D‖ :=
    F_p_deriv_lower_bound_at_F_inv η hr0 hr1 hpr_pos F_inv hF_an hF_inv_eq hF_S hF_R p hp z hz
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 - r) / (2 * R_val_paper r)) hD_lower
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  -- 1 / ‖D‖ ≤ invFp = 2R/(1-r)
  have h_invD_bound : 1 / ‖D‖ ≤ invFp := by
    rw [hinvFp_def]
    rw [div_le_div_iff₀ hD_pos h1mr_pos]
    have hstep : (1 - r) ≤ ‖D‖ * (2 * R_val_paper r) := by
      have hmul := mul_le_mul_of_nonneg_right hD_lower (by positivity : (0 : ℝ) ≤ 2 * R_val_paper r)
      have hsimp : (1 - r) / (2 * R_val_paper r) * (2 * R_val_paper r) = 1 - r := by
        field_simp
      linarith [hsimp ▸ hmul]
    linarith
  -- ‖u'‖ = ‖Φ‖ / ‖D‖ from u' = -Φ/D
  have hu'_norm : ‖u'‖ = ‖Φ‖ / ‖D‖ := by
    have : u' = -Φ / D := hu'_value
    rw [this, norm_div, norm_neg]
  -- ‖u'‖ ≤ M_diff · invFp
  have h_phi_bound : ‖Φ‖ ≤ M_diff := h_M_diff_bound p hp z hz
  have h_phip_bound : ‖Φ'‖ ≤ M_diffp := h_M_diffp_bound p hp z hz
  have h_DD_bound : ‖DD‖ ≤ M_pp := h_M_pp_bound p hp z hz
  have hu'_bound : ‖u'‖ ≤ M_diff * invFp := by
    rw [hu'_norm]
    rw [div_eq_mul_inv, ← one_div]
    apply mul_le_mul h_phi_bound h_invD_bound (by positivity) hMdiff_nn
  -- Combine bounds
  have h_phinn : 0 ≤ ‖Φ'‖ := norm_nonneg _
  have h_DDnn : 0 ≤ ‖DD‖ := norm_nonneg _
  have hu'_nn : 0 ≤ ‖u'‖ := norm_nonneg _
  have h_invFp_nn : 0 ≤ invFp := le_of_lt hinvFp_pos
  -- ‖u''‖ ≤ (2 ‖Φ'‖ ‖u'‖ + ‖DD‖ ‖u'‖²) / ‖D‖
  have hu''_step :
      ‖u''‖ ≤ (2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖^2) / ‖D‖ := by
    rw [le_div_iff₀ hD_pos]
    have : ‖D‖ * ‖u''‖ = ‖u''‖ * ‖D‖ := by ring
    linarith [h_norm_bound]
  -- (2 ‖Φ'‖ ‖u'‖ + ‖DD‖ ‖u'‖²) / ‖D‖ ≤ 2 M_diff M_diffp invFp² + M_pp M_diff² invFp³
  have h_outer :
      (2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖^2) / ‖D‖
        ≤ 2 * M_diff * M_diffp * invFp^2 + M_pp * M_diff^2 * invFp^3 := by
    have h_term1 : 2 * ‖Φ'‖ * ‖u'‖ ≤ 2 * M_diffp * (M_diff * invFp) := by
      have := mul_le_mul h_phip_bound hu'_bound hu'_nn hMdiffp_nn
      have h2 : (2 : ℝ) * (‖Φ'‖ * ‖u'‖) = 2 * ‖Φ'‖ * ‖u'‖ := by ring
      have h3 : (2 : ℝ) * (M_diffp * (M_diff * invFp)) = 2 * M_diffp * (M_diff * invFp) := by ring
      linarith [mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)]
    have h_term2 : ‖DD‖ * ‖u'‖^2 ≤ M_pp * (M_diff * invFp)^2 := by
      have hu'_sq_bound : ‖u'‖^2 ≤ (M_diff * invFp)^2 := by
        apply pow_le_pow_left₀ hu'_nn hu'_bound
      apply mul_le_mul h_DD_bound hu'_sq_bound (by positivity) hMpp_nn
    have h_sum : 2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖^2 ≤
        2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2 := by
      linarith
    have h_div : (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) / ‖D‖ ≤
        (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) * invFp := by
      have h_nn : 0 ≤ 2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2 := by
        positivity
      calc (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) / ‖D‖
          = (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) * (1 / ‖D‖) := by
            rw [div_eq_mul_inv, ← one_div]
        _ ≤ (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) * invFp := by
            exact mul_le_mul_of_nonneg_left h_invD_bound h_nn
    have h_eq2 : (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) * invFp =
        2 * M_diff * M_diffp * invFp^2 + M_pp * M_diff^2 * invFp^3 := by ring
    have h_div_step : (2 * ‖Φ'‖ * ‖u'‖ + ‖DD‖ * ‖u'‖^2) / ‖D‖ ≤
        (2 * M_diffp * (M_diff * invFp) + M_pp * (M_diff * invFp)^2) / ‖D‖ := by
      apply div_le_div_of_nonneg_right h_sum (le_of_lt hD_pos)
    linarith [h_div_step, h_div, h_eq2 ▸ h_div]
  -- Combine: ‖u''‖ ≤ 2 Cr_refined
  have h_final :
      ‖u''‖ ≤ 2 * M_diff * M_diffp * invFp^2 + M_pp * M_diff^2 * invFp^3 :=
    le_trans hu''_step h_outer
  -- Cr_refined = M_diff M_diffp invFp² + M_pp M_diff² invFp³ / 2
  -- 2 Cr_refined = 2 M_diff M_diffp invFp² + M_pp M_diff² invFp³
  have h_2Cr :
      2 * Cr_refined r M_diff M_diffp M_pp (R_val_paper r) =
        2 * M_diff * M_diffp * invFp^2 + M_pp * M_diff^2 * invFp^3 := by
    unfold Cr_refined
    rw [hinvFp_def]
    ring
  rw [h_2Cr]
  exact h_final

end Braverman.Paper