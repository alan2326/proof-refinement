/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem51Generic.lean — generic analytic skeleton of Theorem 5.1

This file extracts the analytic / logical content of `theorem_5_1_paper_effective`
into a generic theorem `theorem_5_1_from_thresholds` that takes as hypotheses
each of the explicit threshold inequalities the proof actually consumes:

* `η`'s strict η-improvement at I,
* the Lemma 5.4 conclusion `h54` for `(η, r)` with constants `Cr, pr₀`,
* the compactness sup bound `B_phi` for `(z - H_η(sin z)) · cos z` on `closedBall 0 r`,
* `p < pr₀`, `p < 1`,
* the gap inequality `p · (|B_phi| + Cr + 1) · r_mid / (r_mid - 9/10) < (sinh(9/10) - 1)/2`,
* `deriv (F_p η p) 0 ≠ 0`,
* the sign-structure threshold `summability_fn F_inv L₀ < 1` already pre-applied at `p`.

The conclusion still uses IVT (`exists_gamma_with_summability`) internally to
produce `γ`, so the existential `∃ γ` remains. Replacing this with an explicit
rational-sandwich `gamma_explicit` is the next refactor (see STATUS_AND_PLAN.md
Phase 4).

Companion file `Theorem51PaperEffective.lean` becomes a thin instantiation that
plumbs `theorem_4_4_effective`, `lemma_5_4_strong_via_paper_on_domain`,
`F_p_deriv_ne_zero_small_p`, and `summability_fn_at_log_lt_one` into this
generic theorem.
-/

import LeanProof.Theorem51

open Complex Set Metric

noncomputable section

namespace Braverman.Effective

/-- **Generic Theorem 5.1.** All "concrete" parts of the proof are exposed as
hypotheses; the proof body only does the analytic IVT bookkeeping. The
parameter list mirrors the load-bearing constants used in
`theorem_5_1_paper_effective`'s original proof. -/
theorem theorem_5_1_from_thresholds
    (η p r r_mid B_phi Cr pr₀ : ℝ)
    (hp_pos : 0 < p)
    (hr_pos : 0 < r) (hr_lt_1 : r < 1) (hr9 : 9 / 10 < r)
    (hr_mid_pos : 0 < r_mid)
    (hr_mid_lt_r : r_mid < r)
    (h9_lt_r_mid : (9 : ℝ) / 10 < r_mid)
    (hCr_pos : 0 < Cr)
    (h54 : ∀ q : ℝ, 0 < q → q < pr₀ →
      ∃ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (Braverman.disk r) ∧
        (∀ z ∈ Braverman.disk r, Braverman.F_p η q (F_inv z) = z) ∧
        (∀ z ∈ Braverman.disk r, F_inv z ∈ Braverman.S) ∧
        F_inv 0 = 0 ∧
        (∀ z ∈ Braverman.disk r,
          ‖F_inv z - Complex.sin z -
            ↑q * ((z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * q ^ 2))
    (hB_phi : ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ‖(z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z‖ ≤ B_phi)
    (hp_lt_pr₀ : p < pr₀)
    (hp_lt_one : p < 1)
    (hp_gap :
      p * (|B_phi| + Cr + 1) * (r_mid / (r_mid - 9 / 10)) < (Real.sinh (9 / 10) - 1) / 2)
    (h_Fp_deriv : deriv (Braverman.F_p η p) 0 ≠ 0)
    (h_sf_lt_one_at_p :
      ∀ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (Braverman.disk r) →
        (∀ z ∈ Braverman.disk r, F_inv (-z) = -F_inv z) →
        (∀ z ∈ Braverman.disk r,
          ‖F_inv z - Complex.sin z -
            ↑p * ((z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * p ^ 2) →
        Braverman.summability_fn F_inv (Real.log (1 + Real.sqrt 2)) < 1) :
    ∃ (γ : ℝ),
      γ > Real.log (1 + Real.sqrt 2) ∧ γ < 1 ∧
      ∃ (F_inv : ℂ → ℂ),
        AnalyticOnNhd ℂ F_inv (Braverman.disk γ) ∧
        (∀ z ∈ Braverman.disk γ, Braverman.F_p η p (F_inv z) = z) ∧
        (∀ z ∈ Braverman.disk γ, F_inv z ∈ Braverman.S) ∧
        Braverman.summability_condition (Braverman.taylor_coeff F_inv) γ := by
  -- Step 1: Extract `F_inv` from `h54` at the chosen `p`.
  obtain ⟨F_inv, hFa, hFi, hFS, hF0, hApprox⟩ := h54 p hp_pos hp_lt_pr₀
  -- Step 2: Comparison parameters.
  set B_total := |B_phi| + Cr + 1 with hB_total_def
  have hB_total_pos : 0 < B_total := by positivity
  set ratio := r_mid / (r_mid - 9 / 10) with hratio_def
  have hr_mid_gap_pos : 0 < r_mid - 9 / 10 := by linarith
  have hratio_pos : 0 < ratio := div_pos hr_mid_pos hr_mid_gap_pos
  set gap := Real.sinh (9 / 10) - 1 with hgap_def
  have hgap_pos : 0 < gap := by
    have := Braverman.sinh_nine_tenths_gt_one; linarith
  -- Step 3: Bound ‖F_inv z - sin z‖ on `closedBall(0, r_mid)`.
  set δ := p * B_total with hδ_def
  have hδ_nn : 0 ≤ δ := by positivity
  have h_bound : ∀ z ∈ Metric.closedBall (0 : ℂ) r_mid,
      ‖F_inv z - Complex.sin z‖ ≤ δ := by
    intro z hz
    have hz_disk : z ∈ Braverman.disk r := by
      rw [Braverman.mem_disk_iff]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      linarith
    have hz_cb : z ∈ Metric.closedBall (0 : ℂ) r := by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      linarith
    have hphi := hB_phi z hz_cb
    have hap := hApprox z hz_disk
    set a := F_inv z - Complex.sin z -
      ↑p * ((z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z) with ha_def
    set b := ↑p * ((z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z) with hb_def
    have hab : F_inv z - Complex.sin z = a + b := by simp only [a, b]; ring
    have hb_norm : ‖b‖ ≤ p * |B_phi| := by
      simp only [b]
      calc ‖↑p * ((z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z)‖
          = ‖(↑p : ℂ)‖ *
              ‖(z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z‖ := norm_mul _ _
        _ = p * ‖(z - Braverman.H_eta η (Complex.sin z)) * Complex.cos z‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp_pos]
        _ ≤ p * |B_phi| := by
            gcongr
            exact le_trans hphi (le_abs_self _)
    calc ‖F_inv z - Complex.sin z‖
        = ‖a + b‖ := by rw [hab]
      _ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
      _ ≤ Cr * p ^ 2 + p * |B_phi| := by linarith [hap]
      _ ≤ Cr * p + p * |B_phi| := by
          have hp2 : p ^ 2 ≤ p := by nlinarith [hp_lt_one]
          nlinarith
      _ = p * (|B_phi| + Cr) := by ring
      _ ≤ p * B_total := by gcongr; linarith
  -- Step 4: Apply `summability_fn_gt_one` to get `> 1` at `9/10`.
  have hsin_an : AnalyticOnNhd ℂ Complex.sin (Braverman.disk r) := fun z _ =>
    Complex.differentiable_sin.analyticAt z
  have hδ_small :
      Braverman.summability_fn Complex.sin (9 / 10) -
        δ * r_mid / (r_mid - 9 / 10) > 1 := by
    have hδ_ratio : δ * ratio < gap := by
      have h1 : δ * ratio < gap / 2 := by
        have : p * (|B_phi| + Cr + 1) * (r_mid / (r_mid - 9 / 10)) <
            (Real.sinh (9 / 10) - 1) / 2 := hp_gap
        simpa [δ, ratio, gap, B_total, hδ_def, hratio_def, hgap_def, hB_total_def] using this
      linarith
    rw [Braverman.summability_fn_sin_eq_sinh (9 / 10) (by norm_num)]
    have h_ratio_eq : δ * r_mid / (r_mid - 9 / 10) = δ * ratio := by
      simp only [ratio]; ring
    rw [h_ratio_eq]
    simp only [gap] at hδ_ratio; linarith
  have h_gt_one := Braverman.summability_fn_gt_one F_inv r r_mid (9 / 10)
    hr_pos hr_mid_pos (by norm_num) h9_lt_r_mid hr_mid_lt_r hFa hsin_an h_bound hδ_nn hδ_small
  -- Step 5: IVT to get `γ`.
  obtain ⟨γ, hγ_pos, hγ_lt, hγ_sum⟩ :=
    Braverman.exists_gamma_with_summability F_inv r hr_pos hFa hF0
      (9 / 10) (by norm_num) hr9 h_gt_one
  -- Step 6: γ > log(1+√2) by sign-structure / monotonicity.
  have hγ_lt_r : γ < r := lt_trans hγ_lt hr9
  have hFp_an : AnalyticAt ℂ (Braverman.F_p η p) 0 :=
    Braverman.F_p_analyticOnNhd η p 0 (by rw [Braverman.mem_S_iff]; simp)
  have hF_odd := Braverman.F_inv_odd η p r hr_pos hr_lt_1 hp_pos F_inv hFa hFi hFS hF0
    hFp_an h_Fp_deriv
  have h_sf_lt_one := h_sf_lt_one_at_p F_inv hFa hF_odd hApprox
  set L₀ := Real.log (1 + Real.sqrt 2) with hL₀_def
  have hL₀_pos : 0 < L₀ := by
    apply Real.log_pos
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  have hL₀_lt_9 : L₀ < 9 / 10 := by
    by_contra h
    push_neg at h
    have h1 : Real.sinh L₀ = 1 := by
      rw [show L₀ = Real.arsinh 1 from by simp [L₀, Real.arsinh]; norm_num]
      exact Real.sinh_arsinh 1
    have h2 := Braverman.sinh_nine_tenths_gt_one
    linarith [Real.sinh_le_sinh.mpr h]
  have hL₀_lt_r : L₀ < r := lt_trans hL₀_lt_9 hr9
  have hγ_gt_log : γ > L₀ := by
    by_contra hle
    push_neg at hle
    have h_sum_γ := Braverman.summable_weights_of_lt_radius F_inv r γ hr_pos hγ_pos.le hγ_lt_r hFa
    have h_sum_L₀ :=
      Braverman.summable_weights_of_lt_radius F_inv r L₀ hr_pos hL₀_pos.le hL₀_lt_r hFa
    have h_le : Braverman.summability_fn F_inv γ ≤ Braverman.summability_fn F_inv L₀ := by
      simp only [Braverman.summability_fn]
      exact h_sum_γ.tsum_mono h_sum_L₀ (fun k =>
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hγ_pos.le hle k) (norm_nonneg _))
    have h_eq_one : Braverman.summability_fn F_inv γ = 1 := by
      simp only [Braverman.summability_fn, Braverman.summability_condition,
        Braverman.embedding_weight] at hγ_sum ⊢
      exact hγ_sum.tsum_eq
    linarith
  -- Step 7: Package.
  refine ⟨γ, hγ_gt_log, ?_, F_inv, ?_, ?_, ?_, hγ_sum⟩
  · linarith
  · exact hFa.mono (Metric.ball_subset_ball (le_of_lt hγ_lt_r))
  · exact fun z hz => hFi z (Metric.ball_subset_ball (le_of_lt hγ_lt_r) hz)
  · exact fun z hz => hFS z (Metric.ball_subset_ball (le_of_lt hγ_lt_r) hz)

end Braverman.Effective
