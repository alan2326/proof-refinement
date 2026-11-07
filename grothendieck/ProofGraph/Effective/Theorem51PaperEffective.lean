/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem51PaperEffective.lean — paper-faithful effective Theorem 5.1

This is `theorem_5_1_paper_effective`, a re-derivation of
`Braverman.theorem_5_1`'s conclusion through the paper-faithful Lemma 5.4
(`lemma_5_4_strong_via_paper_on_domain`) instead of the opaque
`Braverman.lemma_5_4_strong`.

The analytic content lives in `Theorem51Generic.theorem_5_1_from_thresholds`;
this file is now a *thin instantiation* that:

1. obtains `(hη_pos, hη_improvement)` from `theorem_4_4_effective`;
2. obtains `(Cr, pr₀, hCr, hpr₀, h54)` from
   `lemma_5_4_strong_via_paper_on_domain` on the explicit oracle rectangle;
3. obtains the compactness bound `B_phi`;
4. obtains `p_deriv` and `p_β` thresholds from
   `F_p_deriv_ne_zero_small_p` and `summability_fn_at_log_lt_one`;
5. picks `p := p_thresh / 2` from the `min` of all six thresholds;
6. discharges each numerical inequality and feeds them to the generic theorem.

Replacing the `min`-based `p` with an explicit rational (and the IVT-based
`γ` with a rational sandwich) is Phase 4 of `STATUS_AND_PLAN.md`.
-/

import LeanProof.Theorem51
import ProofGraph.Effective.Lemma54Effective
import ProofGraph.Effective.Theorem44Effective
import ProofGraph.Effective.Lemma54PaperBridge
import ProofGraph.Effective.Theorem51Generic

open Complex Set Metric

noncomputable section

namespace Braverman.Effective

/-- **Paper-faithful effective Theorem 5.1.** Identical conclusion to
`Braverman.theorem_5_1`, routed through `theorem_5_1_from_thresholds` and
`lemma_5_4_strong_via_paper_on_domain`. The transitive axiom set is the 12
trusted analytic axioms + 2 oracle-backed Lemma-5.4 axioms (`h_M_oracle`,
`h_oracle_domain_contains_image`) + 1 oracle-backed η-improvement axiom. -/
theorem theorem_5_1_paper_effective :
    ∃ (η : ℝ) (p : ℝ) (γ : ℝ),
      0 < η ∧ 0 < p ∧ γ > Real.log (1 + Real.sqrt 2) ∧ γ < 1 ∧
      ∃ (F_inv : ℂ → ℂ),
        AnalyticOnNhd ℂ F_inv (Braverman.disk γ) ∧
        (∀ z ∈ Braverman.disk γ, Braverman.F_p η p (F_inv z) = z) ∧
        (∀ z ∈ Braverman.disk γ, F_inv z ∈ Braverman.S) ∧
        Braverman.summability_condition (Braverman.taylor_coeff F_inv) γ := by
  -- Step 1: η = eta_val (from theorem_4_4_effective).
  obtain ⟨hη_pos, hη_improvement⟩ := theorem_4_4_effective
  -- Step 2: r = r_val = 23/25 (matches `Lemma54Effective`'s r_val).
  set r : ℝ := r_val with hr_def
  have hr_pos : 0 < r := r_val_pos
  have hr_lt_1 : r < 1 := r_val_lt_one
  have hr9 : 9 / 10 < r := by show 9 / 10 < r_val; unfold r_val; norm_num
  -- Step 3: Lemma 5.4 on the explicit oracle rectangle.
  obtain ⟨Cr, pr₀, hCr, hpr₀, h54⟩ :=
    Braverman.Paper.lemma_5_4_strong_via_paper_on_domain
      eta_val r_val r_val_pos r_val_lt_one
      M_val M_val_pos oracle_domain h_oracle_domain_contains_image h_M_oracle
  -- Step 4: Compactness bound on `phi(z) = (z - H_η(sin z)) · cos z` over `closedBall 0 r`.
  have h_phi_cont : ContinuousOn
      (fun z => (z - Braverman.H_eta eta_val (Complex.sin z)) * Complex.cos z)
      (closedBall (0 : ℂ) r) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.sub
        ((Braverman.H_eta_analyticOnNhd eta_val).continuousOn.comp
          Complex.continuous_sin.continuousOn (fun z hz => by
            rw [Braverman.mem_S_iff]
            exact Braverman.norm_sin_lt_one_of_norm_lt_one z (lt_of_le_of_lt
              (by rwa [mem_closedBall, dist_zero_right] at hz) hr_lt_1)))
    · exact Complex.continuous_cos.continuousOn
  obtain ⟨B_phi, hB_phi⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn h_phi_cont
  -- Step 5: r_mid between 9/10 and r.
  set r_mid : ℝ := 91 / 100 with hr_mid_def
  have hr_mid_pos : 0 < r_mid := by norm_num
  have hr_mid_lt_r : r_mid < r := by
    show r_mid < r_val; unfold r_val; norm_num
  have h9_lt_r_mid : (9 : ℝ) / 10 < r_mid := by norm_num
  -- Step 6: Comparison parameters used to size `p`.
  set B_total := |B_phi| + Cr + 1 with hB_total_def
  have hB_total_pos : 0 < B_total := by positivity
  set ratio := r_mid / (r_mid - 9 / 10) with hratio_def
  have hr_mid_gap_pos : (0 : ℝ) < r_mid - 9 / 10 := by linarith
  have hratio_pos : 0 < ratio := div_pos hr_mid_pos hr_mid_gap_pos
  set gap := Real.sinh (9 / 10) - 1 with hgap_def
  have hgap_pos : 0 < gap := by
    have := Braverman.sinh_nine_tenths_gt_one; linarith
  set gap_η := (Braverman.H_eta eta_val Complex.I / Complex.I).re -
    Real.log (1 + Real.sqrt 2) with hgap_η_def
  have hgap_η_pos : 0 < gap_η := by linarith
  -- Step 7: Threshold from `F_p_deriv_ne_zero_small_p` at z = 0.
  obtain ⟨p_deriv, hp_deriv_pos, hp_deriv_cond⟩ :=
    Braverman.F_p_deriv_ne_zero_small_p eta_val {0} isCompact_singleton
      (Set.singleton_subset_iff.mpr (by rw [Braverman.mem_S_iff]; simp))
  -- Step 8: Threshold from `summability_fn_at_log_lt_one`.
  obtain ⟨p_β, hp_β_pos, h_sf_lt⟩ :=
    Braverman.summability_fn_at_log_lt_one eta_val r hr_pos hr_lt_1 hr9 hη_improvement Cr hCr
  -- Step 9: Pick `p := p_thresh / 2` with `p_thresh = min` of all six thresholds.
  set p_thresh := min pr₀ (min 1 (min (gap / (2 * B_total * ratio))
    (min (1 / (2 * gap_η)) (min p_deriv p_β)))) with hp_thresh_def
  have hp_thresh_pos : 0 < p_thresh := by
    apply lt_min hpr₀
    apply lt_min one_pos
    apply lt_min
    · exact div_pos hgap_pos (by positivity)
    · exact lt_min (div_pos one_pos (by positivity)) (lt_min hp_deriv_pos hp_β_pos)
  have hp_lt_thresh : p_thresh / 2 < p_thresh := by linarith
  set p := p_thresh / 2 with hp_def
  have hp_pos : 0 < p := by simp [hp_def]; linarith
  -- Discharge each threshold inequality.
  have hp_lt_pr₀ : p < pr₀ := lt_of_lt_of_le hp_lt_thresh (min_le_left _ _)
  have hp_lt_one : p < 1 := lt_of_lt_of_le hp_lt_thresh
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp_lt_gap_ratio : p < gap / (2 * B_total * ratio) :=
    lt_of_lt_of_le hp_lt_thresh
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hp_lt_p_deriv : p < p_deriv :=
    lt_of_lt_of_le hp_lt_thresh
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hp_lt_pβ : p < p_β :=
    lt_of_lt_of_le hp_lt_thresh
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
  -- Convert `p < gap / (2 * B_total * ratio)` to the gap-form expected by the generic theorem.
  have hp_gap_form :
      p * (|B_phi| + Cr + 1) * (r_mid / (r_mid - 9 / 10)) <
        (Real.sinh (9 / 10) - 1) / 2 := by
    have hBratio_pos : 0 < 2 * B_total * ratio := by positivity
    have h1 : p * (B_total * ratio) < gap / 2 := by
      have hmul : p < gap / 2 / (B_total * ratio) := by
        have : p < gap / (2 * B_total * ratio) := hp_lt_gap_ratio
        have heq : gap / (2 * B_total * ratio) = gap / 2 / (B_total * ratio) := by
          rw [div_div]; congr 1; ring
        rwa [heq] at this
      have hBratio_pos' : 0 < B_total * ratio := mul_pos hB_total_pos hratio_pos
      have := (lt_div_iff₀ hBratio_pos').mp hmul
      linarith
    have hmul_assoc :
        p * (|B_phi| + Cr + 1) * (r_mid / (r_mid - 9 / 10)) =
          p * (B_total * ratio) := by
      simp only [B_total, ratio]
      ring
    rw [hmul_assoc]
    simpa [gap, hgap_def] using h1
  -- Compactness bound to the form expected by the generic theorem.
  have hB_phi_form :
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        ‖(z - Braverman.H_eta eta_val (Complex.sin z)) * Complex.cos z‖ ≤ B_phi :=
    hB_phi
  -- F_p deriv at 0 nonzero from `hp_deriv_cond`.
  have h_Fp_deriv : deriv (Braverman.F_p eta_val p) 0 ≠ 0 := by
    have hp_abs : |p| < p_deriv := by rwa [abs_of_pos hp_pos]
    exact hp_deriv_cond p hp_abs 0 (Set.mem_singleton _)
  -- Summability sign-structure at L₀ from `h_sf_lt`.
  have h_sf_lt_one_at_p :
      ∀ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (Braverman.disk r) →
        (∀ z ∈ Braverman.disk r, F_inv (-z) = -F_inv z) →
        (∀ z ∈ Braverman.disk r,
          ‖F_inv z - Complex.sin z -
            ↑p * ((z - Braverman.H_eta eta_val (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr * p ^ 2) →
        Braverman.summability_fn F_inv (Real.log (1 + Real.sqrt 2)) < 1 :=
    h_sf_lt p hp_pos hp_lt_pβ
  -- Step 10: Apply the generic theorem.
  obtain ⟨γ, hγ_gt_log, hγ_lt_1, F_inv, hFa, hFi, hFS, hγ_sum⟩ :=
    theorem_5_1_from_thresholds eta_val p r r_mid B_phi Cr pr₀
      hp_pos hr_pos hr_lt_1 hr9
      hr_mid_pos hr_mid_lt_r h9_lt_r_mid
      hCr h54 hB_phi_form hp_lt_pr₀ hp_lt_one
      hp_gap_form h_Fp_deriv h_sf_lt_one_at_p
  -- Step 11: Package the existential.
  exact ⟨eta_val, p, γ, eta_val_pos, hp_pos, hγ_gt_log, hγ_lt_1,
    F_inv, hFa, hFi, hFS, hγ_sum⟩

end Braverman.Effective
