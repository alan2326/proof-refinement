/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma53
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Lemma 5.4 (Alternative): First-order expansion of F_p⁻¹

For every r ∈ (0, 1), there exists C_r > 0 such that for all p ∈ (0, p_r) and z ∈ rD:
  ‖F_p⁻¹(z) - sin(z) - p · ψ(z)‖ ≤ C_r · p²
where ψ(z) = (z - H_η(sin z)) · cos z.

## Strategy

We use two bounds:
1. ‖w - s‖ ≤ 2·B_cos·B₁·p  (from D·(w-s) = p·Δ - R and ‖R‖ small)
2. ‖R‖ ≤ p²  (from the Taylor remainder bound via MVT on a segment)

The error identity:
  w - s - p·(Δ·cos z) = p·Δ·(1/D - cos z) - R/D

Term 1 is O(p²) from the algebraic identity for 1/D - cos z.
Term 2 is O(p²) from the ‖R‖ bound and ‖D‖ lower bound.
-/

open Complex Set Metric Real

noncomputable section

namespace Braverman

set_option maxHeartbeats 4000000 in
/-- **Lemma 5.4** (alternative proof).
    For every r ∈ (0, 1), there exists C_r > 0 such that for all
    sufficiently small p > 0 and all z ∈ rD:
      ‖F_p⁻¹(z) - sin(z) - p · ψ(z)‖ ≤ C_r · p²
    where ψ(z) = (z - H_η(sin z)) · cos z. -/
theorem lemma_5_4 (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (Cr : ℝ) (pr : ℝ), 0 < Cr ∧ 0 < pr ∧
      ∀ p : ℝ, 0 < p → p < pr →
        ∀ z ∈ disk r,
          ∃ F_inv : ℂ → ℂ,
            (∀ w ∈ disk r, F_p η p (F_inv w) = w) ∧
            ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * p ^ 2 := by
  -- ================================================================
  -- Setup: thresholds from Lemma 5.3 and derivative bounds
  -- ================================================================
  obtain ⟨pr₀, hpr₀_pos, h_inv⟩ := lemma_5_3 η r hr0 hr1
  -- Use F_p_deriv_ne_zero_small_p on the compact set sin(closedBall(0,r)) ⊆ S
  have hK_sin_compact : IsCompact (Complex.sin '' closedBall (0 : ℂ) r) :=
    (isCompact_closedBall _ _).image Complex.continuous_sin
  have hK_sin_sub_S : Complex.sin '' closedBall (0 : ℂ) r ⊆ S := by
    intro u ⟨z', hz', hu⟩; rw [← hu, mem_S_iff]
    exact norm_sin_lt_one_of_norm_lt_one z' (lt_of_le_of_lt
      (by rwa [mem_closedBall, dist_zero_right] at hz') hr1)
  obtain ⟨p₃, hp₃_pos, h_deriv_ne⟩ :=
    F_p_deriv_ne_zero_small_p η _ hK_sin_compact hK_sin_sub_S

  -- ================================================================
  -- Uniform bounds on disk r (independent of p and z)
  -- ================================================================

  -- B₁: ‖z' - H_η(sin z')‖ ≤ B₁ for z' ∈ disk r
  have h_phi_bounded₀ : ∃ B₁ : ℝ, 0 < B₁ ∧ ∀ z' ∈ disk r,
      ‖z' - H_eta η (Complex.sin z')‖ ≤ B₁ := by
    set K := Complex.sin '' (closedBall (0 : ℂ) r)
    have hK_compact : IsCompact K := (isCompact_closedBall _ _).image Complex.continuous_sin
    have hK_subset_S : K ⊆ S := by
      intro u ⟨z', hz', hu⟩; rw [← hu, mem_S_iff]
      exact norm_sin_lt_one_of_norm_lt_one z' (lt_of_le_of_lt
        (by rwa [mem_closedBall, dist_zero_right] at hz') hr1)
    obtain ⟨M, hM⟩ := H_eta_bounded_on_compact η K hK_compact hK_subset_S
    refine ⟨r + max M 0 + 1, by linarith [le_max_right M 0], ?_⟩
    intro z' hz'
    have hz'_cb : z' ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z' r).mp hz')
    calc ‖z' - H_eta η (Complex.sin z')‖
        ≤ ‖z'‖ + ‖H_eta η (Complex.sin z')‖ := norm_sub_le _ _
      _ ≤ r + max M 0 := by
          linarith [le_trans (hM _ ⟨z', hz'_cb, rfl⟩) (le_max_left M 0),
                    le_of_lt ((mem_disk_iff z' r).mp hz')]
      _ ≤ r + max M 0 + 1 := by linarith
  obtain ⟨B₁, hB₁_pos, hB₁_bound⟩ := h_phi_bounded₀

  -- B_cos: ‖cos z'‖ ≤ B_cos for z' ∈ disk r
  have h_cos_bounded₀ : ∃ B_cos : ℝ, 0 < B_cos ∧ ∀ z' ∈ disk r,
      ‖Complex.cos z'‖ ≤ B_cos := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      Complex.continuous_cos.continuousOn
    refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro z' hz'
    have hz'_cb : z' ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z' r).mp hz')
    exact le_trans (hM z' hz'_cb) (le_max_left _ _)
  obtain ⟨B_cos, hB_cos_pos, hB_cos_bound⟩ := h_cos_bounded₀

  -- B_diff: ‖H_η'(sin z') - H₀'(sin z')‖ ≤ B_diff for z' ∈ disk r
  have h_deriv_diff_bounded₀ : ∃ B_diff : ℝ, 0 < B_diff ∧ ∀ z' ∈ disk r,
      ‖deriv (H_eta η) (Complex.sin z') - deriv H0 (Complex.sin z')‖ ≤ B_diff := by
    set K := Complex.sin '' (closedBall (0 : ℂ) r)
    have hK_compact : IsCompact K := (isCompact_closedBall _ _).image Complex.continuous_sin
    have hK_subset_S : K ⊆ S := by
      intro u ⟨z', hz', hu⟩; rw [← hu, mem_S_iff]
      exact norm_sin_lt_one_of_norm_lt_one z' (lt_of_le_of_lt
        (by rwa [mem_closedBall, dist_zero_right] at hz') hr1)
    have h_cont : ContinuousOn (fun u => deriv (H_eta η) u - deriv H0 u) S :=
      ((H_eta_analyticOnNhd η).deriv.continuousOn).sub H0_analyticOnNhd.deriv.continuousOn
    obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn (h_cont.mono hK_subset_S)
    refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro z' hz'
    have hz'_cb : z' ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z' r).mp hz')
    exact le_trans (hM _ ⟨z', hz'_cb, rfl⟩) (le_max_left _ _)
  obtain ⟨B_diff, hB_diff_pos, hB_diff_bound⟩ := h_deriv_diff_bounded₀

  -- B_H0': ‖H₀'(sin z')‖ ≤ B_H0' for z' ∈ disk r
  have h_H0_deriv_bounded₀ : ∃ B_H0' : ℝ, 0 < B_H0' ∧ ∀ z' ∈ disk r,
      ‖deriv H0 (Complex.sin z')‖ ≤ B_H0' := by
    set K := Complex.sin '' (closedBall (0 : ℂ) r)
    have hK_compact : IsCompact K := (isCompact_closedBall _ _).image Complex.continuous_sin
    have hK_subset_S : K ⊆ S := by
      intro u ⟨z', hz', hu⟩; rw [← hu, mem_S_iff]
      exact norm_sin_lt_one_of_norm_lt_one z' (lt_of_le_of_lt
        (by rwa [mem_closedBall, dist_zero_right] at hz') hr1)
    obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn
      (H0_analyticOnNhd.deriv.continuousOn.mono hK_subset_S)
    refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro z' hz'
    have hz'_cb : z' ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z' r).mp hz')
    exact le_trans (hM _ ⟨z', hz'_cb, rfl⟩) (le_max_left _ _)
  obtain ⟨B_H0', hB_H0'_pos, hB_H0'_bound⟩ := h_H0_deriv_bounded₀

  -- ================================================================
  -- σ: max |Re(sin z')| for z' ∈ closedBall(0, r), with σ < 1
  -- ================================================================
  have h_max_re : ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 ∧ ∀ z' ∈ closedBall (0 : ℂ) r,
      |Complex.re (Complex.sin z')| ≤ σ := by
    have h_cont : ContinuousOn (fun z => |Complex.re (Complex.sin z)|)
        (closedBall (0 : ℂ) r) :=
      (Complex.continuous_re.comp Complex.continuous_sin).continuousOn.abs
    obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
      ⟨0, mem_closedBall_self hr0.le⟩ h_cont
    refine ⟨|Complex.re (Complex.sin z₀)|, abs_nonneg _, ?_, fun z' hz' => hmax hz'⟩
    exact norm_sin_lt_one_of_norm_lt_one z₀
      (lt_of_le_of_lt (by rw [mem_closedBall, dist_zero_right] at hz₀; exact hz₀) hr1)
  obtain ⟨σ, hσ_nn, hσ_lt1, hσ_bound⟩ := h_max_re

  -- ================================================================
  -- M_sin: bound on ‖sin z'‖ for z' ∈ closedBall(0, r)
  -- ================================================================
  obtain ⟨M_sin, hM_sin_bound⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    Complex.continuous_sin.continuousOn

  -- ================================================================
  -- L₂: second-derivative bound (Lipschitz constant for deriv(F_p))
  -- We bound ‖H₀''(u)‖ + ‖H_η''(u)‖ on K₂ = closedBall(0, max M_sin 1 + 1) ∩ {|Re| ≤ (1+σ)/2}
  -- This K₂ is compact, convex, and ⊂ S.
  -- ================================================================
  set ρ_K := max M_sin 1 + 1 with hρ_K_def
  set δ_K := (1 + σ) / 2 with hδ_K_def
  have hδ_K_lt1 : δ_K < 1 := by rw [hδ_K_def]; linarith
  have hδ_K_pos : 0 < δ_K := by rw [hδ_K_def]; linarith
  set K₂ := closedBall (0 : ℂ) ρ_K ∩ {z : ℂ | |z.re| ≤ δ_K} with hK₂_def
  have hK₂_compact : IsCompact K₂ :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_le (Continuous.abs Complex.continuous_re) continuous_const)
  have hK₂_convex : Convex ℝ K₂ := by
    apply Convex.inter (convex_closedBall _ _)
    intro x hx y hy a b ha hb hab
    simp only [mem_setOf_eq] at hx hy ⊢
    have h1 : |(a • x + b • y).re| = |a * x.re + b * y.re| := by
      simp [Complex.add_re, Complex.smul_re]
    rw [h1]
    calc |a * x.re + b * y.re|
        ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
      _ = a * |x.re| + b * |y.re| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * δ_K + b * δ_K := by
          gcongr
      _ = δ_K := by nlinarith
  have hK₂_sub_S : K₂ ⊆ S := fun u ⟨_, hu_re⟩ => by
    simp only [mem_setOf_eq] at hu_re; exact lt_of_le_of_lt hu_re hδ_K_lt1
  -- sin(closedBall(0,r)) ⊂ K₂
  have hsin_sub_K₂ : ∀ z' ∈ closedBall (0 : ℂ) r, Complex.sin z' ∈ K₂ := by
    intro z' hz'
    constructor
    · rw [mem_closedBall, dist_zero_right]
      exact le_trans (hM_sin_bound z' hz') (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))
    · simp only [mem_setOf_eq]
      exact le_trans (hσ_bound z' hz') (by rw [hδ_K_def]; linarith)
  -- Extract L₂: bound on ‖deriv(deriv H0)(u)‖ + ‖deriv(deriv(H_eta η))(u)‖ on K₂
  have hH0_dd_cont : ContinuousOn (deriv (deriv H0)) S :=
    H0_analyticOnNhd.deriv.deriv.continuousOn
  have hHeta_dd_cont : ContinuousOn (deriv (deriv (H_eta η))) S :=
    (H_eta_analyticOnNhd η).deriv.deriv.continuousOn
  obtain ⟨L_H0, hL_H0⟩ := hK₂_compact.exists_bound_of_continuousOn
    (hH0_dd_cont.mono hK₂_sub_S)
  obtain ⟨L_Heta, hL_Heta⟩ := hK₂_compact.exists_bound_of_continuousOn
    (hHeta_dd_cont.mono hK₂_sub_S)
  set L₂ := max (|L_H0| + |L_Heta|) 1 with hL₂_def
  have hL₂_pos : 0 < L₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- L₂ bounds ‖F_p''(u)‖ on K₂ for all p ∈ [0,1]
  -- Since F_p'' = (1-p)*H₀'' + p*H_η'', ‖F_p''(u)‖ ≤ ‖H₀''(u)‖ + ‖H_η''(u)‖ ≤ |L_H0| + |L_Heta| ≤ L₂

  -- ================================================================
  -- Choose constants and threshold
  -- ================================================================
  -- C_R = 16 * L₂ * B_cos² * B₁² (the R-bound constant)
  set C_R := 16 * L₂ * B_cos ^ 2 * B₁ ^ 2 with hC_R_def
  have hC_R_pos : 0 < C_R := by positivity

  set Cr := 2 * B_cos ^ 2 * (B₁ * B_diff + B_H0') + 2 * B_cos * C_R + 1 with hCr_def
  have hCr_pos : 0 < Cr := by positivity
  set pr := min pr₀ (min p₃ (min (1 / (2 * B_diff * B_cos))
    (min (1 / (16 * L₂ * B_cos ^ 2 * B₁))
      ((1 - σ) / (2 * (4 * B_cos * B₁ + 1)))))) with hpr_def
  have hpr_pos : 0 < pr := by
    apply lt_min hpr₀_pos; apply lt_min hp₃_pos
    apply lt_min; · positivity
    apply lt_min; · positivity
    apply div_pos (by linarith) (by positivity)

  refine ⟨Cr, pr, hCr_pos, hpr_pos, ?_⟩
  intro p hp hppr z hz

  -- Extract threshold bounds
  -- pr = min pr₀ (min p₃ (min a (min b c)))
  have hpr₀' : p < pr₀ := lt_of_lt_of_le hppr (min_le_left _ _)
  have hp₃' : |p| < p₃ := by
    rw [abs_of_pos hp]
    calc p < pr := hppr
      _ ≤ min p₃ _ := min_le_right _ _
      _ ≤ p₃ := min_le_left _ _
  have hp_small : p < 1 / (2 * B_diff * B_cos) := by
    calc p < pr := hppr
      _ ≤ min p₃ _ := min_le_right _ _
      _ ≤ min (1 / (2 * B_diff * B_cos)) _ := min_le_right _ _
      _ ≤ 1 / (2 * B_diff * B_cos) := min_le_left _ _
  have hp_L₂ : p < 1 / (16 * L₂ * B_cos ^ 2 * B₁) := by
    calc p < pr := hppr
      _ ≤ min p₃ _ := min_le_right _ _
      _ ≤ min (1 / (2 * B_diff * B_cos)) _ := min_le_right _ _
      _ ≤ min (1 / (16 * L₂ * B_cos ^ 2 * B₁)) _ := min_le_right _ _
      _ ≤ 1 / (16 * L₂ * B_cos ^ 2 * B₁) := min_le_left _ _
  have hp_sigma : p < (1 - σ) / (2 * (4 * B_cos * B₁ + 1)) := by
    calc p < pr := hppr
      _ ≤ min p₃ _ := min_le_right _ _
      _ ≤ min (1 / (2 * B_diff * B_cos)) _ := min_le_right _ _
      _ ≤ min (1 / (16 * L₂ * B_cos ^ 2 * B₁)) _ := min_le_right _ _
      _ ≤ (1 - σ) / (2 * (4 * B_cos * B₁ + 1)) := min_le_right _ _

  -- Get the inverse on disk r
  obtain ⟨F_inv₀, _hF_an₀, hF_right₀, _hF_mem₀, _⟩ := h_inv p hp hpr₀'

  -- ================================================================
  -- Setup: s = sin(z)
  -- ================================================================
  set s := Complex.sin z with hs_def
  have hz_S : z ∈ S := disk_subset_S r hr1 hz
  have hz_norm : ‖z‖ < 1 := by
    rw [mem_disk_iff] at hz; linarith
  have hs_S : s ∈ S := by
    rw [hs_def, mem_S_iff]; exact norm_sin_lt_one_of_norm_lt_one z hz_norm
  have hre : |z.re| < Real.pi / 2 := by
    calc |z.re| < 1 := hz_S
      _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hH0s : H0 s = z := H0_sin_eq z hre hs_S

  -- F_p(s) = (1-p)*z + p*H_η(s) and z - F_p(s) = p*(z - H_η(s))
  have hFs : F_p η p s = (1 - ↑p) * z + ↑p * H_eta η s := by
    unfold F_p; rw [hs_def, hH0s]
  have h_diff : z - F_p η p s = ↑p * (z - H_eta η s) := by rw [hFs]; ring

  -- Chain rule: cos z * H₀'(s) = 1
  have hchain : Complex.cos z * deriv H0 s = 1 := by
    have h_diff_H0 : DifferentiableAt ℂ H0 s :=
      H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hs_S)
    have h_evt : (Complex.sin ∘ H0) =ᶠ[nhds s] id :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨S, S_isOpen.mem_nhds hs_S, fun u hu => sin_H0_eq u hu⟩
    have h1 : deriv (Complex.sin ∘ H0) s = 1 := by rw [h_evt.deriv_eq, deriv_id']
    have h2 : deriv (Complex.sin ∘ H0) s = Complex.cos (H0 s) * deriv H0 s :=
      ((Complex.hasDerivAt_sin (H0 s)).comp s h_diff_H0.hasDerivAt).deriv
    rw [hH0s] at h2; rw [h2] at h1; exact h1

  have hH0'_ne : deriv H0 s ≠ 0 := right_ne_zero_of_mul_eq_one hchain
  have hcos_ne : Complex.cos z ≠ 0 := left_ne_zero_of_mul_eq_one hchain
  have h_norm_prod : ‖Complex.cos z‖ * ‖deriv H0 s‖ = 1 := by
    rw [← norm_mul, hchain, norm_one]
  have hs_in_K_sin : s ∈ Complex.sin '' closedBall (0 : ℂ) r := by
    exact ⟨z, by rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z r).mp hz),
      hs_def⟩
  have hD_ne : deriv (F_p η p) s ≠ 0 := h_deriv_ne p hp₃' s hs_in_K_sin

  -- Pointwise bounds
  have hΔ_bound : ‖z - H_eta η s‖ ≤ B₁ := hB₁_bound z hz
  have hBdiff_bound : ‖deriv (H_eta η) s - deriv H0 s‖ ≤ B_diff := hB_diff_bound z hz
  have hBcos_bound : ‖Complex.cos z‖ ≤ B_cos := hB_cos_bound z hz
  have hBH0'_bound : ‖deriv H0 s‖ ≤ B_H0' := hB_H0'_bound z hz

  -- ================================================================
  -- Algebraic identities (w-independent part)
  -- ================================================================
  set D := deriv (F_p η p) s with hD_def
  set Δ := z - H_eta η s with hΔ_def
  have hD_val : D = deriv H0 s + ↑p * (deriv (H_eta η) s - deriv H0 s) := by
    rw [hD_def, F_p_deriv η p s hs_S]; ring
  have h_inv_diff : 1 / D - Complex.cos z =
      -(↑p * (deriv (H_eta η) s - deriv H0 s)) / (D * deriv H0 s) := by
    have hcos_eq : Complex.cos z = 1 / deriv H0 s := by
      rw [one_div]; exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact hchain)
    rw [hcos_eq, div_sub_div _ _ hD_ne hH0'_ne]; congr 1; rw [hD_val]; ring

  -- ================================================================
  -- Lower bounds on ‖D‖ and ‖H₀'(s)‖
  -- ================================================================
  have hH0'_lower : 1 / B_cos ≤ ‖deriv H0 s‖ := by
    rw [div_le_iff₀ hB_cos_pos]
    nlinarith [h_norm_prod, hBcos_bound, norm_nonneg (deriv H0 s)]

  have hD_lower : 1 / (2 * B_cos) ≤ ‖D‖ := by
    have h1 : ‖deriv H0 s‖ ≤ ‖D‖ + ‖↑p * (deriv (H_eta η) s - deriv H0 s)‖ := by
      calc ‖deriv H0 s‖ = ‖D - ↑p * (deriv (H_eta η) s - deriv H0 s)‖ := by
              congr 1; rw [hD_val]; ring
        _ ≤ ‖D‖ + ‖↑p * (deriv (H_eta η) s - deriv H0 s)‖ := norm_sub_le _ _
    have h2 : ‖↑p * (deriv (H_eta η) s - deriv H0 s)‖ =
        p * ‖deriv (H_eta η) s - deriv H0 s‖ := by
      rw [norm_mul]; simp [Complex.norm_real, abs_of_pos hp]
    have h3 : p * ‖deriv (H_eta η) s - deriv H0 s‖ < 1 / (2 * B_cos) := by
      calc p * ‖deriv (H_eta η) s - deriv H0 s‖
          ≤ p * B_diff := by gcongr
        _ < 1 / (2 * B_diff * B_cos) * B_diff := by gcongr
        _ = 1 / (2 * B_cos) := by field_simp
    rw [h2] at h1
    have h4 : 1 / (2 * B_cos) + 1 / (2 * B_cos) = 1 / B_cos := by field_simp; ring
    linarith [hH0'_lower]

  -- ================================================================
  -- Bound on ‖1/D - cos z‖ (the key algebraic term)
  -- ================================================================
  have h_inv_diff_bound : ‖1 / D - Complex.cos z‖ ≤
      p * B_diff * (2 * B_cos) * B_cos := by
    rw [h_inv_diff, norm_div, norm_neg, norm_mul]
    have hD_pos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD_ne
    have hH0'_pos : (0 : ℝ) < ‖deriv H0 s‖ := norm_pos_iff.mpr hH0'_ne
    have hp_norm : ‖(↑p : ℂ)‖ = p := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    rw [norm_mul, hp_norm]
    have h_num : p * ‖deriv (H_eta η) s - deriv H0 s‖ ≤ p * B_diff := by gcongr
    have h_den : 1 / (2 * B_cos) * (1 / B_cos) ≤ ‖D‖ * ‖deriv H0 s‖ :=
      mul_le_mul hD_lower hH0'_lower (by positivity) (by positivity)
    have h_simp : p * B_diff / (1 / (2 * B_cos) * (1 / B_cos)) =
        p * B_diff * (2 * B_cos) * B_cos := by field_simp
    calc p * ‖deriv (H_eta η) s - deriv H0 s‖ / (‖D‖ * ‖deriv H0 s‖)
        ≤ p * B_diff / (‖D‖ * ‖deriv H0 s‖) := by gcongr
      _ ≤ p * B_diff / (1 / (2 * B_cos) * (1 / B_cos)) := by gcongr
      _ = p * B_diff * (2 * B_cos) * B_cos := h_simp

  -- ================================================================
  -- Term 1 bound: ‖p·Δ·(1/D - cos z)‖ ≤ 2·B_cos²·B₁·B_diff·p²
  -- ================================================================
  have hTerm1 : ‖↑p * Δ * (1 / D - Complex.cos z)‖ ≤
      2 * B_cos ^ 2 * B₁ * B_diff * p ^ 2 := by
    have hp_norm : ‖(↑p : ℂ)‖ = p := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    calc ‖↑p * Δ * (1 / D - Complex.cos z)‖
        ≤ ‖(↑p : ℂ)‖ * ‖Δ‖ * ‖1 / D - Complex.cos z‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ p * B₁ * (p * B_diff * (2 * B_cos) * B_cos) := by
          rw [hp_norm]; gcongr
      _ = 2 * B_cos ^ 2 * B₁ * B_diff * p ^ 2 := by ring

  -- ================================================================
  -- Banach FPT: find w ∈ closedBall s ε with F_p(w) = z
  -- ================================================================
  have hz_cb : z ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z r).mp hz)
  have hs_K₂ : s ∈ K₂ := hsin_sub_K₂ z hz_cb
  have hp_lt1 : p < 1 := by
    calc p < (1 - σ) / (2 * (4 * B_cos * B₁ + 1)) := hp_sigma
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hσ_nn, hB_cos_pos, hB₁_pos]
      _ < 1 := by norm_num
  have hFp_diff_S : ∀ u ∈ S, DifferentiableAt ℂ (F_p η p) u :=
    fun u hu => (F_p_analyticOnNhd η p).differentiableOn.differentiableAt (S_isOpen.mem_nhds hu)
  have hFp'_diff_K₂ : ∀ u ∈ K₂, DifferentiableAt ℂ (deriv (F_p η p)) u :=
    fun u hu => (F_p_analyticOnNhd η p).deriv.differentiableOn.differentiableAt
      (S_isOpen.mem_nhds (hK₂_sub_S hu))
  have hFp''_bound_K₂ : ∀ u ∈ K₂, ‖deriv (deriv (F_p η p)) u‖ ≤ L₂ := by
    intro u hu
    have hu_S : u ∈ S := hK₂_sub_S hu
    have hevt : deriv (F_p η p) =ᶠ[nhds u] fun v =>
        (1 - ↑p) * deriv H0 v + ↑p * deriv (H_eta η) v :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨S, S_isOpen.mem_nhds hu_S, fun v hv => F_p_deriv η p v hv⟩
    rw [hevt.deriv_eq]
    have hH0'_da : DifferentiableAt ℂ (deriv H0) u :=
      H0_analyticOnNhd.deriv.differentiableOn.differentiableAt (S_isOpen.mem_nhds hu_S)
    have hHeta'_da : DifferentiableAt ℂ (deriv (H_eta η)) u :=
      (H_eta_analyticOnNhd η).deriv.differentiableOn.differentiableAt (S_isOpen.mem_nhds hu_S)
    have h_da_add := hH0'_da.const_mul ((1 : ℂ) - ↑p)
    have h_da_add2 := hHeta'_da.const_mul (↑p : ℂ)
    have hfun_eq : (fun v => (1 - ↑p) * deriv H0 v + ↑p * deriv (H_eta η) v) =
        (fun v => (1 - ↑p) * deriv H0 v) + (fun v => ↑p * deriv (H_eta η) v) := by
      ext v; simp [Pi.add_apply]
    rw [hfun_eq, deriv_add h_da_add h_da_add2,
        deriv_const_mul _ hH0'_da, deriv_const_mul _ hHeta'_da]
    have hp_norm_le1 : ‖(↑p : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]; linarith
    have h1mp_le : ‖(1 : ℂ) - ↑p‖ ≤ 1 := by
      have : (1 : ℂ) - ↑p = ↑((1 : ℝ) - p) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    calc ‖(1 - ↑p) * deriv (deriv H0) u + ↑p * deriv (deriv (H_eta η)) u‖
        ≤ ‖(1 - ↑p) * deriv (deriv H0) u‖ + ‖↑p * deriv (deriv (H_eta η)) u‖ :=
          norm_add_le _ _
      _ = ‖(1 : ℂ) - ↑p‖ * ‖deriv (deriv H0) u‖ + ‖(↑p : ℂ)‖ * ‖deriv (deriv (H_eta η)) u‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * |L_H0| + 1 * |L_Heta| := by
          gcongr
          · exact le_trans (hL_H0 u hu) (le_abs_self _)
          · exact le_trans (hL_Heta u hu) (le_abs_self _)
      _ = |L_H0| + |L_Heta| := by ring
      _ ≤ L₂ := le_max_left _ _
  have hFp'_lip : ∀ u ∈ K₂, ‖deriv (F_p η p) u - D‖ ≤ L₂ * ‖u - s‖ := by
    intro u hu
    exact Convex.norm_image_sub_le_of_norm_deriv_le hFp'_diff_K₂ hFp''_bound_K₂
      hK₂_convex hs_K₂ hu
  set ε := 4 * B_cos * B₁ * p with hε_def
  have hε_pos : 0 < ε := by positivity
  have hε_bound : ε < (1 - σ) / 2 := by
    calc ε = 4 * B_cos * B₁ * p := rfl
      _ < 4 * B_cos * B₁ * ((1 - σ) / (2 * (4 * B_cos * B₁ + 1))) := by gcongr
      _ = (4 * B_cos * B₁) * (1 - σ) / (2 * (4 * B_cos * B₁ + 1)) := by ring
      _ ≤ (1 - σ) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hB_cos_pos, hB₁_pos]
  have hball_sub_K₂ : closedBall s ε ⊆ K₂ := by
    intro u hu
    rw [mem_closedBall] at hu
    have h_us_le : ‖u - s‖ ≤ ε := by rwa [dist_eq_norm] at hu
    constructor
    · rw [mem_closedBall, dist_zero_right]
      have hs_norm : ‖s‖ ≤ M_sin := hM_sin_bound z hz_cb
      calc ‖u‖ ≤ ‖s‖ + ‖u - s‖ := norm_le_insert' u s
        _ ≤ M_sin + ε := by linarith
        _ ≤ max M_sin 1 + 1 := by
            have : ε < 1 := by linarith [hε_bound, hσ_nn]
            linarith [le_max_left M_sin 1]
    · simp only [mem_setOf_eq]
      have hs_re : |s.re| ≤ σ := hσ_bound z hz_cb
      calc |u.re| ≤ |(u - s).re| + |s.re| := by
            have : u.re = (u - s).re + s.re := by simp [Complex.sub_re]
            rw [this]; exact abs_add_le _ _
        _ ≤ ‖u - s‖ + σ := by
            have : |(u - s).re| ≤ ‖u - s‖ := Complex.abs_re_le_norm (u - s)
            linarith
        _ ≤ ε + σ := by linarith
        _ ≤ δ_K := by rw [hδ_K_def]; linarith
  have hg_diff : ∀ u ∈ closedBall s ε, DifferentiableAt ℂ (fun u => F_p η p u - D * u) u := by
    intro u hu
    have hu_S := hK₂_sub_S (hball_sub_K₂ hu)
    exact (hFp_diff_S u hu_S).sub (differentiableAt_id.const_mul D)
  have hg_deriv_bound : ∀ u ∈ closedBall s ε,
      ‖deriv (fun u => F_p η p u - D * u) u‖ ≤ L₂ * ε := by
    intro u hu
    have hu_K₂ := hball_sub_K₂ hu
    have hu_S := hK₂_sub_S hu_K₂
    have hFp_da := hFp_diff_S u hu_S
    have hlin_da : DifferentiableAt ℂ (fun u => D * u) u :=
      differentiableAt_id.const_mul D
    have hderiv_eq : deriv (fun u => F_p η p u - D * u) u =
        deriv (F_p η p) u - D := by
      have h1 : deriv (fun u => F_p η p u - D * u) u =
          deriv (F_p η p) u - deriv (fun u => D * u) u :=
        deriv_sub hFp_da hlin_da
      rw [h1, deriv_const_mul_field]
      simp
    rw [hderiv_eq]
    have h_us : ‖u - s‖ ≤ ε := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hu
    calc ‖deriv (F_p η p) u - D‖ ≤ L₂ * ‖u - s‖ := hFp'_lip u hu_K₂
      _ ≤ L₂ * ε := by gcongr
  have hLε_lt : L₂ * ε < 1 / (4 * B_cos) := by
    calc L₂ * ε = 4 * L₂ * B_cos * B₁ * p := by rw [hε_def]; ring
      _ < 4 * L₂ * B_cos * B₁ * (1 / (16 * L₂ * B_cos ^ 2 * B₁)) := by gcongr
      _ = 1 / (4 * B_cos) := by field_simp; ring
  have hLε_lt_D : L₂ * ε < ‖D‖ := by
    calc L₂ * ε < 1 / (4 * B_cos) := hLε_lt
      _ < 1 / (2 * B_cos) := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ ≤ ‖D‖ := hD_lower
  -- Define Ψ(u) = u + (z - F_p η p u) / D; fixed pts of Ψ ↔ preimages of z
  let Ψ : ℂ → ℂ := fun u => u + (z - F_p η p u) / D
  have hΨ_fixed_iff : ∀ u, Ψ u = u ↔ F_p η p u = z := by
    intro u; simp only [Ψ]
    constructor
    · intro h
      have hdiv : (z - F_p η p u) / D = 0 := by
        have : u + (z - F_p η p u) / D - u = 0 := by
          rw [h]; ring
        simp only [add_sub_cancel_left] at this
        exact this
      rcases div_eq_zero_iff.mp hdiv with h1 | h1
      · exact (sub_eq_zero.mp h1).symm
      · exact absurd h1 hD_ne
    · intro h; simp [h]
  have hΨ_sub_s : ∀ u, Ψ u - s = (↑p * Δ - ((F_p η p u - D * u) - (F_p η p s - D * s))) / D := by
    intro u; simp only [Ψ]
    have hFs_eq : F_p η p s = z - ↑p * Δ := by linear_combination -h_diff
    have hgoal : u + (z - F_p η p u) / D - s =
        (↑p * Δ - (F_p η p u - D * u - (F_p η p s - D * s))) / D := by
      rw [hFs_eq]; field_simp [hD_ne]; ring
    exact hgoal
  have hΨ_maps : MapsTo Ψ (closedBall s ε) (closedBall s ε) := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm, hΨ_sub_s]
    have hs_ball : s ∈ closedBall s ε := mem_closedBall_self hε_pos.le
    have hg_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hg_diff hg_deriv_bound
      (convex_closedBall s ε) hs_ball hu
    simp only at hg_mvt
    have h_us : ‖u - s‖ ≤ ε := by rw [← dist_eq_norm]; exact mem_closedBall.mp hu
    have h_gu_gs : ‖(F_p η p u - D * u) - (F_p η p s - D * s)‖ ≤ L₂ * ε * ε :=
      calc ‖(F_p η p u - D * u) - (F_p η p s - D * s)‖
          ≤ L₂ * ε * ‖u - s‖ := by
            rw [show (F_p η p u - D * u) - (F_p η p s - D * s) =
                (fun v => F_p η p v - D * v) u - (fun v => F_p η p v - D * v) s from rfl]
            linarith [norm_sub_rev ((fun v => F_p η p v - D * v) s) ((fun v => F_p η p v - D * v) u)]
        _ ≤ L₂ * ε * ε := by gcongr
    have h_pΔ : ‖(↑p : ℂ) * Δ‖ ≤ p * B₁ := by
      have hp_norm : ‖(↑p : ℂ)‖ = p :=
        by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      calc ‖(↑p : ℂ) * Δ‖ = ‖(↑p : ℂ)‖ * ‖Δ‖ := norm_mul _ _
        _ = p * ‖Δ‖ := by rw [hp_norm]
        _ ≤ p * B₁ := by gcongr
    have hD_pos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD_ne
    have hnum : ‖↑p * Δ - ((F_p η p u - D * u) - (F_p η p s - D * s))‖ ≤ 2 * p * B₁ := by
      have hLε_ε : L₂ * ε * ε < p * B₁ := by
        have h1 : L₂ * ε * ε < (1 / (4 * B_cos)) * ε :=
          mul_lt_mul_of_pos_right hLε_lt hε_pos
        have h2 : (1 / (4 * B_cos)) * ε = p * B₁ := by
          rw [hε_def]; field_simp [hB_cos_pos.ne']
        linarith
      linarith [norm_sub_le (↑p * Δ) ((F_p η p u - D * u) - (F_p η p s - D * s))]
    have hbound : 2 * p * B₁ / ‖D‖ ≤ ε := by
      rw [div_le_iff₀ hD_pos, hε_def]
      have h1 : 4 * B_cos * B₁ * p * (1 / (2 * B_cos)) = 2 * p * B₁ := by
        field_simp; ring
      linarith [mul_le_mul_of_nonneg_left hD_lower (by positivity : 0 ≤ 4 * B_cos * B₁ * p)]
    rw [norm_div]
    calc ‖↑p * Δ - ((F_p η p u - D * u) - (F_p η p s - D * s))‖ / ‖D‖
        ≤ 2 * p * B₁ / ‖D‖ := by gcongr
      _ ≤ ε := hbound
  have hΨ_contract : ∀ u ∈ closedBall s ε, ∀ v ∈ closedBall s ε,
      ‖Ψ u - Ψ v‖ ≤ (1 / 2) * ‖u - v‖ := by
    intro u hu v hv
    have hΨuv : Ψ u - Ψ v = -((F_p η p u - D * u) - (F_p η p v - D * v)) / D := by
      simp only [Ψ]; field_simp [hD_ne]; ring
    have hg_mvt2 := Convex.norm_image_sub_le_of_norm_deriv_le hg_diff hg_deriv_bound
      (convex_closedBall s ε) hu hv
    simp only at hg_mvt2
    have h_guv : ‖(F_p η p u - D * u) - (F_p η p v - D * v)‖ ≤ L₂ * ε * ‖u - v‖ := by
      have h := hg_mvt2
      rw [norm_sub_rev (F_p η p v - D * v) (F_p η p u - D * u),
          norm_sub_rev v u] at h
      exact h
    have hD_pos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD_ne
    rw [hΨuv, norm_div, norm_neg]
    have hLε_half : L₂ * ε ≤ ‖D‖ / 2 := by
      have h1 : 1 / (4 * B_cos) ≤ ‖D‖ / 2 := by
        have hBcos_pos : (0:ℝ) < B_cos := hB_cos_pos
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith [mul_le_mul_of_nonneg_right hD_lower (by linarith : (0:ℝ) ≤ 4 * B_cos),
                  mul_comm (1 / (2 * B_cos)) (4 * B_cos),
                  div_mul_cancel₀ (1:ℝ) (ne_of_gt (by linarith : (0:ℝ) < 2 * B_cos))]
      linarith [hLε_lt]
    calc ‖(F_p η p u - D * u) - (F_p η p v - D * v)‖ / ‖D‖
        ≤ L₂ * ε * ‖u - v‖ / ‖D‖ := by gcongr
      _ ≤ (‖D‖ / 2) * ‖u - v‖ / ‖D‖ := by gcongr
      _ = 1 / 2 * ‖u - v‖ := by field_simp [hD_pos.ne']
  have hball_complete : IsComplete (closedBall s ε) :=
    Metric.isClosed_closedBall.isComplete
  have hΨ_lip : LipschitzWith (1/2 : NNReal)
      (hΨ_maps.restrict Ψ (closedBall s ε) (closedBall s ε)) :=
    LipschitzWith.of_dist_le_mul fun ⟨u, hu⟩ ⟨v, hv⟩ => by
      simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
      have h := hΨ_contract u hu v hv
      push_cast
      linarith
  have hΨ_contractingWith : ContractingWith (1/2 : NNReal)
      (hΨ_maps.restrict Ψ (closedBall s ε) (closedBall s ε)) :=
    ⟨by norm_num, hΨ_lip⟩
  have hs_in : s ∈ closedBall s ε := mem_closedBall_self hε_pos.le
  have hedge : edist s (Ψ s) ≠ ⊤ := edist_ne_top s (Ψ s)
  obtain ⟨w, hw_in_ball, hw_fixed, _, _⟩ := ContractingWith.exists_fixedPoint' hball_complete
    hΨ_maps hΨ_contractingWith hs_in hedge
  have hFw : F_p η p w = z := (hΨ_fixed_iff w).mp hw_fixed

  -- ================================================================
  -- Construct F_inv: use F_inv₀ on disk r \ {z}, use w at z
  -- ================================================================
  let F_inv : ℂ → ℂ := fun v => if v = z then w else F_inv₀ v
  have hF_right : ∀ v ∈ disk r, F_p η p (F_inv v) = v := by
    intro v hv
    simp only [F_inv]
    split
    · next h => rw [h]; exact hFw
    · exact hF_right₀ v hv
  refine ⟨F_inv, hF_right, ?_⟩
  -- Goal: ‖F_inv z - sin z - p*(...)‖ ≤ Cr * p²
  -- F_inv z = w (by the if-then-else)
  show ‖(if z = z then w else F_inv₀ z) - Complex.sin z -
      ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * p ^ 2
  simp only [ite_true]

  -- ================================================================
  -- Algebraic identities (w-dependent part)
  -- ================================================================
  set R := F_p η p w - F_p η p s - D * (w - s) with hR_def
  have hFp_ws : F_p η p w - F_p η p s = ↑p * Δ := by rw [hFw, h_diff, hΔ_def]
  have h_Dws : D * (w - s) = ↑p * Δ - R := by simp only [hR_def, hFp_ws]; ring
  have h_ws_eq : w - s = (↑p * Δ - R) / D := by
    have hmul : (w - s) * D = ↑p * Δ - R := by linear_combination h_Dws
    exact (div_eq_of_eq_mul hD_ne hmul.symm).symm
  have h_error_eq : w - s - ↑p * (Δ * Complex.cos z) =
      ↑p * Δ * (1 / D - Complex.cos z) - R / D := by
    rw [h_ws_eq]; field_simp; ring

  -- ================================================================
  -- Bound ‖R‖ via MVT (w ∈ closedBall s ε from Banach FPT)
  -- ================================================================
  have hR_bound : ‖R‖ ≤ C_R * p ^ 2 := by
    have hR_eq_g : R = (fun u => F_p η p u - D * u) w -
        (fun u => F_p η p u - D * u) s := by simp only [hR_def]; ring
    have hs_in_ball : s ∈ closedBall s ε := mem_closedBall_self hε_pos.le
    have hg_mvt_w := Convex.norm_image_sub_le_of_norm_deriv_le hg_diff hg_deriv_bound
      (convex_closedBall s ε) hs_in_ball hw_in_ball
    have hw_s_le : ‖w - s‖ ≤ ε := by
      rw [mem_closedBall, dist_eq_norm] at hw_in_ball; exact hw_in_ball
    calc ‖R‖ = ‖(fun u => F_p η p u - D * u) w - (fun u => F_p η p u - D * u) s‖ := by
          rw [hR_eq_g]
      _ ≤ L₂ * ε * ‖w - s‖ := by
          have := hg_mvt_w
          simp only at this
          linarith [norm_sub_rev (F_p η p s - D * s) (F_p η p w - D * w),
                    norm_sub_rev s w]
      _ ≤ L₂ * ε * ε := by gcongr
      _ = L₂ * (4 * B_cos * B₁ * p) ^ 2 := by rw [hε_def]; ring
      _ = 16 * L₂ * B_cos ^ 2 * B₁ ^ 2 * p ^ 2 := by ring
      _ = C_R * p ^ 2 := by rw [hC_R_def]

  have hTerm2 : ‖R / D‖ ≤ 2 * B_cos * C_R * p ^ 2 := by
    rw [norm_div]
    have hD_pos : 0 < ‖D‖ := norm_pos_iff.mpr hD_ne
    rw [div_le_iff₀ hD_pos]
    calc ‖R‖ ≤ C_R * p ^ 2 := hR_bound
      _ = C_R * p ^ 2 * 1 := by ring
      _ ≤ C_R * p ^ 2 * (2 * B_cos * ‖D‖) := by
          gcongr
          calc (1 : ℝ) = 1 / (2 * B_cos) * (2 * B_cos) := by field_simp
            _ ≤ ‖D‖ * (2 * B_cos) := by gcongr
            _ = 2 * B_cos * ‖D‖ := by ring
      _ = 2 * B_cos * C_R * p ^ 2 * ‖D‖ := by ring

  -- ================================================================
  -- Final calc: combine Term 1 and Term 2
  -- ================================================================
  rw [h_error_eq]
  calc ‖↑p * Δ * (1 / D - Complex.cos z) - R / D‖
      ≤ ‖↑p * Δ * (1 / D - Complex.cos z)‖ + ‖R / D‖ := norm_sub_le _ _
    _ ≤ 2 * B_cos ^ 2 * B₁ * B_diff * p ^ 2 + 2 * B_cos * C_R * p ^ 2 := by
        gcongr
    _ = (2 * B_cos ^ 2 * B₁ * B_diff + 2 * B_cos * C_R) * p ^ 2 := by ring
    _ ≤ Cr * p ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [hCr_def]; nlinarith [sq_nonneg B_cos, hB_cos_pos, hB_H0'_pos]

/-- Any two analytic right inverses of F_p on disk(r) mapping into S agree on disk(r).
    Proof: by the identity theorem for analytic functions. Both are analytic on the
    connected open set disk(r). They agree near 0 because F_p is locally injective
    there (nonvanishing derivative), so any right inverse must equal the local inverse
    of F_p near 0. The identity theorem then extends the equality to all of disk(r). -/
theorem right_inverse_unique (η : ℝ) (p : ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (F₁ F₂ : ℂ → ℂ)
    (hF₁a : AnalyticOnNhd ℂ F₁ (disk r))
    (hF₂a : AnalyticOnNhd ℂ F₂ (disk r))
    (hF₁i : ∀ z ∈ disk r, F_p η p (F₁ z) = z)
    (hF₂i : ∀ z ∈ disk r, F_p η p (F₂ z) = z)
    (hF₁S : ∀ z ∈ disk r, F₁ z ∈ S)
    (hF₂S : ∀ z ∈ disk r, F₂ z ∈ S)
    (hF₁_zero : F₁ 0 = 0) (hF₂_zero : F₂ 0 = 0)
    (hFp_an : AnalyticAt ℂ (F_p η p) 0)
    (hFp_deriv : deriv (F_p η p) 0 ≠ 0) :
    Set.EqOn F₁ F₂ (disk r) := by
  -- Step 1: disk(r) is preconnected (it's a convex set)
  have h_preconn : IsPreconnected (disk r) := by
    rw [disk]; exact (convex_ball (0 : ℂ) r).isPreconnected
  have h0_mem : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
  -- Step 2: F_p has a strict derivative at 0 (from analyticity)
  have hFp_strict : HasStrictDerivAt (F_p η p) (deriv (F_p η p) 0) 0 :=
    hFp_an.hasStrictDerivAt
  -- Step 3: Get the local inverse of F_p near F_p(0) = 0
  set g := HasStrictDerivAt.localInverse (F_p η p) (deriv (F_p η p) 0) 0
    hFp_strict hFp_deriv with hg_def
  -- Step 4: F₁ =ᶠ[nhds 0] F₂ via the local inverse
  -- Near 0: g(F_p(x)) = x (left inverse), so for y near F_p(0) = 0:
  -- g(y) is the unique preimage of y under F_p near 0.
  -- F₁(y) is also a preimage: F_p(F₁(y)) = y. If F₁(y) is near 0, then F₁(y) = g(y).
  -- Similarly F₂(y) = g(y). Hence F₁(y) = F₂(y) near 0.
  have hFp_zero : F_p η p 0 = 0 := by
    have h1 : H_eta 0 0 = 0 := by
      have h := H_eta_odd 0 0 zero_mem_S; simp only [neg_zero] at h
      exact CharZero.eq_neg_self_iff.mp h
    have h2 : H_eta η 0 = 0 := by
      have h := H_eta_odd η 0 zero_mem_S; simp only [neg_zero] at h
      exact CharZero.eq_neg_self_iff.mp h
    change (1 - ↑p) * H_eta 0 0 + ↑p * H_eta η 0 = 0
    rw [h1, h2]; ring
  -- The left inverse property: g(F_p(x)) = x near 0
  have h_left_inv := hFp_strict.eventually_left_inverse hFp_deriv
  -- h_left_inv : ∀ᶠ x in nhds 0, g(F_p(x)) = x
  -- The right inverse property: F_p(g(y)) = y near F_p(0) = 0
  have h_right_inv := hFp_strict.eventually_right_inverse hFp_deriv
  -- h_right_inv : ∀ᶠ y in nhds (F_p 0), F_p(g(y)) = y
  rw [hFp_zero] at h_right_inv
  -- h_right_inv : ∀ᶠ y in nhds 0, F_p(g(y)) = y
  -- F₁ is continuous at 0, so F₁(y) is near F₁(0) when y is near 0
  -- F₁(0) is a preimage of 0 under F_p: F_p(F₁(0)) = 0 = F_p(0)
  -- By the left inverse property near F₁(0): g(F_p(x)) = x near 0
  -- So g(F_p(F₁(y))) = g(y) = F₁(y) if F₁(y) is in the left-inverse neighborhood
  -- But we also have F_p(F₁(y)) = y, so g(y) = F₁(y).
  -- Helper: any analytic right inverse of F_p on disk(r) with F(0)=0 equals g near 0
  have h_eq_g : ∀ (F : ℂ → ℂ), AnalyticOnNhd ℂ F (disk r) →
      (∀ z ∈ disk r, F_p η p (F z) = z) → (∀ z ∈ disk r, F z ∈ S) →
      F 0 = 0 → F =ᶠ[nhds 0] g := by
    intro F hFan hFright hFmem hF_zero
    -- F is continuous at 0 (analytic → continuous)
    have hF_cont : ContinuousAt F 0 := (hFan 0 h0_mem).continuousAt
    -- h_left_inv: ∀ᶠ x near 0, g(F_p(x)) = x
    -- We need: g(F_p(F(y))) = F(y) for y near 0, which requires F(y) near 0.
    -- Then since F_p(F(y)) = y, we get g(y) = F(y).
    -- F(y) is near F(0) for y near 0 (by continuity).
    -- F(0) is a preimage of 0: F_p(F(0)) = 0 = F_p(0).
    -- g(F_p(F(0))) = F(0) holds if F(0) is in the h_left_inv neighborhood.
    -- Since h_left_inv holds at 0, and by continuity of F_p and g,
    -- there's a neighborhood U of 0 where g ∘ F_p = id on U.
    -- F(0) ∈ U if F(0) is close enough to 0.
    --
    -- Cleaner: use Filter.EventuallyEq
    rw [Filter.eventuallyEq_iff_exists_mem]
    -- h_left_inv gives a neighborhood V₁ of 0 where g(F_p(x)) = x
    rw [Filter.eventually_iff_exists_mem] at h_left_inv
    obtain ⟨V₁, hV₁_nhds, h_left⟩ := h_left_inv
    -- F is continuous at 0, so F⁻¹(V₁) is a neighborhood of 0 (if F(0) ∈ V₁)
    -- But we don't know F(0) ∈ V₁ yet.
    -- Actually: V₁ ∈ nhds 0, and we need F(y) ∈ V₁ for y near 0.
    -- F is continuous, so F⁻¹(V₁) ∈ nhds 0 if F(0) ∈ V₁.
    -- F(0) ∈ V₁? V₁ is a neighborhood of 0, so 0 ∈ V₁.
    -- We need F(0) = 0. This follows from the same argument as F_inv_zero.
    -- F_p(F(0)) = 0, and g(0) is also a preimage of 0.
    -- By h_left at x = 0 (if 0 ∈ V₁): g(F_p(0)) = 0, so g(0) = 0.
    -- Step A: 0 ∈ V₁
    have h0_V₁ : (0 : ℂ) ∈ V₁ := mem_of_mem_nhds hV₁_nhds
    -- Step B: g(F_p(0)) = 0 (applying h_left at x = 0)
    have hg_Fp_zero : g (F_p η p 0) = 0 := h_left 0 h0_V₁
    rw [hFp_zero] at hg_Fp_zero
    -- hg_Fp_zero : g 0 = 0
    -- Step C: F(0) = 0
    -- F(0) = 0 is given as hypothesis
    -- Step D: F⁻¹(V₁) is a neighborhood of 0 (since F is continuous and F(0) = 0 ∈ V₁)
    have hF_preimage : F ⁻¹' V₁ ∈ nhds (0 : ℂ) :=
      hF_cont.preimage_mem_nhds (by rw [hF_zero]; exact hV₁_nhds)
    -- Step E: disk(r) is a neighborhood of 0
    have hdisk_nhds : disk r ∈ nhds (0 : ℂ) := (disk_isOpen r).mem_nhds h0_mem
    -- Step F: The intersection W = disk(r) ∩ F⁻¹(V₁) is a neighborhood of 0
    have hW : disk r ∩ F ⁻¹' V₁ ∈ nhds (0 : ℂ) := Filter.inter_mem hdisk_nhds hF_preimage
    -- Step G: On W, F(y) = g(y)
    exact ⟨disk r ∩ F ⁻¹' V₁, hW, fun y hy => by
      have hy_disk := hy.1
      have hy_V₁ := hy.2  -- F(y) ∈ V₁
      -- g(F_p(F(y))) = F(y) (from h_left, since F(y) ∈ V₁)
      have h1 : g (F_p η p (F y)) = F y := h_left (F y) hy_V₁
      -- F_p(F(y)) = y (from hFright)
      rw [hFright y hy_disk] at h1
      -- h1 : g y = F y
      exact h1.symm⟩
  have h_eq : F₁ =ᶠ[nhds 0] F₂ :=
    (h_eq_g F₁ hF₁a hF₁i hF₁S hF₁_zero).trans (h_eq_g F₂ hF₂a hF₂i hF₂S hF₂_zero).symm
  -- Step 5: Apply the identity theorem
  exact hF₁a.eqOn_of_preconnected_of_eventuallyEq hF₂a h_preconn h0_mem h_eq

set_option maxHeartbeats 8000000 in
/-- **Lemma 5.4 (strengthened)**: There exists an analytic right inverse F_inv of F_p
    on disk(r) that maps into S, satisfies F_inv(0) = 0, and the approximation bound
    ‖F_inv(z) - sin(z) - p·φ(z)‖ ≤ Cr·p² for all z ∈ disk(r). -/
theorem lemma_5_4_strong (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (Cr pr : ℝ), 0 < Cr ∧ 0 < pr ∧
      ∀ p : ℝ, 0 < p → p < pr →
        ∃ F_inv : ℂ → ℂ,
          AnalyticOnNhd ℂ F_inv (disk r) ∧
          (∀ z ∈ disk r, F_p η p (F_inv z) = z) ∧
          (∀ z ∈ disk r, F_inv z ∈ S) ∧
          F_inv 0 = 0 ∧
          (∀ z ∈ disk r,
            ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * p ^ 2) := by
  -- Get the weak Lemma 5.4 for Cr and pointwise bounds
  obtain ⟨Cr, pr_weak, hCr, hpr_weak, h_weak⟩ := lemma_5_4 η r hr0 hr1
  -- Get Lemma 5.3 with W_inv data
  obtain ⟨pr53, hpr53, h53⟩ := lemma_5_3_with_W_inv η r hr0 hr1
  -- Nested radii: r < r₁ < r₂ < 1
  set r₁ : ℝ := (1 + r) / 2 with hr₁_def
  set r₂ : ℝ := (1 + r₁) / 2 with hr₂_def
  have hr₁₂ : r₁ < r₂ := by simp only [r₁, r₂]; linarith
  have hr₂0 : 0 < r₂ := by simp only [r₁, r₂]; linarith
  have hr₂1 : r₂ < 1 := by simp only [r₁, r₂]; linarith
  have hr_r₂ : r < r₂ := by simp only [r₁, r₂]; linarith
  -- G_p injectivity on ball(0, r₂)
  obtain ⟨p_inj, hp_inj, h_inj⟩ := G_p_injOn_ball η r₂ hr₂0 hr₂1
  -- Bound on ‖φ(z)‖ for z ∈ closedBall 0 r
  have h_phi_cont : ContinuousOn (fun z => (z - H_eta η (Complex.sin z)) * Complex.cos z)
      (closedBall (0 : ℂ) r) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.sub ((H_eta_analyticOnNhd η).continuousOn.comp
        Complex.continuous_sin.continuousOn (fun z hz => by
          rw [mem_S_iff]; exact norm_sin_lt_one_of_norm_lt_one z (lt_of_le_of_lt
            (by rwa [mem_closedBall, dist_zero_right] at hz) hr1)))
    · exact Complex.continuous_cos.continuousOn
  obtain ⟨B_phi, hB_phi⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn h_phi_cont
  -- σ: max |Re(sin z')| for z' ∈ closedBall 0 r, with σ < 1
  obtain ⟨z₀, hz₀, hmax_σ⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
    ⟨0, mem_closedBall_self hr0.le⟩
    ((Complex.continuous_re.comp Complex.continuous_sin).continuousOn.abs)
  set σ := |Complex.re (Complex.sin z₀)| with hσ_def
  have hσ_lt1 : σ < 1 := norm_sin_lt_one_of_norm_lt_one z₀
    (lt_of_le_of_lt (by rw [mem_closedBall, dist_zero_right] at hz₀; exact hz₀) hr1)
  have hσ_nn : 0 ≤ σ := abs_nonneg _
  -- M_sin: bound on ‖sin z'‖ for z' ∈ closedBall 0 r
  obtain ⟨M_sin, hM_sin⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    Complex.continuous_sin.continuousOn
  -- Compact convex K₃ ⊆ S for Lipschitz bound of H0
  set δ₃ : ℝ := (1 + σ) / 2 with hδ₃_def
  have hδ₃_lt1 : δ₃ < 1 := by linarith
  have hσ_lt_δ₃ : σ < δ₃ := by linarith
  set ρ₃ := max M_sin 1 + 1 with hρ₃_def
  have hρ₃_pos : 0 < ρ₃ := by positivity
  set K₃ := closedBall (0 : ℂ) ρ₃ ∩ {u : ℂ | |u.re| ≤ δ₃} with hK₃_def
  have hK₃_compact : IsCompact K₃ :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_le (Continuous.abs Complex.continuous_re) continuous_const)
  have hK₃_convex : Convex ℝ K₃ := by
    apply Convex.inter (convex_closedBall _ _)
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    calc |(a • x + b • y).re| = |a * x.re + b * y.re| := by
          simp [Complex.add_re, Complex.smul_re]
      _ ≤ a * |x.re| + b * |y.re| := by
          exact le_trans (abs_add_le _ _) (by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
      _ ≤ a * δ₃ + b * δ₃ := by gcongr
      _ = δ₃ := by nlinarith
  have hK₃_sub_S : K₃ ⊆ S := fun u ⟨_, hu_re⟩ => by
    simp only [Set.mem_setOf_eq] at hu_re; exact lt_of_le_of_lt hu_re hδ₃_lt1
  -- sin(closedBall 0 r) ⊆ K₃
  have hsin_K₃ : ∀ z' ∈ closedBall (0 : ℂ) r, Complex.sin z' ∈ K₃ := by
    intro z' hz'
    constructor
    · rw [mem_closedBall, dist_zero_right]
      exact le_trans (hM_sin z' hz') (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))
    · exact le_of_lt (lt_of_le_of_lt (hmax_σ hz') hσ_lt_δ₃)
  -- Lipschitz constant L_H0 for H0 on K₃
  obtain ⟨L_H0, hL_H0⟩ := hK₃_compact.exists_bound_of_continuousOn
    (H0_analyticOnNhd.deriv.continuousOn.mono hK₃_sub_S)
  set L_H0' := max (|L_H0| + 1) 1 with hL_H0'_def
  have hL_H0'_pos : 0 < L_H0' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hL_H0'_bound : ∀ u ∈ K₃, ‖deriv H0 u‖ ≤ L_H0' := by
    intro u hu
    exact le_trans (le_trans (hL_H0 u hu) (le_abs_self _)) (le_trans (le_add_of_nonneg_right one_pos.le) (le_max_left _ _))
  -- H0 is L_H0'-Lipschitz on K₃
  have hH0_lip : ∀ a ∈ K₃, ∀ b ∈ K₃, ‖H0 b - H0 a‖ ≤ L_H0' * ‖b - a‖ := by
    intro a ha b hb
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (H0_analyticOnNhd u (hK₃_sub_S hu)).differentiableAt)
      hL_H0'_bound hK₃_convex ha hb
  -- Additional thresholds
  -- p_mem: for small p, F_inv'(z) ∈ K₃ (both norm and real-part conditions)
  set B_close := max (|B_phi| + Cr + 1) 1 with hB_close_def
  have hB_close_pos : 0 < B_close := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- For p < p_mem, p * B_close < min((δ₃ - σ), 1)
  set p_mem := min ((δ₃ - σ) / (2 * B_close)) (1 / (2 * B_close))
  have hp_mem_pos : 0 < p_mem := by
    apply lt_min
    · apply div_pos (by linarith) (by positivity)
    · apply div_pos one_pos (by positivity)
  -- p_ball: for small p, ‖H0(F_inv'(z)) - z‖ < r₂ - r
  set p_ball := (r₂ - r) / (2 * L_H0' * B_close)
  have hp_ball_pos : 0 < p_ball := by
    apply div_pos (by linarith) (by positivity)
  -- Choose pr
  refine ⟨Cr, min pr_weak (min pr53 (min p_inj (min p_mem p_ball))), hCr,
    lt_min hpr_weak (lt_min hpr53 (lt_min hp_inj (lt_min hp_mem_pos hp_ball_pos))), ?_⟩
  intro p hp hplt
  -- Extract thresholds
  have hplt_weak : p < pr_weak :=
    lt_of_lt_of_le hplt (min_le_left _ _)
  have hplt_53 : p < pr53 :=
    lt_of_lt_of_le hplt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hplt_inj : |p| < p_inj := by
    rw [abs_of_pos hp]
    exact lt_of_lt_of_le hplt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hplt_mem : p < p_mem :=
    lt_of_lt_of_le hplt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hplt_ball : p < p_ball :=
    lt_of_lt_of_le hplt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  -- Get W_inv and F_inv₀ from lemma_5_3_with_W_inv
  obtain ⟨W_inv, F_inv₀, hW_an, hF₀_an, hW_mem, hF_eq, hF₀_right, hF₀_mem, hF₀_zero⟩ :=
    h53 p hp hplt_53
  -- Return F_inv₀ as the witness
  refine ⟨F_inv₀, hF₀_an, hF₀_right, hF₀_mem, hF₀_zero, ?_⟩
  intro z hz
  -- Get the bound from weak lemma_5_4 for some F_inv'(z)
  obtain ⟨F_inv', hFi', hbound'⟩ := h_weak p hp hplt_weak z hz
  -- Suffices to show F_inv₀ z = F_inv' z
  suffices h_id : F_inv₀ z = F_inv' z by rw [h_id]; exact hbound'
  -- Key bound: F_inv'(z) is close to sin(z)
  have hz_cb : z ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right]; exact le_of_lt ((mem_disk_iff z r).mp hz)
  have h_phi_at_z : ‖(z - H_eta η (Complex.sin z)) * Complex.cos z‖ ≤ B_phi :=
    hB_phi z hz_cb
  -- p < 1 (from p < p_mem ≤ 1/(2·B_close) and B_close ≥ 1)
  have hp_lt1 : p < 1 := by
    have h1 := lt_of_lt_of_le hplt_mem (min_le_right _ _)  -- p < 1/(2*B_close)
    rw [lt_div_iff₀ (by positivity : 0 < 2 * B_close)] at h1  -- p * (2*B_close) < 1
    nlinarith [le_max_right (|B_phi| + Cr + 1) (1 : ℝ)]
  have h_close : ‖F_inv' z - Complex.sin z‖ ≤ p * B_close := by
    -- Triangle: ‖a + b‖ ≤ ‖a‖ + ‖b‖ with a = remainder, b = p * φ(z)
    set a := F_inv' z - Complex.sin z - ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)
    set b := ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)
    have hab : F_inv' z - Complex.sin z = a + b := by simp only [a, b]; ring
    have hb_norm : ‖b‖ ≤ p * B_phi := by
      simp only [b]
      calc ‖↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
          = ‖(↑p : ℂ)‖ * ‖(z - H_eta η (Complex.sin z)) * Complex.cos z‖ := norm_mul _ _
        _ = p * ‖(z - H_eta η (Complex.sin z)) * Complex.cos z‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        _ ≤ p * B_phi := by gcongr
    have h_split : ‖F_inv' z - Complex.sin z‖ ≤ Cr * p ^ 2 + p * B_phi := by
      calc ‖F_inv' z - Complex.sin z‖ = ‖a + b‖ := by rw [hab]
        _ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
        _ ≤ Cr * p ^ 2 + p * B_phi := by linarith [hbound']
    -- Cr * p² ≤ Cr * p (since p ≤ 1)
    calc ‖F_inv' z - Complex.sin z‖ ≤ Cr * p ^ 2 + p * B_phi := h_split
      _ ≤ Cr * p + p * B_phi := by
          have : p ^ 2 ≤ p := by nlinarith
          nlinarith
      _ = p * (B_phi + Cr) := by ring
      _ ≤ p * B_close := by
          gcongr
          calc B_phi + Cr ≤ |B_phi| + Cr := by linarith [le_abs_self B_phi]
            _ ≤ |B_phi| + Cr + 1 := by linarith
            _ ≤ B_close := le_max_left _ _
  -- Helper for the p * B_close < gap bounds
  have hp_B_lt_gap : p * B_close < (δ₃ - σ) / 2 := by
    calc p * B_close < p_mem * B_close := by nlinarith [hplt_mem]
      _ ≤ ((δ₃ - σ) / (2 * B_close)) * B_close := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hB_close_pos)
      _ = (δ₃ - σ) / 2 := by field_simp
  have hp_B_lt_half : p * B_close < 1 / 2 := by
    calc p * B_close < p_mem * B_close := by nlinarith [hplt_mem]
      _ ≤ (1 / (2 * B_close)) * B_close := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hB_close_pos)
      _ = 1 / 2 := by field_simp
  -- Helper: |Re(F_inv'(z))| ≤ σ + p * B_close
  have h_re_bound : |Complex.re (F_inv' z)| ≤ σ + p * B_close := by
    have h1 : |(F_inv' z - Complex.sin z).re| ≤ ‖F_inv' z - Complex.sin z‖ :=
      Complex.abs_re_le_norm _
    have h2 : (F_inv' z).re = (F_inv' z - Complex.sin z).re + (Complex.sin z).re := by
      simp [Complex.sub_re]
    calc |Complex.re (F_inv' z)| = |(F_inv' z - Complex.sin z).re + (Complex.sin z).re| := by
          rw [← h2]
      _ ≤ |(F_inv' z - Complex.sin z).re| + |(Complex.sin z).re| := abs_add_le _ _
      _ ≤ ‖F_inv' z - Complex.sin z‖ + σ := by
          have hsin_re : |(Complex.sin z).re| ≤ σ := by
            have := hmax_σ hz_cb; simp only [Function.comp] at this; exact this
          linarith
      _ ≤ p * B_close + σ := by linarith [h_close]
      _ = σ + p * B_close := by ring
  -- F_inv'(z) ∈ S
  have h_inv'_S : F_inv' z ∈ S := by
    rw [mem_S_iff]
    calc |Complex.re (F_inv' z)| ≤ σ + p * B_close := h_re_bound
      _ < σ + (δ₃ - σ) / 2 := by linarith
      _ = (σ + δ₃) / 2 := by ring
      _ < 1 := by linarith
  -- F_inv'(z) ∈ K₃
  have h_inv'_K₃ : F_inv' z ∈ K₃ := by
    constructor
    · rw [mem_closedBall, dist_zero_right]
      have h1 : ‖F_inv' z‖ ≤ M_sin + p * B_close := by
        linarith [norm_le_insert' (F_inv' z) (Complex.sin z), hM_sin z hz_cb, h_close]
      have h2 : M_sin + 1 ≤ ρ₃ := by simp only [ρ₃]; linarith [le_max_left M_sin (1 : ℝ)]
      linarith [hp_B_lt_half]
    · simp only [Set.mem_setOf_eq]
      exact le_of_lt (lt_of_le_of_lt h_re_bound (by linarith))
  -- sin(z) ∈ K₃
  have hsin_K₃ : Complex.sin z ∈ K₃ := hsin_K₃ z hz_cb
  -- H0(sin z) = z
  have hz_S : z ∈ S := disk_subset_S r hr1 hz
  have hre_z : |z.re| < Real.pi / 2 := by
    calc |z.re| < 1 := hz_S
      _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsin_z_S : Complex.sin z ∈ S := by
    rw [mem_S_iff]; exact norm_sin_lt_one_of_norm_lt_one z (by rw [mem_disk_iff] at hz; linarith)
  have hH0_sin_z : H0 (Complex.sin z) = z := H0_sin_eq z hre_z hsin_z_S
  -- Lipschitz bound: ‖H0(F_inv'(z)) - z‖ ≤ L_H0' * ‖F_inv'(z) - sin(z)‖
  have hH0_lip_bound : ‖H0 (F_inv' z) - z‖ ≤ L_H0' * (p * B_close) := by
    calc ‖H0 (F_inv' z) - z‖ = ‖H0 (F_inv' z) - H0 (Complex.sin z)‖ := by rw [hH0_sin_z]
      _ ≤ L_H0' * ‖F_inv' z - Complex.sin z‖ := hH0_lip (Complex.sin z) hsin_K₃ (F_inv' z) h_inv'_K₃
      _ ≤ L_H0' * (p * B_close) := by gcongr
  -- H0(F_inv'(z)) ∈ ball(0, r₂)
  have h_u_ball : H0 (F_inv' z) ∈ Metric.ball (0 : ℂ) r₂ := by
    rw [Metric.mem_ball, dist_zero_right]
    have hz_norm_le : ‖z‖ ≤ r := le_of_lt ((mem_disk_iff z r).mp hz)
    have h_L_bound : L_H0' * (p * B_close) < r₂ - r := by
      have h1 : p * B_close < p_ball * B_close := by nlinarith [hplt_ball]
      have h2 : p_ball * B_close = (r₂ - r) / (2 * L_H0') := by
        simp only [p_ball]; field_simp
      have h3 : L_H0' * ((r₂ - r) / (2 * L_H0')) = (r₂ - r) / 2 := by
        field_simp
      calc L_H0' * (p * B_close) < L_H0' * (p_ball * B_close) := by
            exact mul_lt_mul_of_pos_left h1 hL_H0'_pos
        _ = L_H0' * ((r₂ - r) / (2 * L_H0')) := by rw [h2]
        _ = (r₂ - r) / 2 := h3
        _ < r₂ - r := by linarith [hr_r₂]
    have h_norm_tri : ‖H0 (F_inv' z)‖ ≤ ‖z‖ + ‖H0 (F_inv' z) - z‖ := norm_le_insert' _ _
    linarith [hH0_lip_bound]
  -- W_inv(z) ∈ ball(0, r₂)
  have h_W_ball : W_inv z ∈ Metric.ball (0 : ℂ) r₂ := by
    rw [Metric.mem_ball, dist_zero_right]
    have hW := hW_mem z hz
    rw [mem_closedBall, dist_zero_right] at hW
    exact lt_of_le_of_lt hW hr₁₂
  -- G_p(H0(F_inv'(z))) = z (since sin(H0(F_inv'(z))) = F_inv'(z))
  have h_sin_H0 : Complex.sin (H0 (F_inv' z)) = F_inv' z := sin_H0_eq (F_inv' z) h_inv'_S
  have h_Gp_u : (fun w => F_p η p (Complex.sin w)) (H0 (F_inv' z)) = z := by
    simp only; rw [h_sin_H0]; exact hFi' z hz
  -- G_p(W_inv(z)) = z
  have h_Gp_W : (fun w => F_p η p (Complex.sin w)) (W_inv z) = z := by
    simp only; rw [← hF_eq z hz]; exact hF₀_right z hz
  -- By G_p injectivity: H0(F_inv'(z)) = W_inv(z)
  have h_eq_W : H0 (F_inv' z) = W_inv z := by
    exact (h_inj p hplt_inj) h_u_ball h_W_ball (by rw [h_Gp_u, h_Gp_W])
  -- Therefore: F_inv₀(z) = sin(W_inv(z)) = sin(H0(F_inv'(z))) = F_inv'(z)
  calc F_inv₀ z = Complex.sin (W_inv z) := hF_eq z hz
    _ = Complex.sin (H0 (F_inv' z)) := by rw [h_eq_W]
    _ = F_inv' z := h_sin_H0

end Braverman
