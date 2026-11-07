/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Cauchy.lean — Step 3 of the paper-faithful Lemma 5.4

Cauchy's estimate applied to the analytic right-inverse `F_inv` on the
*recentred* disk `closedBall z₀ ((1-r)/2) ⊆ disk r₁`. Yields closed-form
bounds on the first and second `z`-derivatives of `F_inv` at any
`z₀ ∈ disk r`:

* `‖deriv F_inv z₀‖           ≤ 2 R / (1 - r)`
* `‖iteratedDeriv 2 F_inv z₀‖ ≤ 8 R / (1 - r)²`

where `R := R_val_paper r = sinh r₂`. Both core lemmas take `F_inv` as
an explicit hypothesis (with its analyticity and `R`-bound) so that the
top-level proof can share a single `F_inv` across all paper steps.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Cauchy

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-! ## Geometric helpers — recentred disk lies in the outer disk -/

/-- The Cauchy radius `(1 - r) / 2` is strictly positive whenever `r < 1`. -/
private theorem half_one_sub_pos {r : ℝ} (hr1 : r < 1) : 0 < (1 - r) / 2 := by
  linarith

/-- If `‖z₀‖ < r` and `‖w‖ ≤ (1-r)/2`, then `z₀ + w ∈ disk r₁`. -/
private theorem add_mem_disk_r1 {r : ℝ} (_hr1 : r < 1)
    {z₀ w : ℂ} (hz₀ : z₀ ∈ disk r)
    (hw : w ∈ closedBall (0 : ℂ) ((1 - r) / 2)) :
    z₀ + w ∈ disk (r1 r) := by
  have hz₀' : ‖z₀‖ < r := by
    simpa [disk, mem_ball, dist_zero_right] using hz₀
  have hw' : ‖w‖ ≤ (1 - r) / 2 := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have hsum : ‖z₀ + w‖ ≤ ‖z₀‖ + ‖w‖ := norm_add_le _ _
  have hbound : ‖z₀‖ + ‖w‖ < r1 r := by unfold r1; linarith
  have : ‖z₀ + w‖ < r1 r := lt_of_le_of_lt hsum hbound
  simpa [disk, mem_ball, dist_zero_right] using this

/-- The recentred map `g w := F_inv (z₀ + w)` is differentiable on
`closedBall 0 ((1-r)/2)` whenever `F_inv` is analytic on `disk r₁` and
`z₀ ∈ disk r`. -/
private theorem differentiableOn_recentered
    {F_inv : ℂ → ℂ} {r : ℝ} (hr1 : r < 1)
    (hF : AnalyticOnNhd ℂ F_inv (disk (r1 r)))
    {z₀ : ℂ} (hz₀ : z₀ ∈ disk r) :
    DifferentiableOn ℂ (fun w => F_inv (z₀ + w)) (closedBall (0 : ℂ) ((1 - r) / 2)) := by
  have hF_diff : DifferentiableOn ℂ F_inv (disk (r1 r)) := hF.differentiableOn
  have htrans_diff : DifferentiableOn ℂ (fun w : ℂ => z₀ + w)
      (closedBall (0 : ℂ) ((1 - r) / 2)) := fun w _ =>
    ((differentiableAt_const z₀).add differentiableAt_id).differentiableWithinAt
  have himage : Set.MapsTo (fun w : ℂ => z₀ + w)
      (closedBall (0 : ℂ) ((1 - r) / 2)) (disk (r1 r)) :=
    fun _ hw => add_mem_disk_r1 hr1 hz₀ hw
  exact DifferentiableOn.comp hF_diff htrans_diff himage

private theorem norm_recentered_le
    {F_inv : ℂ → ℂ} {r : ℝ} (hr1 : r < 1)
    (hRb : ∀ z ∈ disk (r1 r), ‖F_inv z‖ ≤ R_val_paper r)
    {z₀ : ℂ} (hz₀ : z₀ ∈ disk r) :
    ∀ w ∈ closedBall (0 : ℂ) ((1 - r) / 2), ‖F_inv (z₀ + w)‖ ≤ R_val_paper r :=
  fun w hw => hRb (z₀ + w) (add_mem_disk_r1 hr1 hz₀ hw)

/-- `iteratedDeriv n` of the recentred map at `0` equals
`iteratedDeriv n F_inv` at `z₀`. -/
private theorem iteratedDeriv_recentered_zero (F_inv : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w => F_inv (z₀ + w)) 0 = iteratedDeriv n F_inv z₀ := by
  have h := iteratedDeriv_comp_const_add (𝕜 := ℂ) (F := ℂ) n F_inv z₀
  have := congrArg (fun f => f 0) h
  simpa using this

/-! ## Section 1 — First z-derivative bound -/

/-- **Step 3a (core).** Cauchy bound on `‖deriv F_inv z₀‖`, given an
explicit `F_inv` analytic on `disk r₁` with `‖F_inv‖ ≤ R_val_paper r`. -/
theorem F_inv_first_deriv_bound_core {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1)
    {F_inv : ℂ → ℂ}
    (hF_an : AnalyticOnNhd ℂ F_inv (disk (r1 r)))
    (hF_R  : ∀ z ∈ disk (r1 r), ‖F_inv z‖ ≤ R_val_paper r) :
    ∀ z₀ ∈ disk r, ‖deriv F_inv z₀‖ ≤ 2 * R_val_paper r / (1 - r) := by
  intro z₀ hz₀
  set g : ℂ → ℂ := fun w => F_inv (z₀ + w) with hg_def
  have hRpos : 0 < (1 - r) / 2 := half_one_sub_pos hr1
  have hg_diff :
      DifferentiableOn ℂ g (closedBall (0 : ℂ) ((1 - r) / 2)) :=
    differentiableOn_recentered hr1 hF_an hz₀
  have hg_bound :
      ∀ w ∈ closedBall (0 : ℂ) ((1 - r) / 2), ‖g w‖ ≤ R_val_paper r :=
    fun w hw => norm_recentered_le hr1 hF_R hz₀ w hw
  have hk1 :
      ‖Braverman.taylor_coeff g 1‖ ≤ R_val_paper r / ((1 - r) / 2) ^ 1 :=
    Braverman.cauchy_taylor_coeff_bound_closedBall hRpos hg_diff hg_bound
  have htc1 : Braverman.taylor_coeff g 1 = deriv F_inv z₀ := by
    unfold Braverman.taylor_coeff
    have hid : iteratedDeriv 1 g 0 = iteratedDeriv 1 F_inv z₀ :=
      iteratedDeriv_recentered_zero F_inv z₀ 1
    have hone : iteratedDeriv 1 F_inv = deriv F_inv := iteratedDeriv_one
    have hfact : (Nat.factorial 1 : ℂ) = 1 := by simp
    rw [hid, hfact, div_one]
    set_option linter.unnecessarySimpa false in
    have := congrArg (fun f => f z₀) hone
    simpa using this
  have hk1' : ‖deriv F_inv z₀‖ ≤ R_val_paper r / ((1 - r) / 2) := by
    have := hk1
    rw [htc1] at this
    simpa [pow_one] using this
  have hsimplify : R_val_paper r / ((1 - r) / 2) = 2 * R_val_paper r / (1 - r) := by
    have h1mr_pos : 0 < 1 - r := by linarith
    field_simp
  linarith [hk1', hsimplify ▸ hk1']

/-! ## Section 2 — Second z-derivative bound -/

/-- **Step 3b (core).** Cauchy bound on `‖iteratedDeriv 2 F_inv z₀‖`. -/
theorem F_inv_second_deriv_bound_core {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1)
    {F_inv : ℂ → ℂ}
    (hF_an : AnalyticOnNhd ℂ F_inv (disk (r1 r)))
    (hF_R  : ∀ z ∈ disk (r1 r), ‖F_inv z‖ ≤ R_val_paper r) :
    ∀ z₀ ∈ disk r, ‖iteratedDeriv 2 F_inv z₀‖ ≤ 8 * R_val_paper r / (1 - r) ^ 2 := by
  intro z₀ hz₀
  set g : ℂ → ℂ := fun w => F_inv (z₀ + w) with hg_def
  have hRpos : 0 < (1 - r) / 2 := half_one_sub_pos hr1
  have hg_diff :
      DifferentiableOn ℂ g (closedBall (0 : ℂ) ((1 - r) / 2)) :=
    differentiableOn_recentered hr1 hF_an hz₀
  have hg_bound :
      ∀ w ∈ closedBall (0 : ℂ) ((1 - r) / 2), ‖g w‖ ≤ R_val_paper r :=
    fun w hw => norm_recentered_le hr1 hF_R hz₀ w hw
  have hk2 :
      ‖Braverman.taylor_coeff g 2‖ ≤ R_val_paper r / ((1 - r) / 2) ^ 2 :=
    Braverman.cauchy_taylor_coeff_bound_closedBall hRpos hg_diff hg_bound
  have htc2 :
      Braverman.taylor_coeff g 2 = iteratedDeriv 2 F_inv z₀ / 2 := by
    unfold Braverman.taylor_coeff
    have hid : iteratedDeriv 2 g 0 = iteratedDeriv 2 F_inv z₀ :=
      iteratedDeriv_recentered_zero F_inv z₀ 2
    have hfact : (Nat.factorial 2 : ℂ) = 2 := by norm_num [Nat.factorial]
    rw [hid, hfact]
  have hnorm_eq :
      ‖iteratedDeriv 2 F_inv z₀‖ = 2 * ‖Braverman.taylor_coeff g 2‖ := by
    have h' : iteratedDeriv 2 F_inv z₀ = 2 * Braverman.taylor_coeff g 2 := by
      rw [htc2]; ring
    rw [h', norm_mul]
    norm_num
  have hbnd1 :
      ‖iteratedDeriv 2 F_inv z₀‖ ≤ 2 * (R_val_paper r / ((1 - r) / 2) ^ 2) := by
    rw [hnorm_eq]
    exact mul_le_mul_of_nonneg_left hk2 (by norm_num : (0 : ℝ) ≤ 2)
  have h1mr_pos : 0 < 1 - r := by linarith
  have hsimplify :
      2 * (R_val_paper r / ((1 - r) / 2) ^ 2) = 8 * R_val_paper r / (1 - r) ^ 2 := by
    have h2 : ((1 - r) / 2) ^ 2 = (1 - r) ^ 2 / 4 := by ring
    rw [h2]
    field_simp
    ring
  linarith [hbnd1, hsimplify ▸ hbnd1]

end Braverman.Paper
