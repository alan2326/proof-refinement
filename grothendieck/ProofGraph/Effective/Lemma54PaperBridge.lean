/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54PaperBridge.lean — bridges `lemma_5_4_paper` to `lemma_5_4_strong`'s shape

`lemma_5_4_paper` (in `ProofRefinement/`) concludes a *curried* existential
(F_inv quantified inside ∀ z) without `AnalyticOnNhd` or `F_inv 0 = 0`.

`lemma_5_4_strong` (in `LeanProof/`) requires the *uncurried* form (single
F_inv per p) plus those two extra properties.

This file provides `lemma_5_4_strong_via_paper`, with exactly
`lemma_5_4_strong`'s conclusion shape, proved through the paper-faithful
single-`M` machinery and the `F_inv_paper_*` axioms.

Key ingredients:
* `F_inv := F_inv_paper η r hr0 hr1 p` is the uncurried witness.
* `AnalyticOnNhd` on `disk r` follows from `F_inv_paper_analytic` on
  `disk r₁` (since `disk r ⊆ disk r₁`).
* `F_inv 0 = 0` is the `F_inv_paper_at_origin` axiom.
* The Taylor bound is reproved by re-running
  `F_inv_p_second_deriv_bound_paper + taylor_remainder_p` on the same
  `(η, r, M)` tuple — the same machinery `lemma_5_4_paper` uses internally,
  just exposed here with the uncurried witness.

We require strict positivity of the M-bound (rather than just `0 ≤ ·`) so
that `Cr_paper` is strictly positive, matching `lemma_5_4_strong`'s `0 < Cr`.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

private lemma Cr_paper_pos {r M R : ℝ}
    (hr1 : r < 1) (hM_pos : 0 < M) (hR : 0 < R) :
    0 < Cr_paper r M R := by
  unfold Cr_paper
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  have h1mr_cu_pos : 0 < (1 - r) ^ 3 := by positivity
  have h_lead_pos : 0 < 8 * M ^ 2 * R / (1 - r) ^ 2 := by positivity
  have h_inner_pos : 0 < 1 + 16 * R / (1 - r) ^ 3 := by positivity
  exact mul_pos h_lead_pos h_inner_pos

set_option maxHeartbeats 800000 in
/-- **Bridge: `lemma_5_4_strong` via `lemma_5_4_paper`, on an abstract domain.**

This is the domain-parametric form of the bridge: the M-bound is assumed on an
arbitrary set `E`, together with an explicit containment hypothesis for the
`F_inv_paper` image. This lets the effective layer use the exact oracle domain
instead of the historical envelope. The envelope-based wrapper remains
available below as `lemma_5_4_strong_via_paper`. -/
theorem lemma_5_4_strong_via_paper_on_domain
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_pos : 0 < M) (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_bound :
      ∀ w ∈ E,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
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
  set F_inv := F_inv_paper η r hr0 hr1 with hFinv_def
  set pr := pr_paper η r hr0 hr1 with hpr_def
  have hpr_pos : 0 < pr := pr_paper_pos η r hr0 hr1
  have hpr_le_one : pr ≤ 1 := pr_paper_le_one η r hr0 hr1
  set Cr := Cr_paper r M (R_val_paper r) with hCr_def
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hCr_pos : 0 < Cr := Cr_paper_pos hr1 hM_pos hRpos
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hCr_nn : 0 ≤ Cr := le_of_lt hCr_pos
  refine ⟨Cr, pr, hCr_pos, hpr_pos, ?_⟩
  intro p hp_pos hp_lt
  have hp_Ico : p ∈ Set.Ico (0 : ℝ) pr := ⟨le_of_lt hp_pos, hp_lt⟩
  have hp_Ioo : p ∈ Set.Ioo (0 : ℝ) pr := ⟨hp_pos, hp_lt⟩
  refine ⟨F_inv p, ?_, ?_, ?_, ?_, ?_⟩
  · have h_an_r1 := F_inv_paper_analytic η r hr0 hr1 p hp_Ioo
    exact h_an_r1.mono (disk_subset_disk_r1 hr1)
  · intro z hz
    exact F_inv_paper_eq η r hr0 hr1 p hp_Ico z (disk_subset_disk_r1 hr1 hz)
  · intro z hz
    exact F_inv_paper_mem_S η r hr0 hr1 p hp_Ico z (disk_subset_disk_r1 hr1 hz)
  · exact F_inv_paper_at_origin η r hr0 hr1 p hp_Ico
  · -- Taylor bound — re-run the paper-faithful Step 5 + Step 6 machinery.
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
    have h_M_H0_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖H0 (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).1
    have h_M_He_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖H_eta η (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.1
    have h_M_H0p_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖deriv H0 (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.1
    have h_M_Hep_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖deriv (H_eta η) (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.2
    have h_step5 := F_inv_p_second_deriv_bound_paper η hr0 hr1 hpr_pos hM_nn
      F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full hF_p_contdiff_Ioo
      h_M_H0_at h_M_He_at h_M_H0p_at h_M_Hep_at
    have h_second_deriv_bound : ∀ w ∈ disk r, ∀ t ∈ Set.Ico (0 : ℝ) pr,
        ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico (0 : ℝ) pr) t‖
          ≤ 2 * Cr := by
      intro w hw t ht
      have hUnique : UniqueDiffOn ℝ (Set.Ico (0 : ℝ) pr) := uniqueDiffOn_Ico 0 pr
      have h_contInner : ContinuousOn
          (iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico 0 pr))
          (Set.Ico 0 pr) :=
        (hF_p_contdiff_Ico w hw).continuousOn_iteratedDerivWithin (m := 2) (by norm_cast) hUnique
      rcases lt_or_eq_of_le ht.1 with htpos | hteq
      · have htIoo : t ∈ Set.Ioo (0 : ℝ) pr := ⟨htpos, ht.2⟩
        rw [iteratedDerivWithin_2_Ico_eq_iteratedDeriv_on_Ioo _ pr t htIoo]
        exact h_step5 t htIoo w hw
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
          exact h_step5 x hxIoo w hw
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
    intro z hz
    exact h_step6 p hp_Ioo z hz

set_option maxHeartbeats 800000 in
/-- **Bridge variant with `Cr` and `pr` made explicit.** Identical to
`lemma_5_4_strong_via_paper_on_domain` except the conclusion exposes
`Cr_paper r M (R_val_paper r)` and `pr_paper η r hr0 hr1` directly instead
of packaging them existentially. This lets downstream callers
(e.g. `theorem_5_1_at_p_explicit`) compare a concrete rational against
`pr_paper η r hr0 hr1` and use the closed-form `Cr_paper`. -/
theorem lemma_5_4_strong_via_paper_on_domain_explicit
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_pos : 0 < M) (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_bound :
      ∀ w ∈ E,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
    0 < Cr_paper r M (R_val_paper r) ∧
    0 < pr_paper η r hr0 hr1 ∧
    ∀ p : ℝ, 0 < p → p < pr_paper η r hr0 hr1 →
      ∃ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (disk r) ∧
        (∀ z ∈ disk r, F_p η p (F_inv z) = z) ∧
        (∀ z ∈ disk r, F_inv z ∈ S) ∧
        F_inv 0 = 0 ∧
        (∀ z ∈ disk r,
          ‖F_inv z - Complex.sin z -
            ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤
            Cr_paper r M (R_val_paper r) * p ^ 2) := by
  set F_inv := F_inv_paper η r hr0 hr1 with hFinv_def
  set pr := pr_paper η r hr0 hr1 with hpr_def
  have hpr_pos : 0 < pr := pr_paper_pos η r hr0 hr1
  have hpr_le_one : pr ≤ 1 := pr_paper_le_one η r hr0 hr1
  set Cr := Cr_paper r M (R_val_paper r) with hCr_def
  have hRpos : 0 < R_val_paper r := R_val_paper_pos hr0
  have hCr_pos : 0 < Cr := Cr_paper_pos hr1 hM_pos hRpos
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hCr_nn : 0 ≤ Cr := le_of_lt hCr_pos
  refine ⟨hCr_pos, hpr_pos, ?_⟩
  intro p hp_pos hp_lt
  have hp_Ico : p ∈ Set.Ico (0 : ℝ) pr := ⟨le_of_lt hp_pos, hp_lt⟩
  have hp_Ioo : p ∈ Set.Ioo (0 : ℝ) pr := ⟨hp_pos, hp_lt⟩
  refine ⟨F_inv p, ?_, ?_, ?_, ?_, ?_⟩
  · have h_an_r1 := F_inv_paper_analytic η r hr0 hr1 p hp_Ioo
    exact h_an_r1.mono (disk_subset_disk_r1 hr1)
  · intro z hz
    exact F_inv_paper_eq η r hr0 hr1 p hp_Ico z (disk_subset_disk_r1 hr1 hz)
  · intro z hz
    exact F_inv_paper_mem_S η r hr0 hr1 p hp_Ico z (disk_subset_disk_r1 hr1 hz)
  · exact F_inv_paper_at_origin η r hr0 hr1 p hp_Ico
  · -- Taylor bound — re-run the paper-faithful Step 5 + Step 6 machinery.
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
    have h_M_H0_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖H0 (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).1
    have h_M_He_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖H_eta η (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.1
    have h_M_H0p_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖deriv H0 (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.1
    have h_M_Hep_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
        ‖deriv (H_eta η) (F_inv q w)‖ ≤ M := fun q hq w hw =>
      (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.2
    have h_step5 := F_inv_p_second_deriv_bound_paper η hr0 hr1 hpr_pos hM_nn
      F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full hF_p_contdiff_Ioo
      h_M_H0_at h_M_He_at h_M_H0p_at h_M_Hep_at
    have h_second_deriv_bound : ∀ w ∈ disk r, ∀ t ∈ Set.Ico (0 : ℝ) pr,
        ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico (0 : ℝ) pr) t‖
          ≤ 2 * Cr := by
      intro w hw t ht
      have hUnique : UniqueDiffOn ℝ (Set.Ico (0 : ℝ) pr) := uniqueDiffOn_Ico 0 pr
      have h_contInner : ContinuousOn
          (iteratedDerivWithin 2 (fun q : ℝ => F_inv q w) (Set.Ico 0 pr))
          (Set.Ico 0 pr) :=
        (hF_p_contdiff_Ico w hw).continuousOn_iteratedDerivWithin (m := 2) (by norm_cast) hUnique
      rcases lt_or_eq_of_le ht.1 with htpos | hteq
      · have htIoo : t ∈ Set.Ioo (0 : ℝ) pr := ⟨htpos, ht.2⟩
        rw [iteratedDerivWithin_2_Ico_eq_iteratedDeriv_on_Ioo _ pr t htIoo]
        exact h_step5 t htIoo w hw
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
          exact h_step5 x hxIoo w hw
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
    intro z hz
    exact h_step6 p hp_Ioo z hz

/-- **Bridge: `lemma_5_4_strong` via `lemma_5_4_paper`.** Same conclusion
shape as `Braverman.lemma_5_4_strong`, with
`Cr := Cr_paper r M (R_val_paper r)` and `pr := pr_paper η r hr0 hr1`.

Requires strict positivity of the M-bound (so `Cr_paper > 0` is recoverable).
-/
theorem lemma_5_4_strong_via_paper (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_pos : 0 < M)
    (h_M_bound :
      ∀ w ∈ F_inv_envelope r,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
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
  refine lemma_5_4_strong_via_paper_on_domain η r hr0 hr1 M hM_pos (F_inv_envelope r) ?_ h_M_bound
  intro q hq w hw
  have hw_r1 : w ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hw
  refine ⟨?_, F_inv_paper_mem_S η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw_r1⟩
  rw [mem_closedBall, dist_zero_right]
  exact F_inv_paper_R_bound η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw_r1

end Braverman.Paper
