/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper_Main.lean — paper-faithful Lemma 5.4 (top-level theorem)

The conclusion is the second-order Taylor remainder bound for `F_inv`
in `p`, with the **paper's literal** `Cr_paper` constant from Braverman
et al. (2011) p.23:

    Cr_paper r M R := 8·M²·R/(1-r)² · (1 + 16·R/(1-r)³).

The single hypothesis is a uniform sup-norm bound

    M ≥ max{|H_0|, |H_η|, |H_0'|, |H_η'|}  on the F_inv envelope (Ω_r in the paper).

The proof structure mirrors the paper:
* Step 1+2: `F_inv_R_bound` (in `Lemma54_Paper.lean`) — non-joint version
  for reference. The actual joint-regular F_inv comes from the
  axiomatized `F_inv_paper` (12 trusted analytic axioms in `Lemma54_Paper.lean`).
* Step 3:   Cauchy z-derivative bounds (in `Lemma54_Paper_Cauchy.lean`).
* Step 4:   `identity_75` (in `Lemma54_Paper_Identity.lean`).
* Step 5:   `F_inv_p_second_deriv_bound_paper` (in
            `Lemma54_Paper_Pderiv_Single.lean`) — bounds `‖∂²_p F_inv‖`
            via the auxiliary z-identity `DD·h² + D·u_zz = 0` (chain rule
            on `F_p ∘ F_inv = id`) combined with the form-A identity
            `D·u'' = -(2 Φ' u' + DD·u'²)`, recentred Cauchy estimates on
            `d/dz F_inv`, `d²/dz² F_inv`, and the algebraic step
            `(2R+1)(1-r)³ ≤ 16R`.
* Step 6:   `taylor_remainder_p` (in `Lemma54_Paper_Taylor.lean`).

All steps are fully proved. The only assumed axioms are the 12 trusted
analytic facts about the joint-regular `F_inv_paper` family (existence,
analyticity-in-`z`, `C²`-in-`p`, right-inverse identity, image bounds)
in `Lemma54_Paper.lean`, supplied by the implicit function theorem
applied to `(p, w) ↦ F_p η p w` near `(0, sin z)`.
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Cauchy
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Identity
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv_Single
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Taylor

open Complex Set Metric Real

noncomputable section

/-! ### Helpers: `iteratedDerivWithin` ↔ `iteratedDeriv` on the open interior -/

namespace Braverman.Paper

/-- Within `Ioo 0 pr`, `derivWithin u (Ico 0 pr)` agrees with `deriv u`. -/
lemma derivWithin_Ico_eq_deriv_on_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) (pr : ℝ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) pr, derivWithin u (Set.Ico 0 pr) t = deriv u t := by
  intro t ht
  apply derivWithin_of_mem_nhds
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
    (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)

/-- Within `Ioo 0 pr`, `iteratedDerivWithin 2 u (Ico 0 pr)` agrees with
`iteratedDeriv 2 u`. -/
lemma iteratedDerivWithin_2_Ico_eq_iteratedDeriv_on_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) (pr : ℝ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) pr,
      iteratedDerivWithin 2 u (Set.Ico 0 pr) t = iteratedDeriv 2 u t := by
  intro t ht
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
  rw [show iteratedDeriv 2 u = deriv (deriv u) from by
    funext x; rw [iteratedDeriv_succ, iteratedDeriv_one]]
  have hIco_nhds : Set.Ico (0 : ℝ) pr ∈ nhds t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have h_outer : derivWithin (derivWithin u (Set.Ico 0 pr)) (Set.Ico 0 pr) t
      = deriv (derivWithin u (Set.Ico 0 pr)) t :=
    derivWithin_of_mem_nhds hIco_nhds
  rw [h_outer]
  have h_eqOn : (derivWithin u (Set.Ico 0 pr)) =ᶠ[nhds t] deriv u := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo 0 pr, isOpen_Ioo.mem_nhds ht, ?_⟩
    intro x hx
    exact derivWithin_Ico_eq_deriv_on_Ioo u pr x hx
  exact Filter.EventuallyEq.deriv_eq h_eqOn

end Braverman.Paper

namespace Braverman.Paper

/-! ## Glue lemmas: paper-faithful, single-`M` -/

-- Heartbeats raised: chains 12 IFT axioms + paper Step 5 (Pderiv_Single)
-- + Taylor remainder (Pderiv); single-pass elaboration is heavy.
set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain.**

This is the paper-faithful single-`M` statement, but the sup-norm bound is
phrased on an arbitrary set `E` together with a separate oracle-style
containment hypothesis `F_inv_paper(disk r) ⊆ E`. This isolates the real
load-bearing property from the historical `F_inv_envelope` choice and lets the
effective layer instantiate the theorem with the exact numerical domain
certified by the Python side.

The default envelope-based version remains available below as
`lemma_5_4_paper`. -/
theorem lemma_5_4_paper_on_domain (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_nn : 0 ≤ M) (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_bound :
      ∀ w ∈ E,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_paper r M (R_val_paper r) * p ^ 2 := by
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
  have h_M_H0_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H0 (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).1
  have h_M_He_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.1
  have h_M_H0p_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv H0 (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.1
  have h_M_Hep_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.2
  have h_step5 := F_inv_p_second_deriv_bound_paper η hr0 hr1 hpr_pos hM_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full hF_p_contdiff_Ioo
    h_M_H0_at h_M_He_at h_M_H0p_at h_M_Hep_at
  set Cr := Cr_paper r M (R_val_paper r) with hCr_def
  have hCr_nn : 0 ≤ Cr := Cr_paper_nonneg hr1 hM_nn (R_val_paper_nonneg hr0)
  -- Extend the bound from Ioo to Ico.
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

-- Heartbeats raised: chains 12 IFT axioms + paper Step 5 (Pderiv_Single)
-- + Taylor remainder (Pderiv); single-pass elaboration is heavy.
set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — tight `Cr` version.**

Same as `lemma_5_4_paper_on_domain` but the conclusion is stated with the
tighter `Cr_tight r M (R_val_paper r) = 16 M² R (R+1) / (1-r)²` in place
of `Cr_paper`, eliminating the loose `(2R+1)(1-r)³ ≤ 16R` algebraic step
in the closing arithmetic of `F_inv_p_second_deriv_bound_paper`.

The proof body mirrors `lemma_5_4_paper_on_domain` exactly, with two
substitutions:
* `Cr := Cr_tight r M (R_val_paper r)` (was `Cr_paper`);
* `F_inv_p_second_deriv_bound_tight` (was `F_inv_p_second_deriv_bound_paper`).

The Lagrange remainder step (`taylor_remainder_p`) is `Cr`-polymorphic, so
no further changes are needed: it consumes the `≤ 2 * Cr` second-derivative
bound, halves it via `1/2!`, and produces the `Cr * p²` conclusion. -/
theorem lemma_5_4_paper_on_domain_tight (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_nn : 0 ≤ M) (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_bound :
      ∀ w ∈ E,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_tight r M (R_val_paper r) * p ^ 2 := by
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
  have h_M_H0_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H0 (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).1
  have h_M_He_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.1
  have h_M_H0p_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv H0 (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.1
  have h_M_Hep_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w)‖ ≤ M := by
    intro q hq w hw
    exact (h_M_bound (F_inv q w) (h_image_domain q hq w hw)).2.2.2
  have h_step5 := F_inv_p_second_deriv_bound_tight η hr0 hr1 hpr_pos hM_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full hF_p_contdiff_Ioo
    h_M_H0_at h_M_He_at h_M_H0p_at h_M_Hep_at
  set Cr := Cr_tight r M (R_val_paper r) with hCr_def
  have hCr_nn : 0 ≤ Cr := Cr_tight_nonneg hr1 hM_nn (R_val_paper_nonneg hr0)
  -- Extend the bound from Ioo to Ico.
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

-- Heartbeats raised: chains 12 IFT axioms + paper Step 5 (Pderiv_Single, _phi)
-- + Taylor remainder (Pderiv); single-pass elaboration is heavy.
set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — η-aware `Cr_phi` version.**

Same as `lemma_5_4_paper_on_domain_tight` but the conclusion is stated with
the hybrid `Cr_phi r M_phi M_phi_prime (R_val_paper r)` constant, which
consumes η-aware sup-norm bounds on `H_η - H_0` (via `M_phi`) and
`H_η' - H_0'` (via `M_phi_prime`) instead of the loose triangle bounds
`‖Φ‖, ‖Φ'‖ ≤ 2M`. The Cauchy step `‖u_zz‖ ≤ 8R/(1-r)²` is retained
(no `M_pp` consumption — at the candidate's parameters the implicit-
function chain via `M_pp · invFp³` would be worse than direct Cauchy).

The proof body mirrors `lemma_5_4_paper_on_domain_tight`, with two
substitutions:
* `Cr := Cr_phi r M_phi M_phi_prime (R_val_paper r)` (was `Cr_tight r M …`);
* `F_inv_p_second_deriv_bound_phi` (was `_tight`); the new theorem takes
  two new hypotheses (`h_M_phi_bound`, `h_M_phi_prime_bound`) lifted from
  the analogous oracle-style hypotheses on the abstract domain `E`.

The Lagrange remainder step (`taylor_remainder_p`) is `Cr`-polymorphic, so
no further changes are needed: it consumes the `≤ 2 * Cr` second-derivative
bound, halves it via `1/2!`, and produces the `Cr * p²` conclusion. -/
theorem lemma_5_4_paper_on_domain_phi (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M_phi M_phi_prime : ℝ) (hM_phi_nn : 0 ≤ M_phi) (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_phi_bound_dom :
      ∀ w ∈ E, ‖H_eta η w - H0 w‖ ≤ M_phi)
    (h_M_phi_prime_bound_dom :
      ∀ w ∈ E, ‖deriv (H_eta η) w - deriv H0 w‖ ≤ M_phi_prime) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi r M_phi M_phi_prime (R_val_paper r) * p ^ 2 := by
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
  have h_M_phi_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w) - H0 (F_inv q w)‖ ≤ M_phi := by
    intro q hq w hw
    exact h_M_phi_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_M_phi_prime_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w)‖ ≤ M_phi_prime := by
    intro q hq w hw
    exact h_M_phi_prime_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi η hr0 hr1 hpr_pos hM_phi_nn
    hM_phi_prime_nn F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_M_phi_at h_M_phi_prime_at
  set Cr := Cr_phi r M_phi M_phi_prime (R_val_paper r) with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_nonneg hr1 hM_phi_nn hM_phi_prime_nn (R_val_paper_nonneg hr0)
  -- Extend the bound from Ioo to Ico.
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

-- Heartbeats raised: chains 12 IFT axioms + paper Step 5 (Pderiv_Single, _phi_invD)
-- + Taylor remainder (Pderiv); single-pass elaboration is heavy.
set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — η-aware `Cr_phi_invD`
version with arb-supplied `1/‖∂_z F_p‖` bound.**

Same as `lemma_5_4_paper_on_domain_phi` but the loose paper bound
`1/‖∂_z F_p‖ ≤ 2R/(1−r)` is replaced by an *abstract* parameter
`inv_F_p_z` together with an oracle hypothesis
`h_inv_F_p_z_oracle_dom` which the candidate-level pipeline backs by
an arb-certified numerical sup over the rectangle. At candidate
parameters this gives `inv_F_p_z ≈ 2` versus the paper bound
≈ 28.75 — a ~14× tightening of `invFp` (~196× of `invFp²`) — so
`Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z` is roughly half of
`Cr_phi r M_phi M_phi_prime R` at V9 parameters.

The proof body mirrors `lemma_5_4_paper_on_domain_phi`, with two
substitutions:
* `Cr := Cr_phi_invD r M_phi M_phi_prime (R_val_paper r) inv_F_p_z`
  (was `Cr_phi r M_phi M_phi_prime (R_val_paper r)`);
* `F_inv_p_second_deriv_bound_phi_invD` (was `_phi`); the new theorem
  takes one extra hypothesis (`h_invD_bound`) lifted from the
  oracle-style hypothesis on the abstract domain `E`. -/
theorem lemma_5_4_paper_on_domain_phi_invD (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M_phi M_phi_prime : ℝ) (hM_phi_nn : 0 ≤ M_phi) (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_phi_bound_dom :
      ∀ w ∈ E, ‖H_eta η w - H0 w‖ ≤ M_phi)
    (h_M_phi_prime_bound_dom :
      ∀ w ∈ E, ‖deriv (H_eta η) w - deriv H0 w‖ ≤ M_phi_prime)
    (h_inv_F_p_z_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        1 ≤ ‖deriv (F_p η q) w‖ * inv_F_p_z) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_invD r M_phi M_phi_prime (R_val_paper r) inv_F_p_z * p ^ 2 := by
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
  have h_M_phi_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w) - H0 (F_inv q w)‖ ≤ M_phi := by
    intro q hq w hw
    exact h_M_phi_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_M_phi_prime_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w)‖ ≤ M_phi_prime := by
    intro q hq w hw
    exact h_M_phi_prime_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  -- Lift the oracle hypothesis on `E` to a per-`q`/per-`w ∈ disk r` form
  -- via `h_image_domain`.
  have h_invD_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      1 ≤ ‖deriv (F_p η q) (F_inv q w)‖ * inv_F_p_z := by
    intro q hq w hw
    exact h_inv_F_p_z_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_invD η hr0 hr1 hpr_pos hM_phi_nn
    hM_phi_prime_nn inv_F_p_z h_inv_F_p_z_nn F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_M_phi_at h_M_phi_prime_at h_invD_at
  set Cr := Cr_phi_invD r M_phi M_phi_prime (R_val_paper r) inv_F_p_z with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_invD_nonneg hr1 hM_phi_nn hM_phi_prime_nn (R_val_paper_nonneg hr0)
      h_inv_F_p_z_nn
  -- Extend the bound from Ioo to Ico.
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

-- Heartbeats raised: chains 12 IFT axioms + paper Step 5
-- (Pderiv_Single, _phi_uzz with aux-z-identity-driven u_zz bound)
-- + Taylor remainder (Pderiv); single-pass elaboration is heavy.
set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — η-aware `Cr_phi_uzz`
version with arb-supplied `1/‖∂_z F_p‖` AND `‖∂²_z F_p‖` bounds.**

Same as `lemma_5_4_paper_on_domain_phi_invD` but the recentred-Cauchy
bound on `‖u_zz‖` (`‖u_zz‖ ≤ 8R/(1-r)²`) is replaced by an
aux-z-identity-driven bound `‖u_zz‖ ≤ M_pp · inv_F_p_z³`, sourced from
the identity `DD · h² + D · u_zz = 0` together with the certified
sup-norm bounds `‖DD‖ ≤ M_pp` (`h_M_pp_oracle_dom`) and
`1/‖D‖ ≤ inv_F_p_z` (`h_inv_F_p_z_oracle_dom`). At candidate parameters
this gives `‖u_zz‖ ≤ 449` versus the paper Cauchy bound ≈ 1393 — a
3.1× tightening of the dominant term-2 chunk.

The proof body mirrors `lemma_5_4_paper_on_domain_phi_invD`, with two
substitutions:
* `Cr := Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp`
  (was `Cr_phi_invD r M_phi M_phi_prime (R_val_paper r) inv_F_p_z`);
* `F_inv_p_second_deriv_bound_phi_uzz` (was `_phi_invD`); the new theorem
  takes one extra oracle hypothesis (`h_M_pp_bound`) lifted from the
  oracle-style hypothesis on the abstract domain `E`. -/
theorem lemma_5_4_paper_on_domain_phi_uzz (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M_phi M_phi_prime : ℝ) (hM_phi_nn : 0 ≤ M_phi) (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (M_pp : ℝ) (h_M_pp_nn : 0 ≤ M_pp)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_phi_bound_dom :
      ∀ w ∈ E, ‖H_eta η w - H0 w‖ ≤ M_phi)
    (h_M_phi_prime_bound_dom :
      ∀ w ∈ E, ‖deriv (H_eta η) w - deriv H0 w‖ ≤ M_phi_prime)
    (h_inv_F_p_z_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        1 ≤ ‖deriv (F_p η q) w‖ * inv_F_p_z)
    (h_M_pp_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖iteratedDeriv 2 (F_p η q) w‖ ≤ M_pp) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p ^ 2 := by
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
  have h_M_phi_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w) - H0 (F_inv q w)‖ ≤ M_phi := by
    intro q hq w hw
    exact h_M_phi_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_M_phi_prime_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w)‖ ≤ M_phi_prime := by
    intro q hq w hw
    exact h_M_phi_prime_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  -- Lift the inv_F_p_z oracle hypothesis on `E` to a per-`q`/per-`w ∈ disk r` form
  -- via `h_image_domain`.
  have h_invD_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      1 ≤ ‖deriv (F_p η q) (F_inv q w)‖ * inv_F_p_z := by
    intro q hq w hw
    exact h_inv_F_p_z_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  -- Lift the M_pp oracle hypothesis on `E` to a per-`q`/per-`w ∈ disk r` form
  -- via `h_image_domain`.
  have h_M_pp_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖iteratedDeriv 2 (F_p η q) (F_inv q w)‖ ≤ M_pp := by
    intro q hq w hw
    exact h_M_pp_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_uzz η hr0 hr1 hpr_pos hM_phi_nn
    hM_phi_prime_nn inv_F_p_z h_inv_F_p_z_nn M_pp h_M_pp_nn F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_M_phi_at h_M_phi_prime_at h_invD_at h_M_pp_at
  set Cr := Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_uzz_nonneg hM_phi_nn hM_phi_prime_nn h_inv_F_p_z_nn h_M_pp_nn
  -- Extend the bound from Ioo to Ico.
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

set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — η-aware
`Cr_phi_uzz_direct` version with arb-supplied direct `‖u_zz‖` bound.**

Same as `lemma_5_4_paper_on_domain_phi_uzz` but the two-oracle product
bound `‖u_zz‖ ≤ M_pp · inv_F_p_z³` is replaced by a single direct
oracle hypothesis `‖DD‖ ≤ ‖D‖³ · u_zz_bound` on the joint analytic
quotient. By the auxiliary z-identity, this is `‖u_zz‖ ≤ u_zz_bound`
directly — fundamentally tighter than the triangle product, since the
sup of `‖DD‖/‖D‖³` over the rectangle is much smaller than the product
of the individual sups.

At candidate parameters this gives `u_zz_bound ≈ 1.55` versus V11's
`M_pp · inv_F_p_z³ ≈ 449` — a ~289× tightening on the dominant
term-2 chunk, enabling `Cr_val := 1/32` (a 32× reduction over V11). -/
theorem lemma_5_4_paper_on_domain_phi_uzz_direct
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M_phi M_phi_prime : ℝ) (hM_phi_nn : 0 ≤ M_phi) (hM_phi_prime_nn : 0 ≤ M_phi_prime)
    (inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)
    (u_zz_bound : ℝ) (h_u_zz_nn : 0 ≤ u_zz_bound)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_phi_bound_dom :
      ∀ w ∈ E, ‖H_eta η w - H0 w‖ ≤ M_phi)
    (h_M_phi_prime_bound_dom :
      ∀ w ∈ E, ‖deriv (H_eta η) w - deriv H0 w‖ ≤ M_phi_prime)
    (h_inv_F_p_z_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        1 ≤ ‖deriv (F_p η q) w‖ * inv_F_p_z)
    (h_u_zz_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖iteratedDeriv 2 (F_p η q) w‖
          ≤ ‖deriv (F_p η q) w‖ ^ 3 * u_zz_bound) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound * p ^ 2 := by
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
  have h_M_phi_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w) - H0 (F_inv q w)‖ ≤ M_phi := by
    intro q hq w hw
    exact h_M_phi_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_M_phi_prime_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w)‖ ≤ M_phi_prime := by
    intro q hq w hw
    exact h_M_phi_prime_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_invD_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      1 ≤ ‖deriv (F_p η q) (F_inv q w)‖ * inv_F_p_z := by
    intro q hq w hw
    exact h_inv_F_p_z_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  -- Lift the u_zz oracle hypothesis on `E` to a per-`q`/per-`w ∈ disk r` form
  -- via `h_image_domain`.
  have h_u_zz_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖iteratedDeriv 2 (F_p η q) (F_inv q w)‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 3 * u_zz_bound := by
    intro q hq w hw
    exact h_u_zz_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_uzz_direct η hr0 hr1 hpr_pos hM_phi_nn
    hM_phi_prime_nn inv_F_p_z h_inv_F_p_z_nn u_zz_bound h_u_zz_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_M_phi_at h_M_phi_prime_at h_invD_at h_u_zz_at
  set Cr := Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_uzz_direct_nonneg hM_phi_nn hM_phi_prime_nn h_inv_F_p_z_nn h_u_zz_nn
  -- Extend the bound from Ioo to Ico.
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

set_option maxHeartbeats 800000 in
/-- **Lemma 5.4 on an abstract certified domain — η-aware
`Cr_phi_uzz_direct_joint` version with arb-supplied joint
`‖Phi · Phi' / D²‖` bound and direct ‖u_zz‖ bound.**

Same as `lemma_5_4_paper_on_domain_phi_uzz_direct` but the term-1
triangle product `M_phi · M_phi_prime · inv_F_p_z²` is replaced by a
single direct oracle hypothesis `‖Phi · Phi'‖ ≤ ‖D‖² · joint`. By the
joint sup binding at a single (p, w) rather than separate suprema, this
is fundamentally tighter than the product. -/
theorem lemma_5_4_paper_on_domain_phi_uzz_direct_joint
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M_phi : ℝ) (hM_phi_nn : 0 ≤ M_phi)
    (joint_phi_phip_invD2 : ℝ) (h_joint_nn : 0 ≤ joint_phi_phip_invD2)
    (u_zz_bound : ℝ) (h_u_zz_nn : 0 ≤ u_zz_bound)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_M_phi_bound_dom :
      ∀ w ∈ E, ‖H_eta η w - H0 w‖ ≤ M_phi)
    (h_joint_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖(H_eta η w - H0 w) * (deriv (H_eta η) w - deriv H0 w)‖
          ≤ ‖deriv (F_p η q) w‖ ^ 2 * joint_phi_phip_invD2)
    (h_u_zz_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖iteratedDeriv 2 (F_p η q) w‖
          ≤ ‖deriv (F_p η q) w‖ ^ 3 * u_zz_bound) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound * p ^ 2 := by
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
  have h_M_phi_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖H_eta η (F_inv q w) - H0 (F_inv q w)‖ ≤ M_phi := by
    intro q hq w hw
    exact h_M_phi_bound_dom (F_inv q w) (h_image_domain q hq w hw)
  have h_joint_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖(H_eta η (F_inv q w) - H0 (F_inv q w)) *
        (deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w))‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 2 * joint_phi_phip_invD2 := by
    intro q hq w hw
    exact h_joint_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_u_zz_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖iteratedDeriv 2 (F_p η q) (F_inv q w)‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 3 * u_zz_bound := by
    intro q hq w hw
    exact h_u_zz_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_uzz_direct_joint η hr0 hr1 hpr_pos hM_phi_nn
    joint_phi_phip_invD2 h_joint_nn u_zz_bound h_u_zz_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_M_phi_at h_joint_at h_u_zz_at
  set Cr := Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_uzz_direct_joint_nonneg hM_phi_nn h_joint_nn h_u_zz_nn
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

/-- **`lemma_5_4_paper_on_domain` variant — term-1 + term-2 joint.**
Same shape as `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`, but
replaces V14's term-2 triangle product `u_zz_bound · M_phi²` with a
single direct oracle on the analytic quotient `‖DD · Phi² / D³‖`. -/
theorem lemma_5_4_paper_on_domain_phi_uzz_direct_joint2
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (joint_phi_phip_invD2 : ℝ) (h_joint_nn : 0 ≤ joint_phi_phip_invD2)
    (uzz_phi_sq : ℝ) (h_uzz_phi_sq_nn : 0 ≤ uzz_phi_sq)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_joint_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖(H_eta η w - H0 w) * (deriv (H_eta η) w - deriv H0 w)‖
          ≤ ‖deriv (F_p η q) w‖ ^ 2 * joint_phi_phip_invD2)
    (h_uzz_phi_sq_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖iteratedDeriv 2 (F_p η q) w * (H_eta η w - H0 w) ^ 2‖
          ≤ ‖deriv (F_p η q) w‖ ^ 3 * uzz_phi_sq) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq * p ^ 2 := by
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
  have h_joint_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖(H_eta η (F_inv q w) - H0 (F_inv q w)) *
        (deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w))‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 2 * joint_phi_phip_invD2 := by
    intro q hq w hw
    exact h_joint_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_uzz_phi_sq_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖iteratedDeriv 2 (F_p η q) (F_inv q w) *
        (H_eta η (F_inv q w) - H0 (F_inv q w)) ^ 2‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 3 * uzz_phi_sq := by
    intro q hq w hw
    exact h_uzz_phi_sq_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_uzz_direct_joint2 η hr0 hr1 hpr_pos
    joint_phi_phip_invD2 h_joint_nn uzz_phi_sq h_uzz_phi_sq_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_joint_at h_uzz_phi_sq_at
  set Cr := Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_uzz_direct_joint2_nonneg h_joint_nn h_uzz_phi_sq_nn
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

/-- **Merged-numerator variant of Lemma 5.4 on a domain.**

Same shape as `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` but
collapses the two-oracle joint+uzz triangle product into a *single*
oracle on the exact `|u''|` quotient `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³`.
By the form-A identity combined with `u' = -Phi/D`, this quotient is
*exactly* `‖u''‖`, so the merged oracle captures the destructive
interference between `2·Phi·Phi'·D` and `DD·Phi²` (which have opposite
signs at our (η, r) configuration) inside one acb interval per cell.

The Cr formula reduces to `Cr_phi_uzz_merged merged_uderiv =
(1/2) · merged_uderiv` directly. -/
theorem lemma_5_4_paper_on_domain_phi_uzz_merged
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (merged_uderiv : ℝ) (h_merged_nn : 0 ≤ merged_uderiv)
    (E : Set ℂ)
    (h_image_domain :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
        F_inv_paper η r hr0 hr1 q w ∈ E)
    (h_merged_oracle_dom :
      ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
        ‖2 * (H_eta η w - H0 w) *
            (deriv (H_eta η) w - deriv H0 w) *
            deriv (F_p η q) w
          - iteratedDeriv 2 (F_p η q) w * (H_eta η w - H0 w) ^ 2‖
          ≤ ‖deriv (F_p η q) w‖ ^ 3 * merged_uderiv) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_phi_uzz_merged merged_uderiv * p ^ 2 := by
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
  have h_merged_at : ∀ q ∈ Set.Ioo (0 : ℝ) pr, ∀ w ∈ disk r,
      ‖2 * (H_eta η (F_inv q w) - H0 (F_inv q w)) *
          (deriv (H_eta η) (F_inv q w) - deriv H0 (F_inv q w)) *
          deriv (F_p η q) (F_inv q w)
        - iteratedDeriv 2 (F_p η q) (F_inv q w) *
          (H_eta η (F_inv q w) - H0 (F_inv q w)) ^ 2‖
        ≤ ‖deriv (F_p η q) (F_inv q w)‖ ^ 3 * merged_uderiv := by
    intro q hq w hw
    exact h_merged_oracle_dom q hq (F_inv q w) (h_image_domain q hq w hw)
  have h_step5 := F_inv_p_second_deriv_bound_phi_uzz_merged η hr0 hr1 hpr_pos
    merged_uderiv h_merged_nn
    F_inv hF_an hF_inv_eq_full hF_S_full hF_R_full
    hF_p_contdiff_Ioo h_merged_at
  set Cr := Cr_phi_uzz_merged merged_uderiv with hCr_def
  have hCr_nn : 0 ≤ Cr :=
    Cr_phi_uzz_merged_nonneg h_merged_nn
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

/-- **Lemma 5.4 (paper-faithful, Braverman et al. 2011 p.23).**

For every `r ∈ (0, 1)` and every certified sup-norm bound `M` on
*all four* of `H_0`, `H_η`, `H_0'`, `H_η'` over the F_inv-image envelope
`closedBall 0 (sinh r₂) ∩ S`, there exists `pr_paper > 0` such that
for every `p ∈ (0, pr_paper)` and `z ∈ disk r`, there is an analytic
right-inverse `F_inv` of `F_p η p` satisfying

  `‖F_inv z − sin z − p · (z − H_η(sin z)) · cos z‖`
    `≤ Cr_paper r M (sinh r₂) · p²`.

The constant `Cr_paper r M R = 8·M²·R/(1-r)² · (1 + 16·R/(1-r)³)`
is the closed-form `def` in `Lemma54_Paper.lean` — readable directly
from the theorem statement.

This is **Braverman et al.'s literal Lemma 5.4**, faithful to the bound
proved on p.23 of the 2011 paper. The strategy is:
1. Cauchy on `disk r₁` → `‖d/dz F_inv‖ ≤ 4R/(1-r)²`,
   `‖d²/dz² F_inv‖ ≤ 16R/(1-r)³`.
2. Identity (75) → `|d²/dp² F_inv| ≤ (2M + 2M·16R/(1-r)³) · 2M · 4R/(1-r)²`.
3. Lagrange Taylor remainder → `Cr_paper · p²` with `Cr_paper` as above. -/
theorem lemma_5_4_paper (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℝ) (hM_nn : 0 ≤ M)
    (h_M_bound :
      ∀ w ∈ F_inv_envelope r,
        ‖H0 w‖ ≤ M ∧ ‖H_eta η w‖ ≤ M ∧
        ‖deriv H0 w‖ ≤ M ∧ ‖deriv (H_eta η) w‖ ≤ M) :
    ∃ pr_paper : ℝ, 0 < pr_paper ∧ ∀ p : ℝ, 0 < p → p < pr_paper →
      ∀ z ∈ disk r,
        ∃ F_inv : ℂ → ℂ,
          F_p η p (F_inv z) = z ∧
          F_inv z ∈ S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_paper r M (R_val_paper r) * p ^ 2 := by
  refine lemma_5_4_paper_on_domain η r hr0 hr1 M hM_nn (F_inv_envelope r) ?_ h_M_bound
  intro q hq w hw
  have hw_r1 : w ∈ disk (r1 r) := disk_subset_disk_r1 hr1 hw
  refine ⟨?_, F_inv_paper_mem_S η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw_r1⟩
  rw [mem_closedBall, dist_zero_right]
  exact F_inv_paper_R_bound η r hr0 hr1 q ⟨le_of_lt hq.1, hq.2⟩ w hw_r1

end Braverman.Paper
