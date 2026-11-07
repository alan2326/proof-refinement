import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman

/-!
# Circle-mean comparison from outer-annulus pointwise dominance

This file lifts the outer-annulus pointwise dominance hypothesis
`‖f z‖ ≤ ‖g z‖ on c < ‖z‖ < 1` into the radial / circle-mean world. We
expose:

* `circleMeanSq_le_of_outerAnnulus_dom` — at every fixed radius
  `r ∈ Ioo c 1`, the pointwise outer-annulus dominance hypothesis implies
  `circleMeanSq f r ≤ circleMeanSq g r`.
* `outerAnnulus_norm_sq_mono_via_radial` — a parallel proof of
  `outerAnnulus_norm_sq_mono` (already in `Proof/AnnulusBergman.lean`),
  routed through the radial polar form (`outerAnnulus_norm_sq_polar` plus
  the new circle-mean comparison lemma plus integral monotonicity in `r`).

The point of this file is to produce the *radial-form* statement of
outer-annulus comparison so that future inner-half attacks have a clean
target shape: `circleMeanSq f r ≤ circleMeanSq g r` for `r ∈ Ioc 0 c`.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- Circle-mean comparison from outer-annulus pointwise dominance.

If `‖f z‖ ≤ ‖g z‖` on the outer annulus `c < ‖z‖ < 1`, then for every
fixed radius `r ∈ Ioo c 1` we have `circleMeanSq f r ≤ circleMeanSq g r`.

The proof unfolds `circleMeanSq` on both sides, applies
`setIntegral_mono_on` over `θ ∈ Ioo (-π) π`, and at the pointwise step
derives `polarCoord.symm (r, θ) ∈ outerAnnulus c` (mirroring the step-4
unfold from `outerAnnulus_norm_sq_polar`). -/
theorem circleMeanSq_le_of_outerAnnulus_dom
    (f g : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖)
    {r : ℝ} (hr : r ∈ Set.Ioo c 1)
    (hf_int : IntegrableOn
        (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (Set.Ioo (-Real.pi) Real.pi) volume)
    (hg_int : IntegrableOn
        (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (Set.Ioo (-Real.pi) Real.pi) volume) :
    circleMeanSq f r ≤ circleMeanSq g r := by
  unfold circleMeanSq
  refine setIntegral_mono_on hf_int hg_int measurableSet_Ioo ?_
  intro θ hθ
  -- Show polarCoord.symm (r, θ) ∈ outerAnnulus c.
  have hr_pos : 0 < r := lt_of_le_of_lt hc hr.1
  have h_mem : Complex.polarCoord.symm (r, θ) ∈ outerAnnulus c := by
    unfold outerAnnulus
    simp only [Set.mem_setOf_eq, Complex.norm_polarCoord_symm,
               abs_of_pos hr_pos]
    exact ⟨hr.1, hr.2⟩
  -- Apply h pointwise and square.
  have hle : ‖f (Complex.polarCoord.symm (r, θ))‖
                ≤ ‖g (Complex.polarCoord.symm (r, θ))‖ :=
    h _ h_mem
  have hfz : (0 : ℝ) ≤ ‖f (Complex.polarCoord.symm (r, θ))‖ :=
    norm_nonneg _
  exact pow_le_pow_left₀ hfz hle 2

/-- Outer-annulus monotonicity, re-derived via the radial polar form.

This is the same statement as `outerAnnulus_norm_sq_mono` (in
`Proof/AnnulusBergman.lean`), but the proof routes through the radial
polar form (`outerAnnulus_norm_sq_polar`) plus
`circleMeanSq_le_of_outerAnnulus_dom`, plus `setIntegral_mono_on` over
`r ∈ Ioo c 1`. -/
theorem outerAnnulus_norm_sq_mono_via_radial
    (f g : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hg_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hf_circle : ∀ r ∈ Set.Ioo c 1,
        IntegrableOn
          (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (Set.Ioo (-Real.pi) Real.pi) volume)
    (hg_circle : ∀ r ∈ Set.Ioo c 1,
        IntegrableOn
          (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (Set.Ioo (-Real.pi) Real.pi) volume)
    (hf_radial_int :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioo c 1) volume)
    (hg_radial_int :
        IntegrableOn (fun r => circleMeanSq g r * r)
                     (Set.Ioo c 1) volume)
    (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      ≤ (∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ)) := by
  rw [outerAnnulus_norm_sq_polar f c hc hc1 hf_polar,
      outerAnnulus_norm_sq_polar g c hc hc1 hg_polar]
  refine setIntegral_mono_on hf_radial_int hg_radial_int
    measurableSet_Ioo ?_
  intro r hr
  have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt (lt_of_le_of_lt hc hr.1)
  have hcm : circleMeanSq f r ≤ circleMeanSq g r :=
    circleMeanSq_le_of_outerAnnulus_dom f g c hc h hr
      (hf_circle r hr) (hg_circle r hr)
  exact mul_le_mul_of_nonneg_right hcm hr_nonneg

end ProofRefinement.Korenblum
