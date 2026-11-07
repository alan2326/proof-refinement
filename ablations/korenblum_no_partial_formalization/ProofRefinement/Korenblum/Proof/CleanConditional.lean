import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.PolarIntegrability
import ProofRefinement.Korenblum.Proof.RadialIntegrability

/-!
# Clean conditional Korenblum reduction in contract-shaped form

This file exposes the headline conditional Korenblum reduction whose
hypotheses are exactly `ValidKorenblumBound`-contract-shaped (analyticity
on `UnitDisk` plus `Integrable (‖·‖²) (volume.restrict UnitDisk)`) plus
the inner-half radial dominance hypothesis `h_inner` and the outer-half
pointwise dominance hypothesis `h_outer`.

The composition path is:

* `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (sprint 012) —
  analytic-`f` polar pullback bridge.
* `radial_integrableOn_circleMeanSq_mul_r_Ioc` /
  `radial_integrableOn_circleMeanSq_mul_r_Ioo` /
  `circle_integrableOn_normSq_polar_Ioo_ae` (sprint 013) — six integrability
  derivations in the radial / per-θ slice forms consumed by the conditional
  reduction.
* `validKorenblum_of_innerCircleMean_dom_ae` (this file) — `∀ᵐ`-variant of
  the conditional reduction in `Proof/RadialSplit.lean`, derived inline
  here so that the existing reduction stays untouched. The variant's outer
  half closes via `setIntegral_mono_on_ae` rather than `setIntegral_mono_on`,
  consuming the `∀ᵐ`-form per-radius circle integrability.

Sprint 013 ships V13 with `c_value = 3554/10000` unchanged from V12; this
sprint is scaffolding-only and closes the last contract → conditional
plumbing gap. After this sprint, every remaining gap to a c-push attempt
is mathematical content, not Lean plumbing.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## `_ae`-variant of `validKorenblum_of_innerCircleMean_dom`

Same statement as `validKorenblum_of_innerCircleMean_dom` but with the
per-radius circle integrability hypotheses `hf_circle` / `hg_circle` in
`∀ᵐ` form. The proof structure mirrors the original; only the outer
half uses `setIntegral_mono_on_ae` rather than `setIntegral_mono_on`. -/
theorem validKorenblum_of_innerCircleMean_dom_ae
    (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hg_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hf_inner_int :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioc 0 c) volume)
    (hf_outer_int :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioo c 1) volume)
    (hg_inner_int :
        IntegrableOn (fun r => circleMeanSq g r * r)
                     (Set.Ioc 0 c) volume)
    (hg_outer_int :
        IntegrableOn (fun r => circleMeanSq g r * r)
                     (Set.Ioo c 1) volume)
    (hf_circle_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
        IntegrableOn
          (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (Set.Ioo (-Real.pi) Real.pi) volume)
    (hg_circle_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
        IntegrableOn
          (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (Set.Ioo (-Real.pi) Real.pi) volume)
    (h_inner : ∀ r ∈ Set.Ioc 0 c,
        circleMeanSq f r ≤ circleMeanSq g r)
    (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    bergmanNormSq f ≤ bergmanNormSq g := by
  -- Rewrite both sides via the radial polar form.
  rw [bergmanNormSq_radial_polar hf_polar,
      bergmanNormSq_radial_polar hg_polar]
  -- Split each side at radius c.
  rw [radialIntegral_split f c hc hc1 hf_inner_int hf_outer_int,
      radialIntegral_split g c hc hc1 hg_inner_int hg_outer_int]
  -- Combine the two halves additively.
  refine add_le_add ?_ ?_
  · -- Inner half: pointwise dominance from h_inner (unchanged from
    -- `validKorenblum_of_innerCircleMean_dom`).
    refine setIntegral_mono_on hf_inner_int hg_inner_int measurableSet_Ioc ?_
    intro r hr
    have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt hr.1
    exact mul_le_mul_of_nonneg_right (h_inner r hr) hr_nonneg
  · -- Outer half: `∀ᵐ`-form circle-mean comparison.
    refine setIntegral_mono_ae_restrict hf_outer_int hg_outer_int ?_
    -- Show `(fun r => circleMeanSq f r * r) ≤ᵐ[volume.restrict (Ioo c 1)]
    --        (fun r => circleMeanSq g r * r)`.
    have h_in_set : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)), r ∈ Set.Ioo c 1 :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [hf_circle_ae, hg_circle_ae, h_in_set] with
      r hf_int_r hg_int_r hr_mem
    have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt (lt_trans hc hr_mem.1)
    have hcm : circleMeanSq f r ≤ circleMeanSq g r :=
      circleMeanSq_le_of_outerAnnulus_dom f g c (le_of_lt hc) h_outer hr_mem
        hf_int_r hg_int_r
    exact mul_le_mul_of_nonneg_right hcm hr_nonneg

/-! ## Headline clean conditional Korenblum reduction

The `ValidKorenblumBound`-contract-shaped composition. -/

/-- **Clean conditional Korenblum reduction.**

Given:
* `f, g : ℂ → ℂ` analytic on `UnitDisk`,
* `‖f‖²`, `‖g‖²` integrable on `UnitDisk` (the `volume.restrict UnitDisk`
  Bergman A² integrability hypothesis),
* `h_inner` — inner-half radial dominance: for every `r ∈ Ioc 0 c`,
  `circleMeanSq f r ≤ circleMeanSq g r`,
* `h_outer` — outer-half pointwise dominance: for every `z ∈ outerAnnulus c`,
  `‖f z‖ ≤ ‖g z‖`,

the Bergman A² seminorm inequality `bergmanNormSq f ≤ bergmanNormSq g`
follows.

This is a **composition** of three pieces:
1. `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (sprint 012) —
   the polar-pullback `IntegrableOn` from analytic + Bergman A² integrable.
2. The six radial / per-θ integrability bridges from
   `Proof/RadialIntegrability.lean` (sprint 013) — derive the radial
   integrabilities (in `Ioc 0 c` and `Ioo c 1` form) and the `∀ᵐ`-form
   per-radius circle integrability from the polar pullback.
3. `validKorenblum_of_innerCircleMean_dom_ae` (this file) — the `∀ᵐ`-form
   conditional reduction.

After this composition, the only remaining mathematical content for any
future c-push is `h_inner` (the inner-half radial dominance), which is
the genuine Korenblum content. -/
theorem validKorenblum_of_inner_outer_dom_of_analyticOn
    (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk))
    (hg_int : Integrable (fun z => ‖g z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk))
    (h_inner : ∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r)
    (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    bergmanNormSq f ≤ bergmanNormSq g := by
  -- Step 1: derive the polar-pullback `IntegrableOn` for `f` and `g`.
  have hf_polar : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    polar_integrableOn_of_analyticOn_of_bergmanIntegrable hf_an hf_int
  have hg_polar : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    polar_integrableOn_of_analyticOn_of_bergmanIntegrable hg_an hg_int
  -- Step 2: derive the four radial integrabilities and two ae-form circle
  -- integrabilities from the polar pullbacks.
  have hf_inner_int : IntegrableOn (fun r => circleMeanSq f r * r)
                                    (Set.Ioc 0 c) volume :=
    radial_integrableOn_circleMeanSq_mul_r_Ioc hf_polar hc hc1
  have hf_outer_int : IntegrableOn (fun r => circleMeanSq f r * r)
                                    (Set.Ioo c 1) volume :=
    radial_integrableOn_circleMeanSq_mul_r_Ioo hf_polar hc hc1
  have hg_inner_int : IntegrableOn (fun r => circleMeanSq g r * r)
                                    (Set.Ioc 0 c) volume :=
    radial_integrableOn_circleMeanSq_mul_r_Ioc hg_polar hc hc1
  have hg_outer_int : IntegrableOn (fun r => circleMeanSq g r * r)
                                    (Set.Ioo c 1) volume :=
    radial_integrableOn_circleMeanSq_mul_r_Ioo hg_polar hc hc1
  have hf_circle_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
      IntegrableOn
        (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (Set.Ioo (-Real.pi) Real.pi) volume :=
    circle_integrableOn_normSq_polar_Ioo_ae hf_polar hc hc1
  have hg_circle_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
      IntegrableOn
        (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (Set.Ioo (-Real.pi) Real.pi) volume :=
    circle_integrableOn_normSq_polar_Ioo_ae hg_polar hc hc1
  -- Step 3: apply the `∀ᵐ`-form conditional reduction.
  exact validKorenblum_of_innerCircleMean_dom_ae
    f g c hc hc1
    hf_polar hg_polar
    hf_inner_int hf_outer_int hg_inner_int hg_outer_int
    hf_circle_ae hg_circle_ae
    h_inner h_outer

end ProofRefinement.Korenblum
