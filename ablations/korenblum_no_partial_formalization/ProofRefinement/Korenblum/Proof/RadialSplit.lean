import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare

/-!
# Radial-integral split of `bergmanNormSq` and the conditional Korenblum reduction

This file exposes two scaffolding lemmas that compose with the radial polar
forms of the inner / outer halves established in `Proof/RadialBergman.lean`
and `Proof/CircleMeanCompare.lean`:

* `radialIntegral_split` — the radial integral of `circleMeanSq f r * r`
  over `Ioo 0 1` decomposes as the sum of integrals over `Ioc 0 c` and
  `Ioo c 1`, for any `c ∈ Ioo 0 1` (with appropriate radial integrability).
* `validKorenblum_of_innerCircleMean_dom` — given the inner-half radial
  dominance hypothesis `∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`
  and the outer-half pointwise dominance hypothesis on `outerAnnulus c`,
  the Bergman A² seminorm inequality `bergmanNormSq f ≤ bergmanNormSq g`
  follows. The proof composes the two halves via `radialIntegral_split`,
  routing the outer half through `circleMeanSq_le_of_outerAnnulus_dom`.

The conditional reduction isolates the inner-half radial inequality as the
**only** remaining mathematical obstruction for any future Korenblum-style
attack at higher `c`.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- The disjoint-union set equality `Ioo 0 1 = Ioc 0 c ∪ Ioo c 1` whenever
`0 < c < 1`. Used by `radialIntegral_split`. -/
theorem Ioo_eq_Ioc_union_Ioo {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Set.Ioo (0 : ℝ) 1 = Set.Ioc 0 c ∪ Set.Ioo c 1 := by
  ext r
  simp only [Set.mem_Ioo, Set.mem_Ioc, Set.mem_union]
  constructor
  · rintro ⟨hr0, hr1⟩
    by_cases hrc : r ≤ c
    · exact Or.inl ⟨hr0, hrc⟩
    · push_neg at hrc
      exact Or.inr ⟨hrc, hr1⟩
  · rintro (⟨hr0, hrc⟩ | ⟨hrc, hr1⟩)
    · exact ⟨hr0, lt_of_le_of_lt hrc hc1⟩
    · exact ⟨lt_trans hc hrc, hr1⟩

/-- The disjointness of `Ioc 0 c` and `Ioo c 1`. -/
theorem Ioc_disjoint_Ioo {c : ℝ} :
    Disjoint (Set.Ioc (0 : ℝ) c) (Set.Ioo c 1) := by
  rw [Set.disjoint_left]
  intro r hr_in hr_out
  exact (not_lt.mpr hr_in.2) hr_out.1

/-- Radial-integral split: the radial integral of `circleMeanSq f r * r`
over `Ioo 0 1` is the sum of integrals over `Ioc 0 c` and `Ioo c 1`,
provided the integrand is integrable on each half. -/
theorem radialIntegral_split
    (f : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hf_inner_int :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioc 0 c) volume)
    (hf_outer_int :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioo c 1) volume) :
    (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r)
      = (∫ r in Set.Ioc 0 c, circleMeanSq f r * r)
        + (∫ r in Set.Ioo c 1, circleMeanSq f r * r) := by
  rw [Ioo_eq_Ioc_union_Ioo hc hc1]
  exact setIntegral_union Ioc_disjoint_Ioo measurableSet_Ioo
    hf_inner_int hf_outer_int

/-- Conditional Korenblum reduction.

Given:
* polar integrability of `‖f‖²` and `‖g‖²` on the polar box of the unit disk
  (the hypotheses needed to invoke `bergmanNormSq_radial_polar`),
* radial-form integrability of `circleMeanSq · r` on each half for both
  functions,
* slice-integrability hypotheses for `f` and `g` on the outer half,
* the inner-half radial dominance hypothesis
  `∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`,
* the outer-half pointwise dominance hypothesis
  `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖`,

the conclusion `bergmanNormSq f ≤ bergmanNormSq g` follows.

The proof composes the two halves via `radialIntegral_split`. The inner
half closes via `setIntegral_mono_on` against `h_inner`. The outer half
closes via `circleMeanSq_le_of_outerAnnulus_dom` plus
`setIntegral_mono_on` on `Ioo c 1`. The genuinely-hard inner-half
analytical content is taken as a hypothesis; this lemma is the canonical
*conditional* form of the Korenblum implication. -/
theorem validKorenblum_of_innerCircleMean_dom
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
    (hf_circle : ∀ r ∈ Set.Ioo c 1,
        IntegrableOn
          (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (Set.Ioo (-Real.pi) Real.pi) volume)
    (hg_circle : ∀ r ∈ Set.Ioo c 1,
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
  · -- Inner half: pointwise dominance from h_inner.
    refine setIntegral_mono_on hf_inner_int hg_inner_int measurableSet_Ioc ?_
    intro r hr
    have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt hr.1
    exact mul_le_mul_of_nonneg_right (h_inner r hr) hr_nonneg
  · -- Outer half: circle-mean comparison from outerAnnulus dominance.
    refine setIntegral_mono_on hf_outer_int hg_outer_int measurableSet_Ioo ?_
    intro r hr
    have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt (lt_trans hc hr.1)
    have hcm : circleMeanSq f r ≤ circleMeanSq g r :=
      circleMeanSq_le_of_outerAnnulus_dom f g c (le_of_lt hc) h_outer hr
        (hf_circle r hr) (hg_circle r hr)
    exact mul_le_mul_of_nonneg_right hcm hr_nonneg

end ProofRefinement.Korenblum
