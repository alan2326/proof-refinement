import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CleanConditional

/-!
# Contract-shaped reduction: `ValidKorenblumBound c` from universal inner-half
radial dominance

This file lifts sprint 013's per-pair clean conditional Korenblum reduction
`validKorenblum_of_inner_outer_dom_of_analyticOn` to the contract-shaped
universal form.

The theorem `validKorenblumBound_of_inner_radial_dominance` takes the
universal inner-half radial dominance hypothesis (quantified over all
`(f, g)`) plus `0 < c` and `c < 1`, and produces the function-level
`ValidKorenblumBound c`. The proof is a thin composition: `intro` the
contract hypotheses, instantiate the universal inner hypothesis, bridge
the contract-shape outer-annulus hypothesis
`∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖` to the
`outerAnnulus`-shape `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖`, then apply
sprint 013's clean conditional reduction.

This is the final Lean-side composition layer above sprint 013's clean
conditional. Once it is pinned, a future trust-reduction sprint can replace
the seed axiom `hKorenblum_published_3554` with a strictly smaller leaf
`hWang_inner_radial_dominance_3554` that asserts only the inner-half radial
dominance — Wang's intermediate conclusion — and use this theorem to derive
`ValidKorenblumBound (3554/10000)` from that smaller leaf.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- Membership bridge between `UnitDisk` and `‖z‖ < 1`. -/
private theorem mem_unitDisk_iff_norm_lt_one {z : ℂ} :
    z ∈ UnitDisk ↔ ‖z‖ < 1 := by
  unfold UnitDisk
  rw [Metric.mem_ball, dist_zero_right]

/-- **Contract-shaped reduction.**

If for every pair of analytic, A²-integrable functions `(f, g)` on the unit
disk with `‖f‖ ≤ ‖g‖` on the outer annulus `c < ‖z‖ < 1`, the inner-half
radial dominance `circleMeanSq f r ≤ circleMeanSq g r` holds for every
`r ∈ Ioc 0 c`, then `ValidKorenblumBound c`.

This is a thin composition above sprint 013's
`validKorenblum_of_inner_outer_dom_of_analyticOn`. The only non-trivial
step is the bridge between the contract-shape outer-annulus hypothesis
`∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖` and the sprint-013 shape
`∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖`, which is one `simp [outerAnnulus]`
plus the `UnitDisk ↔ ‖z‖ < 1` bridge. -/
theorem validKorenblumBound_of_inner_radial_dominance
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_inner_universal : ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      ∀ r ∈ Set.Ioc (0 : ℝ) c, circleMeanSq f r ≤ circleMeanSq g r) :
    ValidKorenblumBound c := by
  refine ⟨hc, hc1, ?_⟩
  intro f g hf_an hg_an hf_int hg_int h_outer_contract
  -- Inner-half radial dominance from the universal hypothesis.
  have h_inner :
      ∀ r ∈ Set.Ioc (0 : ℝ) c, circleMeanSq f r ≤ circleMeanSq g r :=
    h_inner_universal f g hf_an hg_an hf_int hg_int h_outer_contract
  -- Bridge the contract-shape outer hypothesis to the `outerAnnulus` shape.
  have h_outer_clean : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖ := by
    intro z hz
    simp only [outerAnnulus, Set.mem_setOf_eq] at hz
    exact h_outer_contract z (mem_unitDisk_iff_norm_lt_one.mpr hz.2) hz.1
  -- Apply sprint 013's clean conditional reduction.
  exact validKorenblum_of_inner_outer_dom_of_analyticOn
    f g c hc hc1 hf_an hg_an hf_int hg_int h_inner h_outer_clean

end ProofRefinement.Korenblum
