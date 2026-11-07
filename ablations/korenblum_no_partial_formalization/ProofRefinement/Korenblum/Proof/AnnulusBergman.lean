import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract

/-!
# Annulus decomposition of `bergmanNormSq` and outer-annulus monotonicity

This file derives, against Mathlib only, two scaffolding lemmas for the
function-level Korenblum maximum principle in the no-partial-formalization
arm:

* `bergmanNormSq_split` — splits the Bergman A² seminorm at radius `c` as
  the sum of an inner-disk integral and an outer-annulus integral.
* `outerAnnulus_norm_sq_mono` — pointwise `‖f‖ ≤ ‖g‖` on the outer annulus
  `c < ‖z‖ < 1` implies the corresponding outer-annulus integrals are
  ordered.

The two lemmas are independent of `Proof/PolarBergman.lean`. Together they
isolate the easy half of any Korenblum-style comparison: the outer annulus
piece is dominated by direct integral monotonicity, leaving the inner disk
as the genuine Bergman-side obstruction for follow-up sprints.
-/

open MeasureTheory Set

noncomputable section

namespace ProofRefinement.Korenblum

/-- Open outer annulus `c < ‖z‖ < 1`. -/
def outerAnnulus (c : ℝ) : Set ℂ := {z : ℂ | c < ‖z‖ ∧ ‖z‖ < 1}

/-- Inner closed disk inside the unit disk, `‖z‖ ≤ c` and `‖z‖ < 1`. -/
def innerDisk (c : ℝ) : Set ℂ := {z : ℂ | ‖z‖ ≤ c ∧ ‖z‖ < 1}

/-- The outer annulus is a measurable set. -/
theorem measurableSet_outerAnnulus (c : ℝ) :
    MeasurableSet (outerAnnulus c) := by
  unfold outerAnnulus
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt measurable_const continuous_norm.measurable
  · exact measurableSet_lt continuous_norm.measurable measurable_const

/-- The inner disk is a measurable set. -/
theorem measurableSet_innerDisk (c : ℝ) :
    MeasurableSet (innerDisk c) := by
  unfold innerDisk
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurableSet_lt continuous_norm.measurable measurable_const

/-- The unit disk decomposes as the disjoint union of the inner disk and
the outer annulus. -/
theorem unitDisk_eq_innerDisk_union_outerAnnulus (c : ℝ) :
    UnitDisk = innerDisk c ∪ outerAnnulus c := by
  ext z
  unfold UnitDisk innerDisk outerAnnulus
  rw [Metric.mem_ball, dist_zero_right]
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro hz
    by_cases h : ‖z‖ ≤ c
    · exact Or.inl ⟨h, hz⟩
    · push_neg at h
      exact Or.inr ⟨h, hz⟩
  · rintro (⟨_, hz⟩ | ⟨_, hz⟩) <;> exact hz

/-- The inner disk and outer annulus are disjoint. -/
theorem innerDisk_disjoint_outerAnnulus (c : ℝ) :
    Disjoint (innerDisk c) (outerAnnulus c) := by
  rw [Set.disjoint_left]
  intro z hz_in hz_out
  unfold innerDisk at hz_in
  unfold outerAnnulus at hz_out
  exact (not_lt.mpr hz_in.1) hz_out.1

/-- Splitting the Bergman A² seminorm at radius `c`: the integral over the
unit disk equals the inner-disk integral plus the outer-annulus integral.

The hypothesis `hf` is the natural integrability of `‖f‖²` on the unit
disk, which is already part of the Korenblum contract. -/
theorem bergmanNormSq_split (f : ℂ → ℂ) (c : ℝ)
    (hf : Integrable (fun z => ‖f z‖ ^ 2)
            ((volume : Measure ℂ).restrict UnitDisk)) :
    bergmanNormSq f
      = (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
        + (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ)) := by
  have hUD : UnitDisk = innerDisk c ∪ outerAnnulus c :=
    unitDisk_eq_innerDisk_union_outerAnnulus c
  have hdisj : Disjoint (innerDisk c) (outerAnnulus c) :=
    innerDisk_disjoint_outerAnnulus c
  have hmeas : MeasurableSet (outerAnnulus c) := measurableSet_outerAnnulus c
  unfold bergmanNormSq
  -- Replace the integration domain `UnitDisk` with the union form.
  rw [hUD]
  -- Use additivity over disjoint union. We need integrability of `‖f‖²` on
  -- `innerDisk c ∪ outerAnnulus c`. Using `hf` together with the rewrite
  -- of `UnitDisk` we obtain it directly.
  have hf' : IntegrableOn (fun z => ‖f z‖ ^ 2)
                (innerDisk c ∪ outerAnnulus c) volume := by
    have hrestr : (volume : Measure ℂ).restrict UnitDisk
            = (volume : Measure ℂ).restrict (innerDisk c ∪ outerAnnulus c) := by
      rw [hUD]
    rw [IntegrableOn, ← hrestr]
    exact hf
  obtain ⟨hf_inner, hf_outer⟩ := integrableOn_union.mp hf'
  exact setIntegral_union hdisj hmeas hf_inner hf_outer

/-- Outer-annulus monotonicity: pointwise `‖f‖ ≤ ‖g‖` on the open outer
annulus `c < ‖z‖ < 1` implies the outer-annulus integrals of the squared
norms are ordered. -/
theorem outerAnnulus_norm_sq_mono
    (f g : ℂ → ℂ) (c : ℝ)
    (hf : IntegrableOn (fun z => ‖f z‖ ^ 2) (outerAnnulus c) volume)
    (hg : IntegrableOn (fun z => ‖g z‖ ^ 2) (outerAnnulus c) volume)
    (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      ≤ (∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ)) := by
  refine setIntegral_mono_on hf hg (measurableSet_outerAnnulus c) ?_
  intro z hz
  have hfz : (0 : ℝ) ≤ ‖f z‖ := norm_nonneg _
  have hgz : (0 : ℝ) ≤ ‖g z‖ := norm_nonneg _
  have hle : ‖f z‖ ≤ ‖g z‖ := h z hz
  exact pow_le_pow_left₀ hfz hle 2

end ProofRefinement.Korenblum
