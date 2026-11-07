import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman

/-!
# Radial polar form of `bergmanNormSq` and its inner / outer halves

This file bridges `Proof.PolarBergman` (polar pull-back of the whole disk) to
`Proof.AnnulusBergman` (the inner-disk / outer-annulus split) by deriving the
radial polar form. We expose:

* `circleMeanSq f r` — the squared-norm circle integral at radius `r` over
  `θ ∈ Ioo (-π) π`. No `1/(2π)` normalisation; the bare integral is the
  natural quantity for the radial form of `bergmanNormSq`.
* `bergmanNormSq_radial_polar` — the headline radial form of the whole-disk
  integral: a single `r`-integral of `circleMeanSq f r * r` over `r ∈ (0,1)`.
* `outerAnnulus_norm_sq_polar` — the radial form of the outer-annulus
  integral: an `r`-integral of `circleMeanSq f r * r` over `r ∈ (c, 1)`.
* `innerDisk_norm_sq_polar` — the radial form of the inner-disk integral:
  an `r`-integral of `circleMeanSq f r * r` over `r ∈ (0, c]`.

Together the two halves span the full radial integral. Every honest route
past `c = 0.3554` factors through some monotone-mean argument on
`r ↦ circleMeanSq f r`; this file pins both the canonical definition of
the circle mean and the polar forms of the inner / outer integrals.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

variable {f : ℂ → ℂ}

/-- Squared-norm circle mean of `f` at radius `r`: the bare `θ`-integral of
`‖f (polarCoord.symm (r,θ))‖²` over `Ioo (-π) π`. -/
noncomputable def circleMeanSq (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∫ θ in Ioo (-Real.pi) Real.pi,
    ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2

/-- Radial polar form of `bergmanNormSq`.

Folds the iterated polar integral from `bergmanNormSq_polar` into a single
`r`-integral against `circleMeanSq f r * r` over `r ∈ (0,1)`. The proof is
a `setIntegral_congr_fun` reindexing the inner θ-integral as `circleMeanSq`
and pulling the radial scalar `r` outside. -/
theorem bergmanNormSq_radial_polar
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    bergmanNormSq f =
      ∫ r in Ioo (0 : ℝ) 1, circleMeanSq f r * r := by
  rw [bergmanNormSq_polar hf_polar]
  refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
  -- inner θ-integral of `‖...‖² * r` equals `circleMeanSq f r * r`
  unfold circleMeanSq
  rw [integral_mul_const]

/-- Polar form of the outer-annulus integral.

The proof mirrors `bergmanNormSq_polar` but with the outer annulus in place
of the unit disk, shrinking the radial domain from `Ioi 0` to `Ioo c 1`. -/
theorem outerAnnulus_norm_sq_polar
    (f : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ r in Ioo c 1, circleMeanSq f r * r := by
  have hOA_meas : MeasurableSet (outerAnnulus c) := measurableSet_outerAnnulus c
  -- Step 1: rewrite the set integral as an integral of the indicator.
  have step1 :
      (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
        = ∫ z, ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) :=
    (integral_indicator hOA_meas).symm
  -- Step 2: polar substitution.
  have step2 :
      (∫ z, ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2)) z
            ∂(volume : Measure ℂ))
        = ∫ p in Complex.polarCoord.target,
            p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm
      (fun z => (outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2) z)).symm
  -- Step 3: shrink the integration domain from `polarCoord.target` to
  -- `Ioo c 1 ×ˢ Ioo (-π) π`. Outside that box (within the polar target), the
  -- outer-annulus indicator vanishes.
  have hT_meas : MeasurableSet (Complex.polarCoord.target) :=
    Complex.polarCoord.open_target.measurableSet
  have h_subset :
      Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    intro p hp
    refine ⟨?_, hp.2⟩
    -- p.1 ∈ Ioo c 1, so p.1 > c ≥ 0
    exact Set.mem_Ioi.mpr (lt_of_le_of_lt hc hp.1.1)
  have h_diff_zero :
      ∀ p ∈ Complex.polarCoord.target \
              (Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi),
        p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                (Complex.polarCoord.symm p) = 0 := by
    intro p hp
    obtain ⟨hp_target, hp_not⟩ := hp
    rw [Complex.polarCoord_target] at hp_target
    obtain ⟨hr_pos, hθ⟩ := hp_target
    -- Either p.1 ∈ Ioo c 1 (then by hθ p ∈ box, contradicting hp_not), or
    -- p.1 ≤ c, or p.1 ≥ 1; in either of those, polar-symm p ∉ outerAnnulus c.
    by_cases hp1 : p.1 ∈ Ioo c 1
    · exact absurd ⟨hp1, hθ⟩ hp_not
    · -- p.1 ∉ Ioo c 1; with hr_pos : 0 < p.1, this means p.1 ≤ c ∨ p.1 ≥ 1.
      have hr_pos_real : 0 < p.1 := hr_pos
      have h_not_mem : Complex.polarCoord.symm p ∉ outerAnnulus c := by
        unfold outerAnnulus
        intro hmem
        obtain ⟨h1, h2⟩ := hmem
        rw [Complex.norm_polarCoord_symm, abs_of_pos hr_pos_real] at h1 h2
        exact hp1 ⟨h1, h2⟩
      rw [Set.indicator_of_notMem h_not_mem]
      simp
  have step3 :
      (∫ p in Complex.polarCoord.target,
          p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hT_meas h_subset
      h_diff_zero
  -- Step 4: on `Ioo c 1 ×ˢ Ioo (-π) π`, the indicator unfolds to `‖f‖²`
  -- because the polar-symm point lies in the outer annulus.
  have step4 :
      (∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by
    refine setIntegral_congr_fun
      ((measurableSet_Ioo).prod measurableSet_Ioo) ?_
    intro p hp
    obtain ⟨hr, _hθ⟩ := hp
    have hr_pos : 0 < p.1 := lt_of_le_of_lt hc hr.1
    have h_mem : Complex.polarCoord.symm p ∈ outerAnnulus c := by
      unfold outerAnnulus
      simp only [Set.mem_setOf_eq, Complex.norm_polarCoord_symm,
                 abs_of_pos hr_pos]
      exact ⟨hr.1, hr.2⟩
    change p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p)
        = p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2
    rw [Set.indicator_of_mem h_mem, smul_eq_mul]
  -- Step 5: Fubini.
  have step5 :
      (∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        = ∫ r in Ioo c 1,
            ∫ θ in Ioo (-Real.pi) Real.pi,
              (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 :=
    setIntegral_prod _ hf_polar
  -- Step 6: refold inner θ-integral as `circleMeanSq f r * r`.
  have step6 :
      (∫ r in Ioo c 1,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ r in Ioo c 1, circleMeanSq f r * r := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
    change (∫ θ in Ioo (-Real.pi) Real.pi,
              r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = circleMeanSq f r * r
    unfold circleMeanSq
    rw [integral_const_mul, mul_comm]
  calc (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ z, ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) := step1
    _ = ∫ p in Complex.polarCoord.target,
            p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step2
    _ = ∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • ((outerAnnulus c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step3
    _ = ∫ p in Ioo c 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := step4
    _ = ∫ r in Ioo c 1,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 := step5
    _ = ∫ r in Ioo c 1, circleMeanSq f r * r := step6

/-- Polar form of the inner-disk integral.

The proof mirrors `outerAnnulus_norm_sq_polar` but with the inner disk in
place of the outer annulus. The radial domain is `Ioc 0 c`, which captures
exactly `‖z‖ ≤ c` minus the origin (a measure-zero point). -/
theorem innerDisk_norm_sq_polar
    (f : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ r in Ioc (0 : ℝ) c, circleMeanSq f r * r := by
  have hID_meas : MeasurableSet (innerDisk c) := measurableSet_innerDisk c
  -- Step 1: indicator rewrite.
  have step1 :
      (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
        = ∫ z, ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) :=
    (integral_indicator hID_meas).symm
  -- Step 2: polar substitution.
  have step2 :
      (∫ z, ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2)) z
            ∂(volume : Measure ℂ))
        = ∫ p in Complex.polarCoord.target,
            p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm
      (fun z => (innerDisk c).indicator (fun z => ‖f z‖ ^ 2) z)).symm
  -- Step 3: shrink to `Ioc 0 c ×ˢ Ioo (-π) π`. Outside, the inner-disk
  -- indicator on the polar-symm point vanishes (because either r > c or
  -- r ≥ 1, and r ≥ 1 already implies r > c).
  have hT_meas : MeasurableSet (Complex.polarCoord.target) :=
    Complex.polarCoord.open_target.measurableSet
  have h_subset :
      Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi ⊆
        Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    intro p hp
    exact ⟨Set.mem_Ioi.mpr hp.1.1, hp.2⟩
  have h_diff_zero :
      ∀ p ∈ Complex.polarCoord.target \
              (Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi),
        p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                (Complex.polarCoord.symm p) = 0 := by
    intro p hp
    obtain ⟨hp_target, hp_not⟩ := hp
    rw [Complex.polarCoord_target] at hp_target
    obtain ⟨hr_pos, hθ⟩ := hp_target
    have hr_pos_real : 0 < p.1 := hr_pos
    by_cases hp1 : p.1 ∈ Ioc (0 : ℝ) c
    · exact absurd ⟨hp1, hθ⟩ hp_not
    · -- p.1 > 0 and p.1 ∉ Ioc 0 c, so p.1 > c. Hence symm p has norm > c,
      -- so symm p ∉ innerDisk c.
      have hp1' : c < p.1 := by
        rcases lt_or_ge c p.1 with h | h
        · exact h
        · exact absurd ⟨hr_pos_real, h⟩ hp1
      have h_not_mem : Complex.polarCoord.symm p ∉ innerDisk c := by
        unfold innerDisk
        intro hmem
        obtain ⟨h1, _⟩ := hmem
        rw [Complex.norm_polarCoord_symm, abs_of_pos hr_pos_real] at h1
        exact (not_le.mpr hp1') h1
      rw [Set.indicator_of_notMem h_not_mem]
      simp
  have step3 :
      (∫ p in Complex.polarCoord.target,
          p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hT_meas h_subset
      h_diff_zero
  -- Step 4: on `Ioc 0 c ×ˢ Ioo (-π) π`, polar-symm p ∈ innerDisk c so the
  -- indicator unfolds.
  have step4 :
      (∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by
    refine setIntegral_congr_fun
      ((measurableSet_Ioc).prod measurableSet_Ioo) ?_
    intro p hp
    obtain ⟨hr, _hθ⟩ := hp
    have hr_pos : 0 < p.1 := hr.1
    have hr_le_c : p.1 ≤ c := hr.2
    have h_mem : Complex.polarCoord.symm p ∈ innerDisk c := by
      unfold innerDisk
      simp only [Set.mem_setOf_eq, Complex.norm_polarCoord_symm,
                 abs_of_pos hr_pos]
      exact ⟨hr_le_c, lt_of_le_of_lt hr_le_c hc1⟩
    change p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p)
        = p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2
    rw [Set.indicator_of_mem h_mem, smul_eq_mul]
  -- Step 5: Fubini.
  have step5 :
      (∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        = ∫ r in Ioc (0 : ℝ) c,
            ∫ θ in Ioo (-Real.pi) Real.pi,
              (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 :=
    setIntegral_prod _ hf_polar
  -- Step 6: refold inner θ-integral as `circleMeanSq f r * r`.
  have step6 :
      (∫ r in Ioc (0 : ℝ) c,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ r in Ioc (0 : ℝ) c, circleMeanSq f r * r := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)
    change (∫ θ in Ioo (-Real.pi) Real.pi,
              r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = circleMeanSq f r * r
    unfold circleMeanSq
    rw [integral_const_mul, mul_comm]
  calc (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ z, ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) := step1
    _ = ∫ p in Complex.polarCoord.target,
            p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step2
    _ = ∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • ((innerDisk c).indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step3
    _ = ∫ p in Ioc (0 : ℝ) c ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := step4
    _ = ∫ r in Ioc (0 : ℝ) c,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 := step5
    _ = ∫ r in Ioc (0 : ℝ) c, circleMeanSq f r * r := step6

end ProofRefinement.Korenblum
