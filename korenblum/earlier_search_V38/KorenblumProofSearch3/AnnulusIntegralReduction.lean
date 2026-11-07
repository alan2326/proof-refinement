import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace KorenblumProofSearch3

namespace AnnulusIntegralReduction

/--
The radial annulus density corresponding to Wang's normalized boundary gap
`circleGap(ρ) = (1 / (2π)) ∫ (|g(ρe^{iθ})|^2 - |f(ρe^{iθ})|^2) dθ`.

After multiplying by the polar Jacobian `2ρ`, integrating this density over a
radial interval recovers the corresponding annulus contribution.
-/
def annulusDensity (circleGap : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  2 * ρ * circleGap ρ

/--
The radial annulus contribution over `[a, b]`.
-/
def annulusSlice (circleGap : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ ρ in a..b, annulusDensity circleGap ρ

theorem annulusSlice_nonneg
    {circleGap : ℝ → ℝ}
    {a b : ℝ}
    (hab : a ≤ b)
    (hNonneg : ∀ ρ ∈ Set.Icc a b, 0 ≤ annulusDensity circleGap ρ) :
    0 ≤ annulusSlice circleGap a b := by
  unfold annulusSlice
  exact intervalIntegral.integral_nonneg hab hNonneg

theorem annulusSlice_nonneg_of_ae
    {circleGap : ℝ → ℝ}
    {a b : ℝ}
    (hab : a ≤ b)
    (hNonneg : ∀ᵐ ρ ∂volume.restrict (Set.Icc a b), 0 ≤ annulusDensity circleGap ρ) :
    0 ≤ annulusSlice circleGap a b := by
  unfold annulusSlice
  exact intervalIntegral.integral_nonneg_of_ae_restrict hab hNonneg

theorem annulusSlice_add_adjacent
    {circleGap : ℝ → ℝ}
    {a b c : ℝ}
    (hIntAB : IntervalIntegrable (annulusDensity circleGap) volume a b)
    (hIntBC : IntervalIntegrable (annulusDensity circleGap) volume b c) :
    annulusSlice circleGap a b + annulusSlice circleGap b c =
      annulusSlice circleGap a c := by
  unfold annulusSlice
  simpa using intervalIntegral.integral_add_adjacent_intervals hIntAB hIntBC

/--
If `mass` is a certified lower bound for a radial integrand on `[a, b]`, and
that integrand yields a pointwise annulus-density bound after multiplying by the
inner excess, then `mass * innerExcess` is bounded by the annulus slice.

This is the generic step needed to turn a certified box lower bound for a new
branch-1 scalar kernel into an actual annulus inequality.
-/
theorem mass_mul_le_annulusSlice_of_integral_bound
    {modeIntegrand circleGap : ℝ → ℝ}
    {a b mass innerExcess : ℝ}
    (hab : a ≤ b)
    (hMassNonneg : 0 ≤ mass)
    (hMass :
      mass ≤ ∫ ρ in a..b, modeIntegrand ρ)
    (hModeInt : IntervalIntegrable modeIntegrand volume a b)
    (hAnnInt : IntervalIntegrable (annulusDensity circleGap) volume a b)
    (hPointwise :
      ∀ ρ ∈ Set.Icc a b,
        modeIntegrand ρ * innerExcess ≤ annulusDensity circleGap ρ)
    (hAnnNonneg :
      ∀ ρ ∈ Set.Icc a b, 0 ≤ annulusDensity circleGap ρ) :
    mass * innerExcess ≤ annulusSlice circleGap a b := by
  by_cases hInner : 0 ≤ innerExcess
  · have hScaledMass :
        mass * innerExcess ≤
          (∫ ρ in a..b, modeIntegrand ρ) * innerExcess := by
      exact mul_le_mul_of_nonneg_right hMass hInner
    have hModeMulInt :
        IntervalIntegrable (fun ρ => modeIntegrand ρ * innerExcess) volume a b := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hModeInt.mul_const innerExcess
    have hPointInt :
        ∫ ρ in a..b, modeIntegrand ρ * innerExcess ≤
          ∫ ρ in a..b, annulusDensity circleGap ρ := by
      exact intervalIntegral.integral_mono_on hab hModeMulInt hAnnInt hPointwise
    calc
      mass * innerExcess
          ≤ (∫ ρ in a..b, modeIntegrand ρ) * innerExcess := hScaledMass
      _ = ∫ ρ in a..b, modeIntegrand ρ * innerExcess := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (intervalIntegral.integral_mul_const (fun ρ => modeIntegrand ρ) innerExcess)
      _ ≤ ∫ ρ in a..b, annulusDensity circleGap ρ := hPointInt
      _ = annulusSlice circleGap a b := by
        rfl
  · have hInnerNonpos : innerExcess ≤ 0 := le_of_lt (lt_of_not_ge hInner)
    have hMassMulNonpos : mass * innerExcess ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hMassNonneg hInnerNonpos
    have hSliceNonneg : 0 ≤ annulusSlice circleGap a b :=
      annulusSlice_nonneg hab hAnnNonneg
    exact le_trans hMassMulNonpos hSliceNonneg

theorem mass_mul_le_annulusSlice_of_integral_bound_ae
    {modeIntegrand circleGap : ℝ → ℝ}
    {a b mass innerExcess : ℝ}
    (hab : a ≤ b)
    (hMassNonneg : 0 ≤ mass)
    (hMass :
      mass ≤ ∫ ρ in a..b, modeIntegrand ρ)
    (hModeInt : IntervalIntegrable modeIntegrand volume a b)
    (hAnnInt : IntervalIntegrable (annulusDensity circleGap) volume a b)
    (hPointwise :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc a b),
        modeIntegrand ρ * innerExcess ≤ annulusDensity circleGap ρ)
    (hAnnNonneg :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc a b), 0 ≤ annulusDensity circleGap ρ) :
    mass * innerExcess ≤ annulusSlice circleGap a b := by
  by_cases hInner : 0 ≤ innerExcess
  · have hScaledMass :
        mass * innerExcess ≤
          (∫ ρ in a..b, modeIntegrand ρ) * innerExcess := by
      exact mul_le_mul_of_nonneg_right hMass hInner
    have hModeMulInt :
        IntervalIntegrable (fun ρ => modeIntegrand ρ * innerExcess) volume a b := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hModeInt.mul_const innerExcess
    have hPointInt :
        ∫ ρ in a..b, modeIntegrand ρ * innerExcess ≤
          ∫ ρ in a..b, annulusDensity circleGap ρ := by
      exact intervalIntegral.integral_mono_ae_restrict hab hModeMulInt hAnnInt hPointwise
    calc
      mass * innerExcess
          ≤ (∫ ρ in a..b, modeIntegrand ρ) * innerExcess := hScaledMass
      _ = ∫ ρ in a..b, modeIntegrand ρ * innerExcess := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (intervalIntegral.integral_mul_const (fun ρ => modeIntegrand ρ) innerExcess)
      _ ≤ ∫ ρ in a..b, annulusDensity circleGap ρ := hPointInt
      _ = annulusSlice circleGap a b := by
        rfl
  · have hInnerNonpos : innerExcess ≤ 0 := le_of_lt (lt_of_not_ge hInner)
    have hMassMulNonpos : mass * innerExcess ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hMassNonneg hInnerNonpos
    have hSliceNonneg : 0 ≤ annulusSlice circleGap a b :=
      annulusSlice_nonneg_of_ae hab hAnnNonneg
    exact le_trans hMassMulNonpos hSliceNonneg

/--
Finite bookkeeping lemma: if a family of certified window masses sums to at
least `1`, and each window mass times `innerExcess` is bounded by its annulus
contribution, then the full annulus contribution dominates `innerExcess`.
-/
theorem innerExcess_le_of_window_bounds
    {ι : Type}
    (s : Finset ι)
    (mass annulusTerm : ι → ℝ)
    {innerExcess annulusExcess : ℝ}
    (hWindow :
      ∀ i ∈ s, mass i * innerExcess ≤ annulusTerm i)
    (hTotal : (1 : ℝ) ≤ Finset.sum s (fun i => mass i))
    (hAnnulus :
      Finset.sum s (fun i => annulusTerm i) ≤ annulusExcess)
    (hAnnulusNonneg :
      ∀ i ∈ s, 0 ≤ annulusTerm i) :
    innerExcess ≤ annulusExcess := by
  by_cases hInner : 0 ≤ innerExcess
  · have hScaled :
        innerExcess ≤ Finset.sum s (fun i => mass i) * innerExcess := by
      simpa using mul_le_mul_of_nonneg_right hTotal hInner
    have hWindowSum :
        Finset.sum s (fun i => mass i) * innerExcess ≤
          Finset.sum s (fun i => annulusTerm i) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i hi => hWindow i hi)
    exact le_trans hScaled (le_trans hWindowSum hAnnulus)
  · have hInnerNonpos : innerExcess ≤ 0 := le_of_lt (lt_of_not_ge hInner)
    have hAnnulusSumNonneg : 0 ≤ Finset.sum s (fun i => annulusTerm i) := by
      exact Finset.sum_nonneg (fun i hi => hAnnulusNonneg i hi)
    have hAnnulusExcessNonneg : 0 ≤ annulusExcess := by
      exact le_trans hAnnulusSumNonneg hAnnulus
    exact le_trans hInnerNonpos hAnnulusExcessNonneg

end AnnulusIntegralReduction

end KorenblumProofSearch3
