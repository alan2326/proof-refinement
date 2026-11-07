/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The fifth Hermite polynomial h₅

We define the specific Hermite polynomial `h₅` used in Braverman et al. (2011),
normalized so that `∫ h₅² exp(-x²) dx = 1`. We only need `h₅` explicitly, not the
general Hermite polynomial family.

The paper's normalization gives:
  h₅(x) = (4x⁵ - 20x³ + 15x) / (2⁴ √(π · 15))
-/

open Real

noncomputable section

namespace Braverman

/-- The unnormalized degree-5 Hermite polynomial: `4x⁵ - 20x³ + 15x`. -/
def h5_unnorm (x : ℝ) : ℝ := 4 * x ^ 5 - 20 * x ^ 3 + 15 * x

/-- The normalization constant for h₅: `2⁴ √(π · 15) = 16 √(15π)`. -/
def h5_norm_const : ℝ := 16 * Real.sqrt (Real.pi * 15)

/-- The normalized fifth Hermite polynomial as used in the paper. -/
def h5 (x : ℝ) : ℝ := h5_unnorm x / h5_norm_const

theorem h5_unnorm_odd (x : ℝ) : h5_unnorm (-x) = -h5_unnorm x := by
  simp [h5_unnorm]
  ring

theorem h5_odd (x : ℝ) : h5 (-x) = -h5 x := by
  simp [h5, h5_unnorm_odd, neg_div]

theorem h5_continuous : Continuous h5 := by
  unfold h5 h5_unnorm
  fun_prop

theorem h5_measurable : Measurable h5 :=
  h5_continuous.measurable

end Braverman
