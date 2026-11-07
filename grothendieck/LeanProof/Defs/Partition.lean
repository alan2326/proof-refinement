/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Defs.HermitePoly
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# The partition function f_η

We define `f_η : ℝ × ℝ → ℝ` as in equation (40) of Braverman et al. (2011):
  f_η(x₁, x₂) = if x₂ > η · h₅(x₁) then 1 else -1

This is the planar partition that, when composed with 2D Gaussian projections,
gives the improved rounding scheme.
-/

open MeasureTheory

noncomputable section

namespace Braverman

/-- The partition function `f_η` from equation (40).
    `f_η(x₁, x₂) = 1` if `x₂ > η · h₅(x₁)`, and `-1` otherwise. -/
def f_eta (η : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.2 > η * h5 p.1 then 1 else -1

theorem f_eta_bounded (η : ℝ) (p : ℝ × ℝ) : |f_eta η p| = 1 := by
  unfold f_eta
  split <;> norm_num

theorem f_eta_range (η : ℝ) (p : ℝ × ℝ) : f_eta η p = 1 ∨ f_eta η p = -1 := by
  unfold f_eta
  split
  · left; rfl
  · right; rfl

/-- At η = 0, the partition reduces to `sign(x₂)`. -/
theorem f_eta_zero (p : ℝ × ℝ) : f_eta 0 p = if p.2 > 0 then 1 else -1 := by
  simp [f_eta, h5]

@[measurability]
theorem h5_measurable' : Measurable (fun p : ℝ × ℝ => h5 p.1) :=
  h5_measurable.comp measurable_fst

theorem f_eta_measurable (η : ℝ) : Measurable (f_eta η) := by
  unfold f_eta
  apply Measurable.ite
  · exact measurableSet_lt (measurable_const.mul h5_measurable') measurable_snd
  · exact measurable_const
  · exact measurable_const

end Braverman
