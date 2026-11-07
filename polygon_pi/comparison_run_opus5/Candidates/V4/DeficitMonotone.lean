import ProofRefinement.PolygonPi.Proof.Main

/-!
# Monotonicity of the scaled polygon deficit

Derived theorems for candidate `V4`: copied verbatim from `V3`, namespace
renamed. Theorems and lemmas only — no `axiom`,
no `sorry`, no oracle.

Write `D n := 4 ^ n * (π - polygonLower n)`. The scored contract's lower
conjunct is exactly `lambda < D n` for every `n`, so the binding constraint sits
at whichever `n` minimizes `D`. This file shows `D` is monotone non-decreasing,
hence the binding constraint is at `n = 0` and is *attained*: the exact ceiling
for `lambda` is `π - polygonLower 0 = π - 2√2`.

The analytic content is a single one-variable inequality. With
`y := π / 2 ^ (n + 3)` we have `polygonLower (n+1) = 2 ^ (n+3) * sin y` and, by
the double-angle formula, `polygonLower n = 2 ^ (n+3) * sin y * cos y`, while
`3 * π = 3 * 2 ^ (n+3) * y`. So `D n ≤ D (n+1)` is equivalent to

    sin y * (4 - cos y) ≤ 3 * y.

Setting `φ y := 3 * y - sin y * (4 - cos y)` we get `φ 0 = 0` and

    φ' y = 3 - (cos y * (4 - cos y) + sin y * sin y) = 2 * (cos y - 1) ^ 2 ≥ 0,

an exact square. So `φ` is monotone on all of `ℝ` and `φ y ≥ 0` for `y ≥ 0`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V4

open PolygonCore

/-! ### The one-variable inequality -/

/-- The derivative of `φ y = 3 * y - sin y * (4 - cos y)` is an exact square,
hence non-negative everywhere. -/
lemma phiDeriv_eq_sq (y : ℝ) :
    3 - (Real.cos y * (4 - Real.cos y) + Real.sin y * Real.sin y)
      = 2 * (Real.cos y - 1) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq y]

lemma phiDeriv_nonneg (y : ℝ) :
    0 ≤ 3 - (Real.cos y * (4 - Real.cos y) + Real.sin y * Real.sin y) := by
  rw [phiDeriv_eq_sq]; positivity

lemma hasDerivAt_phi (y : ℝ) :
    HasDerivAt (fun t : ℝ => 3 * t - Real.sin t * (4 - Real.cos t))
      (3 - (Real.cos y * (4 - Real.cos y) + Real.sin y * Real.sin y)) y := by
  have hlin : HasDerivAt (fun t : ℝ => 3 * t) (3 : ℝ) y := by
    simpa using (hasDerivAt_id y).const_mul (3 : ℝ)
  have hsin : HasDerivAt Real.sin (Real.cos y) y := Real.hasDerivAt_sin y
  have hcos : HasDerivAt (fun t : ℝ => 4 - Real.cos t) (Real.sin y) y := by
    simpa using (Real.hasDerivAt_cos y).const_sub (4 : ℝ)
  exact hlin.sub (hsin.mul hcos)

lemma phi_monotone :
    Monotone (fun t : ℝ => 3 * t - Real.sin t * (4 - Real.cos t)) :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_phi (fun y => phiDeriv_nonneg y)

/-- **The one-variable inequality.** For every `y ≥ 0`,
`sin y * (4 - cos y) ≤ 3 * y`. In particular it holds on `Set.Ioc 0 (π / 8)`,
which contains every `π / 2 ^ (n + 3)`. -/
theorem sin_mul_four_sub_cos_le (y : ℝ) (hy : 0 ≤ y) :
    Real.sin y * (4 - Real.cos y) ≤ 3 * y := by
  have h := phi_monotone hy
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, zero_mul, sub_zero] at h
  linarith

/-- The same inequality, packaged on the interval the deficit argument uses. -/
theorem sin_mul_four_sub_cos_le_on_Ioc (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) (Real.pi / 8)) :
    Real.sin y * (4 - Real.cos y) ≤ 3 * y :=
  sin_mul_four_sub_cos_le y hy.1.le

/-! ### The one-step deficit inequality -/

/-- **One doubling step never decreases the scaled deficit.** -/
theorem deficit_step (n : ℕ) :
    4 ^ n * (Real.pi - polygonLower n) ≤ 4 ^ (n + 1) * (Real.pi - polygonLower (n + 1)) := by
  have hP : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have hy0 : (0 : ℝ) < Real.pi / 2 ^ (n + 3) := by positivity
  set y : ℝ := Real.pi / 2 ^ (n + 3) with hy
  -- `polygonLower (n+1) = 2 ^ (n+3) * sin y`
  have hL1 : polygonLower (n + 1) = 2 ^ (n + 3) * Real.sin y := by
    rw [polygonLower_eq_mul_sin, hy]
  -- `polygonLower n = 2 ^ (n+3) * (sin y * cos y)` by the double-angle formula
  have h2y : Real.pi / 2 ^ (n + 2) = 2 * y := by
    rw [hy, show ((2 : ℝ) ^ (n + 3)) = 2 * 2 ^ (n + 2) by ring]
    have : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    field_simp
  have hL0 : polygonLower n = 2 ^ (n + 3) * (Real.sin y * Real.cos y) := by
    rw [polygonLower_eq_mul_sin, h2y, Real.sin_two_mul]
    ring
  -- the scaled one-variable inequality
  have hkey : 4 * (2 ^ (n + 3) * Real.sin y) - 2 ^ (n + 3) * (Real.sin y * Real.cos y)
      ≤ 3 * Real.pi := by
    calc 4 * (2 ^ (n + 3) * Real.sin y) - 2 ^ (n + 3) * (Real.sin y * Real.cos y)
        = 2 ^ (n + 3) * (Real.sin y * (4 - Real.cos y)) := by ring
      _ ≤ 2 ^ (n + 3) * (3 * y) :=
          mul_le_mul_of_nonneg_left (sin_mul_four_sub_cos_le y hy0.le) hP.le
      _ = 3 * Real.pi := by rw [hy]; field_simp
  -- scale by `4 ^ n` and rearrange
  have hscaled := mul_le_mul_of_nonneg_left hkey h4n.le
  rw [hL0, hL1, show ((4 : ℝ) ^ (n + 1)) = 4 * 4 ^ n by ring]
  nlinarith [hscaled]

/-! ### The uniform bridge -/

/-- **The scaled deficit is bounded below by its value at depth `0`, uniformly
in `n`.** Proved by induction from `deficit_step`, not by a per-`n` estimate. -/
theorem deficit_ge_zero_deficit (n : ℕ) :
    Real.pi - polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n) := by
  induction n with
  | zero => simp
  | succ k ih => exact ih.trans (deficit_step k)

end ProofRefinement.PolygonPi.Candidates.V4
