/-
# Polygon-π trusted surface: the inscribed polygon is shorter than the circle

TRUSTED SURFACE — read-only to every agent in the refinement loop.

`polygonLower n < π` is not part of the optimization: it is the fact that makes
the problem statement meaningful, and every candidate gets it for free. What is
*not* free — and is therefore absent from this file — is any quantitative
statement about how much shorter the polygon is. See the harness plan §5.1.
-/
import PolygonCore.Polygon

open scoped Real

namespace PolygonCore

/-- The inscribed polygon has strictly positive half-perimeter. -/
theorem polygonLower_pos (n : ℕ) : 0 < polygonLower n := by
  rw [polygonLower_eq_mul_sin]
  have hpow : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  refine mul_pos hpow (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
  exact div_lt_self Real.pi_pos (one_lt_pow₀ one_lt_two (Nat.succ_ne_zero _))

/-- The inscribed polygon's half-perimeter is strictly below `π`. Uniform in
`n`. -/
theorem polygonLower_lt_pi (n : ℕ) : polygonLower n < Real.pi := by
  have hpow : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
  calc polygonLower n
      = 2 ^ (n + 2) * Real.sin (Real.pi / 2 ^ (n + 2)) := polygonLower_eq_mul_sin n
    _ < 2 ^ (n + 2) * (Real.pi / 2 ^ (n + 2)) :=
        mul_lt_mul_of_pos_left (Real.sin_lt hx) hpow
    _ = Real.pi := by field_simp

end PolygonCore
