/-
# Polygon-π trusted surface: the inscribed-polygon perimeter

TRUSTED SURFACE — read-only to every agent in the refinement loop.

This file fixes the problem statement and nothing else. It contains no analytic
estimate of any kind: in particular there is deliberately **no** cubic bound on
`x - sin x` and no upper bound on `π` here, because those are exactly the levers
the refinement loop is meant to discover and sharpen. See the harness plan §5.1.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped Real

namespace PolygonCore

/-- Half the perimeter of the regular polygon with `2 ^ (n + 2)` sides inscribed
in the unit circle, written in Mathlib's trigonometry-free nested-radical form.

`Real.sqrtTwoAddSeries 0 n` is the nested radical `√(2 + √(2 + ⋯))` with `n`
square roots, equal to `2 * cos (π / 2 ^ (n + 1))`. -/
noncomputable def polygonLower (n : ℕ) : ℝ :=
  2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)

/-- The benchmark depth is frozen, so no score improvement can come from simply
adding sides. Note `n` is the **doubling depth**, not the side count. -/
def benchmarkDepth : ℕ := 10

/-- Side count of the polygon at the benchmark depth: `2 ^ 12 = 4096`.
Stated explicitly so the artifact is unambiguous that depth 10 means a
4096-gon, not a 10-gon. -/
def benchmarkSides : ℕ := 2 ^ (benchmarkDepth + 2)

theorem benchmarkSides_eq_4096 : benchmarkSides = 4096 := by
  norm_num [benchmarkSides, benchmarkDepth]

/-- The perimeter identity: the nested-radical form really is `N * sin (π / N)`
for `N = 2 ^ (n + 2)` sides. -/
theorem polygonLower_eq_mul_sin (n : ℕ) :
    polygonLower n = 2 ^ (n + 2) * Real.sin (Real.pi / 2 ^ (n + 2)) := by
  simp only [polygonLower, Real.sin_pi_over_two_pow_succ]
  ring

end PolygonCore
