-- @parent V1
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V2.DeficitMonotone
import ProofRefinement.PolygonPi.Candidates.V2.CubicDeficit

/-!
# V2 — replacing the whole upper chain by a global cubic plus a π bootstrap

`kappa = 3229947/10000000`, `lambda = 29/100`, score `329947/10000000`, against
the parent `V1`'s `71/100`.

## The upper side (new)

`V1` inherited `V0`'s upper chain verbatim: Mathlib's restricted cubic
(`x - x ^ 3 / 4 < sin x`, valid only on `0 < x ≤ 1`) together with
`Real.pi_le_four`, which was doing *two* jobs — supplying `π ^ 3 ≤ 64` and
discharging the domain hypothesis `π / 2 ^ (n + 2) ≤ 1`. That gave
`kappa = π ^ 3 / 64 ≤ 1`.

`Candidates/V2/CubicDeficit.lean` replaces both. It proves the sharp global
cubic `x - sin x ≤ x ^ 3 / 6` for **all** `x ≥ 0` from
`monotone_of_hasDerivAt_nonneg` applied to `t ↦ t ^ 3 / 6 - t + sin t`, whose
derivative `t ^ 2 / 2 - 1 + cos t` is non-negative everywhere by
`Real.one_sub_sq_div_two_lt_cos`. Because there is no domain hypothesis left,
the `n` cancels exactly and the deficit bound is uniform:

    ∀ n,  π - polygonLower n ≤ π ^ 3 / (96 * 4 ^ n).

That restricted cubic no longer appears anywhere in `V2`, and the whole upper
side of the contract collapses to the single numeric statement
`π ^ 3 / 96 < kappa`.

That number is then pinned by *bootstrapping the deficit bound against itself*.
At depth `2` it reads `π ≤ polygonLower 2 + π ^ 3 / 1536`, so any upper bound
`π ≤ c` yields the better `π ≤ 3.1214464 + c ^ 3 / 1536` (the constant being a
certified rational upper bound for `polygonLower 2 = 8 √(2 - √(2 + √2))`). The
map is a contraction; five rounds from `Real.pi_le_four` reach the fixed point
of the rounded iteration,

    4 → 3.1631131 → 3.1420505 → 3.1416417 → 3.1416338 → 3.1416336,

giving `π ^ 3 / 96 < 0.3229947`. The analytic floor of this chain is
`π ^ 3 / 96 = 0.32298205…`, so the upper side now sits `1.3 × 10 ^ -5` above its
ceiling and is, like the lower side, essentially closed for this family of
argument. Nothing is circular: `deficit_le` is proved with `π ^ 3` symbolic and
mentions no numeric bound on `π`.

## The lower side (carried over from `V1`)

Unchanged: `Candidates/V2/DeficitMonotone.lean` (a verbatim copy of `V1`'s) shows
the scaled deficit `4 ^ n * (π - polygonLower n)` is monotone non-decreasing, so
the binding constraint is at `n = 0` and `lambda`'s exact ceiling is
`π - 2 √2 = 0.31316…`. The rational certification below is `V1`'s, in the
opposite direction to the new one in `CubicDeficit.lean`: the lower conjunct
needs *upper* bounds on `√2` and `√(2 + √2)` and a *lower* bound on
`√(2 - √(2 + √2))`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V2

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, strictly below the exact ceiling `π - 2√2`. -/
def lambda : ℝ := 29/100

/-- Upper error coefficient, strictly above the analytic floor `π ^ 3 / 96`. -/
def kappa : ℝ := 3229947/10000000

/-! ### Staged rational certification of the nested radical, `V1` direction

These are the bounds the *lower* conjunct needs, and they point the opposite way
to `CubicDeficit.lean`'s `sqrt_two_gt` / `sqrt_two_add_sqrt_two_gt` /
`sqrt_two_sub_lt`. Both families are kept, named `_lt` / `_gt`, so a successor
can pick the one it needs.
-/

/-- `√2 < 1.4143`, since `1.4143 ^ 2 = 2.00024449 > 2`. -/
lemma sqrt_two_lt : Real.sqrt 2 < 14143/10000 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√(2 + √2) < 1.8478`, since `1.8478 ^ 2 = 3.41436484 > 2 + 1.4143`. -/
lemma sqrt_two_add_sqrt_two_lt : Real.sqrt (2 + Real.sqrt 2) < 18478/10000 := by
  have hnn : (0:ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  nlinarith [sqrt_two_lt, Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrt 2)]

/-- `√(2 - √(2 + √2)) > 0.3901`, since `0.3901 ^ 2 = 0.15217801 < 2 - 1.8478`. -/
lemma sqrt_two_sub_gt :
    (3901/10000 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  have hnn : (0:ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith [sqrt_two_add_sqrt_two_lt]
  nlinarith [sqrt_two_add_sqrt_two_lt, Real.sq_sqrt hnn,
    Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2))]

lemma polygonLower_zero_eq : polygonLower 0 = 2 * Real.sqrt 2 := by
  simp [polygonLower]

/-- The exact ceiling for `lambda`, certified from below via the trusted
`polygonLower_lt_pi 2`. -/
lemma lambda_lt_deficit_zero : lambda < Real.pi - polygonLower 0 := by
  have hpi : polygonLower 2 < Real.pi := polygonLower_lt_pi 2
  rw [polygonLower_two_eq] at hpi
  rw [polygonLower_zero_eq, lambda]
  linarith [sqrt_two_lt, sqrt_two_sub_gt]

/-! ### The scored contract -/

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- Lower conjunct: monotonicity of the scaled deficit reduces it to `n = 0`.
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hd : Real.pi - polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n) :=
      deficit_ge_zero_deficit n
    have hlt : lambda / 4 ^ n < Real.pi - polygonLower n := by
      rw [div_lt_iff₀' h4n]
      linarith [lambda_lt_deficit_zero]
    linarith
  · -- Upper conjunct: the uniform cubic deficit bound plus the bootstrapped
    -- numeric bound on `π ^ 3 / 96`.
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hscaled : (Real.pi - polygonLower n) * 4 ^ n ≤ Real.pi ^ 3 / 96 := by
      calc (Real.pi - polygonLower n) * 4 ^ n
          ≤ Real.pi ^ 3 / (96 * 4 ^ n) * 4 ^ n :=
            mul_le_mul_of_nonneg_right (deficit_le n) h4n.le
        _ = Real.pi ^ 3 / 96 := by field_simp
    have hstrict : (Real.pi - polygonLower n) * 4 ^ n < kappa := by
      rw [kappa]
      exact lt_of_le_of_lt hscaled pi_cube_div_lt
    have : Real.pi - polygonLower n < kappa / 4 ^ n := by
      rw [lt_div_iff₀ h4n]
      exact hstrict
    linarith

end ProofRefinement.PolygonPi.Candidates.V2
