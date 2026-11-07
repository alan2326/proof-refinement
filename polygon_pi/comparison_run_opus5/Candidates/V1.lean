-- @parent V0
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V1.DeficitMonotone

/-!
# V1 — lifting `lambda` off zero by deficit monotonicity

`kappa = 1` (unchanged from `V0`), `lambda = 29/100`, score `71/100`.

## The lower side

`Candidates/V1/DeficitMonotone.lean` proves that the scaled deficit
`D n := 4 ^ n * (π - polygonLower n)` is monotone non-decreasing in `n`, so

    π - polygonLower 0 ≤ D n   for every n.

The contract's lower conjunct is exactly `lambda < D n`, so it is enough to make
`lambda` strictly smaller than the single number `π - polygonLower 0 = π - 2√2`.
That number is the *exact* ceiling for `lambda`: monotonicity says the binding
constraint is at `n = 0`, and it is attained. Every future lower-side sprint is
now a matter of sharpening one rational, never of new analysis.

Here that rational is certified from the trusted `polygonLower_lt_pi 2`:

    π > polygonLower 2 = 8 √(2 - √(2 + √2)) > 3.1208,
    polygonLower 0 = 2 √2 < 2.8286,

so `π - polygonLower 0 > 0.2922 > 29/100`. The nested radical is pinned by a
three-step staged rational certification (`√2`, then `√(2 + √2)`, then
`√(2 - √(2 + √2))`), each step a `Real.sq_sqrt` plus `nlinarith`.

## The upper side

Carried over verbatim from `V0`: `Real.sin_gt_sub_cube` and `Real.pi_le_four`.
`kappa` is out of scope for this sprint by contract.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V1

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, strictly below the exact ceiling `π - 2√2`. -/
def lambda : ℝ := 29/100

/-- Upper error coefficient, unchanged from `V0`. -/
def kappa : ℝ := 1

/-! ### Staged rational certification of the nested radical -/

/-- `√2 < 1.4143`, since `1.4143 ^ 2 = 2.00024449 > 2`. -/
lemma sqrt_two_lt : Real.sqrt 2 < 14143/10000 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√2 < 2`, a convenience consequence. -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  linarith [sqrt_two_lt]

/-- `√(2 + √2) < 1.8478`, since `1.8478 ^ 2 = 3.41436484 > 2 + 1.4143`. -/
lemma sqrt_two_add_sqrt_two_lt : Real.sqrt (2 + Real.sqrt 2) < 18478/10000 := by
  have hnn : (0:ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  have hsq := Real.sq_sqrt hnn
  have hpos := Real.sqrt_nonneg (2 + Real.sqrt 2)
  nlinarith [sqrt_two_lt, hsq, hpos]

/-- `√(2 - √(2 + √2)) > 0.3901`, since `0.3901 ^ 2 = 0.15217801 < 2 - 1.8478`. -/
lemma sqrt_two_sub_lt : (3901/10000 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  have hnn : (0:ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith [sqrt_two_add_sqrt_two_lt]
  have hsq := Real.sq_sqrt hnn
  have hpos := Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2))
  nlinarith [sqrt_two_add_sqrt_two_lt, hsq, hpos]

/-! ### The two polygon values that enter the bound -/

lemma polygonLower_zero_eq : polygonLower 0 = 2 * Real.sqrt 2 := by
  simp [polygonLower]

lemma polygonLower_two_eq :
    polygonLower 2 = 8 * Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  rw [polygonLower, Real.sqrtTwoAddSeries_two]
  norm_num

/-- The exact ceiling for `lambda`, certified from below. -/
lemma lambda_lt_deficit_zero : lambda < Real.pi - polygonLower 0 := by
  have hpi : polygonLower 2 < Real.pi := polygonLower_lt_pi 2
  rw [polygonLower_two_eq] at hpi
  rw [polygonLower_zero_eq, lambda]
  linarith [sqrt_two_lt, sqrt_two_sub_lt]

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
  · -- Upper conjunct: carried over from `V0`.
    have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have h1le : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have h4le : (4 : ℝ) ≤ 2 ^ (n + 2) := by rw [hpow]; linarith
    have hx1 : Real.pi / 2 ^ (n + 2) ≤ 1 := by
      rw [div_le_one hN]; linarith [Real.pi_le_four]
    have hcube := Real.sin_gt_sub_cube hx hx1
    have key : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 4) < polygonLower n := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left hcube hN
    have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 4)
        = Real.pi - Real.pi ^ 3 / (64 * 4 ^ n) := by
      rw [hpow, h4n]; field_simp; ring
    rw [hid] at key
    have h4npos : (0 : ℝ) < 4 ^ n := by positivity
    have hpi3 : Real.pi ^ 3 ≤ 64 := by
      have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3
      norm_num at h
      exact h
    have hbound : Real.pi ^ 3 / (64 * 4 ^ n) ≤ 1 / 4 ^ n := by
      have h1 : Real.pi ^ 3 / (64 * 4 ^ n) ≤ 64 / (64 * 4 ^ n) := by gcongr
      have h2 : (64 : ℝ) / (64 * 4 ^ n) = 1 / 4 ^ n := by field_simp
      linarith
    simp only [kappa]
    linarith

end ProofRefinement.PolygonPi.Candidates.V1
