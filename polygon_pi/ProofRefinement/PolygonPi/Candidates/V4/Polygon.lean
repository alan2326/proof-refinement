import ProofRefinement.PolygonPi.Proof.Main

/-!
# V4 — depth-2 inscribed-polygon lower bound on `π`

Isolates the new analytic ingredient this sprint introduces: a lower bound
`31/10 < π` derived from the depth-2 inscribed polygon
`polygonLower 2 = 8·√(2 - √(2 + √2))` and a triple-nested rational √2 chain.

## Sketch

`polygonLower_lt_pi 2` gives `polygonLower 2 < π`. Unfolding via
`Real.sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = √(2 + √2)` reduces the
polygonLower witness to `8·√(2 - √(2 + √2))`. The triple-nested chain

  √2      < 14143/10000
  √(2+√2) < 18479/10000        [since (18479)² > 34143·10^4]
  √(2-√(2+√2)) > 31/80         [since (31/80)² < 1521/10000]

then yields `polygonLower 2 > 8 · (31/80) = 31/10`, and `polygonLower_lt_pi 2`
chains to `π > 31/10`.

Numerics: `(14143)² = 200_024_449 > 200_000_000 = 2·10^8`,
`(18479)² = 341_473_441 > 341_430_000` (`= (2 + 14143/10000)·10^8`),
`(31/80)² = 961/6400 = 15_015.625/10^5 < 15_210/10^5 = 1521/10000`.

No `axiom`, `opaque`, `native_decide`, or `sorry`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V4

open ProofRefinement.PolygonPi PolygonCore

/-- Sharp rational upper bound on `√2`: `√2 < 14143/10000`. Certified by
`(14143)² = 200_024_449 > 200_000_000 = 2·(10000)²`. -/
lemma sqrt_two_lt_14143_over_10000 : Real.sqrt 2 < 14143 / 10000 := by
  have h1 : Real.sqrt 2 < Real.sqrt ((14143 / 10000 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 14143 / 10000)] at h1
  exact h1

/-- Rational upper bound on `√(2 + √2)`: `√(2 + √2) < 18479/10000`.

Chain: `2 + √2 < 2 + 14143/10000 = 34143/10000 < (18479/10000)²` since
`(18479)² = 341_473_441 > 341_430_000 = 34143·10^4`. -/
lemma sqrt_two_add_sqrt_two_lt : Real.sqrt (2 + Real.sqrt 2) < 18479 / 10000 := by
  have hsqrt2_lt := sqrt_two_lt_14143_over_10000
  have hbound : 2 + Real.sqrt 2 < (18479 / 10000 : ℝ) ^ 2 := by
    nlinarith [hsqrt2_lt]
  have hnn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have h1 : Real.sqrt (2 + Real.sqrt 2)
              < Real.sqrt ((18479 / 10000 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt hnn hbound
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 18479 / 10000)] at h1

/-- Rational lower bound on `√(2 - √(2 + √2))`: strictly greater than `31/80`.

Chain: `2 - √(2 + √2) > 2 - 18479/10000 = 1521/10000 > 961/6400 = (31/80)²`.
Uses `sq_lt_sq₀` to un-square the sqrt inequality. -/
lemma sqrt_two_sub_sqrt_two_add_sqrt_two_gt :
    (31 / 80 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  have h_outer_lt := sqrt_two_add_sqrt_two_lt
  -- Positivity of the outermost radicand: √(2+√2) < 18479/10000 < 2.
  have h_outer_lt_two : Real.sqrt (2 + Real.sqrt 2) < 2 := by
    have : (18479 / 10000 : ℝ) < 2 := by norm_num
    linarith
  have h_radicand_nn : (0 : ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith
  -- The squared bound (31/80)² < 2 - √(2+√2) follows from
  -- 2 - √(2+√2) > 2 - 18479/10000 = 1521/10000, and (31/80)² = 961/6400
  -- = 15015.625/10^5 < 15210/10^5 = 1521/10000.
  have h_sq_bound : ((31 / 80 : ℝ)) ^ 2 < 2 - Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith [h_outer_lt]
  -- Bring both sides under sqrt.
  have h1 : Real.sqrt (((31 / 80 : ℝ)) ^ 2)
              < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    apply Real.sqrt_lt_sqrt _ h_sq_bound
    positivity
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 31 / 80)] at h1

/-- `polygonLower 2 = 8 · √(2 - √(2 + √2))`.

Uses `Real.sqrtTwoAddSeries_two` to unfold the second-generation nested
radical to the double-square-root form. -/
lemma polygonLower_two_eq :
    polygonLower 2 = 8 * Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  unfold polygonLower
  rw [Real.sqrtTwoAddSeries_two]
  norm_num

/-- The depth-2 inscribed-polygon lower bound: `polygonLower 2 > 31/10`. -/
lemma polygonLower_two_gt_thirty_one_over_ten :
    (31 / 10 : ℝ) < polygonLower 2 := by
  rw [polygonLower_two_eq]
  have hinner := sqrt_two_sub_sqrt_two_add_sqrt_two_gt
  have h_rewrite : (31 / 10 : ℝ) = 8 * (31 / 80) := by norm_num
  rw [h_rewrite]
  exact mul_lt_mul_of_pos_left hinner (by norm_num)

/-- The tightened lower bound on `π`, this sprint's core new lemma:
`31/10 < π`.

Combines `polygonLower_lt_pi 2` with `polygonLower_two_gt_thirty_one_over_ten`.
-/
lemma pi_gt_thirty_one_over_ten : (31 / 10 : ℝ) < Real.pi := by
  have hlt : polygonLower 2 < Real.pi := polygonLower_lt_pi 2
  have hgt : (31 / 10 : ℝ) < polygonLower 2 :=
    polygonLower_two_gt_thirty_one_over_ten
  linarith

end ProofRefinement.PolygonPi.Candidates.V4
