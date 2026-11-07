import ProofRefinement.PolygonPi.Proof.Main

/-!
# V3 — tan-based upper bound on `π`

Isolates the new analytic ingredient this sprint introduces: an upper bound
`π < 7/2` derived from `Real.lt_tan` at the depth-1 circumscribed-polygon
vertex angle `π/8`.

## Sketch

`Real.lt_tan` gives `π/8 < tan(π/8) = sin(π/8) / cos(π/8)`. Using the closed
forms `sin(π/8) = √(2-√2)/2` and `cos(π/8) = √(2+√2)/2` (both already in
Mathlib), squaring reduces the target `tan(π/8) < 7/16` to the polynomial
inequality `256 · (2-√2) < 49 · (2+√2)`, i.e. `414 < 305·√2`, which follows
from `√2 > 7/5` (since `305 · 7/5 = 427 > 414`). Combined with
`π/8 < tan(π/8)`, this yields `π < 7/2`.

No `axiom`, `opaque`, `native_decide`, or `sorry`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V3

open ProofRefinement.PolygonPi PolygonCore

/-- Rational lower bound on `√2`. Used to close the polynomial inequality
`414 < 305·√2` inside `pi_lt_seven_halves`. -/
lemma sqrt_two_gt_seven_fifths : (7 : ℝ) / 5 < Real.sqrt 2 := by
  have h_target : ((7 : ℝ) / 5) ^ 2 < (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hb : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  exact (sq_lt_sq₀ (by norm_num) hb).mp h_target

/-- Upper bound on `√2` — needed only to keep `2 - √2 ≥ 0` in scope. -/
lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ≤ Real.sqrt 4 :=
    Real.sqrt_le_sqrt (by norm_num)
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- The tan-anchored upper bound on `π` opened by this sprint.

Route 2 from the sprint contract: bound `sin(π/8)/cos(π/8)` directly by
squaring and comparing to the algebraic form of `sin²(π/8) = (2-√2)/4`,
`cos²(π/8) = (2+√2)/4`. Avoids the closed form `tan(π/8) = √2 - 1`. -/
lemma pi_lt_seven_halves : Real.pi < 7 / 2 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- (0, π/2) ownership of π/8.
  have h1 : (0 : ℝ) < Real.pi / 8 := by positivity
  have h2 : Real.pi / 8 < Real.pi / 2 := by linarith
  -- Real.lt_tan gives strict π/8 < tan(π/8).
  have htan_lb : Real.pi / 8 < Real.tan (Real.pi / 8) := Real.lt_tan h1 h2
  -- cos(π/8) > 0 via cos_pos_of_mem_Ioo (interval (-π/2, π/2)).
  have hcos_pos : (0 : ℝ) < Real.cos (Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  -- sin(π/8) > 0 via sin_pos_of_pos_of_lt_pi.
  have hsin_pos : (0 : ℝ) < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  -- Nonnegativity of nested radicands.
  have hsqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2msqrt2_nn : (0 : ℝ) ≤ 2 - Real.sqrt 2 := by
    have := sqrt_two_le_two; linarith
  have h2psqrt2_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by linarith
  -- Squared closed forms at π/8.
  have hsin_sq : Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
    rw [Real.sin_pi_div_eight, div_pow, Real.sq_sqrt h2msqrt2_nn]
    norm_num
  have hcos_sq : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
    rw [Real.cos_pi_div_eight, div_pow, Real.sq_sqrt h2psqrt2_nn]
    norm_num
  -- Nonnegativity of 16·sin(π/8) and 7·cos(π/8).
  have h_lhs_nn : (0 : ℝ) ≤ 16 * Real.sin (Real.pi / 8) := by positivity
  have h_rhs_nn : (0 : ℝ) ≤ 7 * Real.cos (Real.pi / 8) := by positivity
  -- Key algebraic inequality: 414 < 305·√2.
  have hsqrt2_gt : (7 : ℝ) / 5 < Real.sqrt 2 := sqrt_two_gt_seven_fifths
  -- Squared inequality: (16 sin)^2 < (7 cos)^2.
  have h_sq_lt : (16 * Real.sin (Real.pi / 8)) ^ 2
                < (7 * Real.cos (Real.pi / 8)) ^ 2 := by
    have hexpand_lhs : (16 * Real.sin (Real.pi / 8)) ^ 2
                      = 256 * Real.sin (Real.pi / 8) ^ 2 := by ring
    have hexpand_rhs : (7 * Real.cos (Real.pi / 8)) ^ 2
                      = 49 * Real.cos (Real.pi / 8) ^ 2 := by ring
    rw [hexpand_lhs, hsin_sq, hexpand_rhs, hcos_sq]
    -- Goal: 256 * ((2 - √2) / 4) < 49 * ((2 + √2) / 4)
    -- Multiply out (linarith): 512 - 256·√2 < 98 + 49·√2, i.e. 414 < 305·√2.
    -- From √2 > 7/5 we get 305·√2 > 305 · 7/5 = 427 > 414.
    nlinarith [hsqrt2_gt, hsqrt2_nn]
  -- Un-square to get 16·sin < 7·cos.
  have h_lin : 16 * Real.sin (Real.pi / 8) < 7 * Real.cos (Real.pi / 8) :=
    (sq_lt_sq₀ h_lhs_nn h_rhs_nn).mp h_sq_lt
  -- Rewrite as tan(π/8) < 7/16.
  have h_tan_lt : Real.tan (Real.pi / 8) < 7 / 16 := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos_pos]
    linarith
  -- Chain: π/8 < tan(π/8) < 7/16, so π < 8 · 7/16 = 7/2.
  linarith [htan_lb, h_tan_lt]

end ProofRefinement.PolygonPi.Candidates.V3
