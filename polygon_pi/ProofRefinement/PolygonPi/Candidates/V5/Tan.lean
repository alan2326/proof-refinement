import ProofRefinement.PolygonPi.Proof.Main

/-!
# V5 — tan-based upper bound on `π`, one polygon depth deeper than V4

Introduces `pi_lt_sixteen_fifths : π < 16/5`, derived from `Real.lt_tan` at
the depth-2 circumscribed-polygon vertex angle `π/16`.

## Sketch

`Real.lt_tan` gives `π/16 < tan(π/16) = sin(π/16) / cos(π/16)`. Using the
closed forms `sin(π/16) = √(2 - √(2 + √2))/2` and
`cos(π/16) = √(2 + √(2 + √2))/2` (both in Mathlib
`Trigonometric/Basic.lean`), squaring reduces the target `tan(π/16) < 1/5`
to the polynomial inequality `25 · (2 - √(2+√2)) < 2 + √(2+√2)`,
i.e. `48 < 26·√(2+√2)`, i.e. `√(2+√2) > 24/13`, which follows from
`√2 > 238/169` (since `(24/13)² = 576/169 = 2 + 238/169 < 2 + √2`).
Combined with `π/16 < tan(π/16)`, this yields `π < 16/5`.

Structurally mirrors V3/V4's `pi_lt_seven_halves` at `π/8`, one polygon
depth deeper (nested radical goes from single √2 to `√(2 + √2)`).

No `axiom`, `opaque`, `native_decide`, or `sorry`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open ProofRefinement.PolygonPi PolygonCore

/-- Rational lower bound on `√2`: `√2 > 238/169`. Certified by
`238² = 56_644 < 57_122 = 2 · 169²`. -/
lemma sqrt_two_gt_238_over_169 : (238 / 169 : ℝ) < Real.sqrt 2 := by
  have h_target : ((238 / 169 : ℝ)) ^ 2 < (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hb : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  exact (sq_lt_sq₀ (by norm_num) hb).mp h_target

/-- Upper bound on `√2` — needed only to keep `2 - √2 ≥ 0` in scope
(reused indirectly via `√(2+√2) < 2`). -/
lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ≤ Real.sqrt 4 :=
    Real.sqrt_le_sqrt (by norm_num)
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- Rational lower bound on `√(2 + √2)`: `√(2 + √2) > 24/13`.

Chain: `(24/13)² = 576/169 = 2 + 238/169 < 2 + √2` given `√2 > 238/169`. -/
lemma sqrt_two_add_sqrt_two_gt_24_over_13 :
    (24 / 13 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
  have hsqrt2 : (238 / 169 : ℝ) < Real.sqrt 2 := sqrt_two_gt_238_over_169
  have h_bound : ((24 / 13 : ℝ)) ^ 2 < 2 + Real.sqrt 2 := by
    nlinarith [hsqrt2]
  have h_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have h1 : Real.sqrt (((24 / 13 : ℝ)) ^ 2)
              < Real.sqrt (2 + Real.sqrt 2) := by
    apply Real.sqrt_lt_sqrt _ h_bound
    positivity
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 24 / 13)] at h1

/-- Upper bound on `√(2 + √2)`: strictly `< 2`. Needed to keep
`2 - √(2 + √2) ≥ 0` in scope for `Real.sq_sqrt`. Derived from `√2 < 2`
via `2 + √2 ≤ 4 = 2²`. -/
lemma sqrt_two_add_sqrt_two_lt_two : Real.sqrt (2 + Real.sqrt 2) < 2 := by
  have h_sqrt2_le : Real.sqrt 2 ≤ 2 := sqrt_two_le_two
  have h_radicand_le : 2 + Real.sqrt 2 ≤ (2 : ℝ) ^ 2 := by
    have := h_sqrt2_le; nlinarith
  -- We want a strict inequality, so use the strict variant.
  have h_sqrt2_lt : Real.sqrt 2 < 2 := by
    have hp : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    -- √2 < 2 ↔ 2 < 4 (squaring both nonneg sides)
    have hb : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h4 : (Real.sqrt 2) ^ 2 < (2 : ℝ) ^ 2 := by rw [hp]; norm_num
    exact (sq_lt_sq₀ hb (by norm_num)).mp h4
  have h_radicand_lt : 2 + Real.sqrt 2 < (2 : ℝ) ^ 2 := by nlinarith
  have hnn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have h1 : Real.sqrt (2 + Real.sqrt 2) < Real.sqrt ((2 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt hnn h_radicand_lt
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h1

/-- The tan-anchored upper bound on `π` opened by this sprint:
`π < 16/5`.

Route 2 shape (mirror of V4/Tan.lean's `pi_lt_seven_halves`, one polygon
depth deeper): bound `sin(π/16)/cos(π/16)` directly by squaring and
comparing to the algebraic form of `sin²(π/16) = (2 - √(2+√2))/4`,
`cos²(π/16) = (2 + √(2+√2))/4`. Avoids any closed form for `tan(π/16)`. -/
lemma pi_lt_sixteen_fifths : Real.pi < 16 / 5 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- (0, π/2) ownership of π/16.
  have h1 : (0 : ℝ) < Real.pi / 16 := by positivity
  have h2 : Real.pi / 16 < Real.pi / 2 := by linarith
  -- Real.lt_tan gives strict π/16 < tan(π/16).
  have htan_lb : Real.pi / 16 < Real.tan (Real.pi / 16) := Real.lt_tan h1 h2
  -- cos(π/16) > 0 via cos_pos_of_mem_Ioo (interval (-π/2, π/2)).
  have hcos_pos : (0 : ℝ) < Real.cos (Real.pi / 16) := by
    apply Real.cos_pos_of_mem_Ioo
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  -- sin(π/16) > 0 via sin_pos_of_pos_of_lt_pi.
  have hsin_pos : (0 : ℝ) < Real.sin (Real.pi / 16) :=
    Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  -- Nonnegativity of nested radicands.
  have hsqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2psqrt2_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by linarith
  have hsqrt_2psqrt2_nn : (0 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have h_outer_upper : Real.sqrt (2 + Real.sqrt 2) < 2 :=
    sqrt_two_add_sqrt_two_lt_two
  have h_minus_nn : (0 : ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by linarith
  have h_plus_nn : (0 : ℝ) ≤ 2 + Real.sqrt (2 + Real.sqrt 2) := by linarith
  -- Squared closed forms at π/16.
  have hsin_sq : Real.sin (Real.pi / 16) ^ 2
      = (2 - Real.sqrt (2 + Real.sqrt 2)) / 4 := by
    rw [Real.sin_pi_div_sixteen, div_pow, Real.sq_sqrt h_minus_nn]
    norm_num
  have hcos_sq : Real.cos (Real.pi / 16) ^ 2
      = (2 + Real.sqrt (2 + Real.sqrt 2)) / 4 := by
    rw [Real.cos_pi_div_sixteen, div_pow, Real.sq_sqrt h_plus_nn]
    norm_num
  -- Nonnegativity of 5·sin(π/16) and 1·cos(π/16).
  have h_lhs_nn : (0 : ℝ) ≤ 5 * Real.sin (Real.pi / 16) := by positivity
  have h_rhs_nn : (0 : ℝ) ≤ Real.cos (Real.pi / 16) := hcos_pos.le
  -- Key numerical bound: √(2+√2) > 24/13.
  have h_s_gt : (24 / 13 : ℝ) < Real.sqrt (2 + Real.sqrt 2) :=
    sqrt_two_add_sqrt_two_gt_24_over_13
  -- Squared inequality: (5 sin)^2 < (cos)^2.
  -- Substituting closed forms and multiplying by 4:
  --   25·(2 - √(2+√2)) < 2 + √(2+√2)
  --   ↔ 50 - 25·s < 2 + s   (s := √(2+√2))
  --   ↔ 48 < 26·s
  --   ↔ s > 24/13
  -- Established by h_s_gt.
  have h_sq_lt : (5 * Real.sin (Real.pi / 16)) ^ 2
                < (Real.cos (Real.pi / 16)) ^ 2 := by
    have hexpand : (5 * Real.sin (Real.pi / 16)) ^ 2
                  = 25 * Real.sin (Real.pi / 16) ^ 2 := by ring
    rw [hexpand, hsin_sq, hcos_sq]
    nlinarith [h_s_gt, hsqrt_2psqrt2_nn]
  -- Un-square to get 5·sin < cos.
  have h_lin : 5 * Real.sin (Real.pi / 16) < Real.cos (Real.pi / 16) :=
    (sq_lt_sq₀ h_lhs_nn h_rhs_nn).mp h_sq_lt
  -- Rewrite as tan(π/16) < 1/5.
  have h_tan_lt : Real.tan (Real.pi / 16) < 1 / 5 := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos_pos]
    linarith
  -- Chain: π/16 < tan(π/16) < 1/5, so π < 16 · 1/5 = 16/5.
  linarith [htan_lb, h_tan_lt]

end ProofRefinement.PolygonPi.Candidates.V5
