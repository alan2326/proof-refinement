-- @parent seed
import ProofRefinement.PolygonPi.Proof.Main

/-!
# V0 — the baseline candidate

`kappa = 1`, `lambda = 0`, score `1`.

The lower coefficient is free: at `lambda = 0` the lower conjunct is exactly the
trusted `polygonLower_lt_pi`.

The upper coefficient is proved inline from two Mathlib facts:
`Real.sin_gt_sub_cube` and `Real.pi_le_four`. Nothing about that chain is
hoisted into the trusted surface — it lives here, in candidate space, where a
successor is free to replace any part of it.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V0

open ProofRefinement.PolygonPi PolygonCore

/-- Baseline lower error coefficient. -/
def lambda : ℝ := 0

/-- Baseline upper error coefficient. -/
def kappa : ℝ := 1

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- Lower conjunct: `lambda = 0` reduces this to the trusted bound.
    simpa [lambda] using polygonLower_lt_pi n
  · -- Upper conjunct.
    have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have h1le : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have h4le : (4 : ℝ) ≤ 2 ^ (n + 2) := by rw [hpow]; linarith
    -- The side condition `x ≤ 1` of the cubic estimate.
    have hx1 : Real.pi / 2 ^ (n + 2) ≤ 1 := by
      rw [div_le_one hN]; linarith [Real.pi_le_four]
    -- The cubic estimate, scaled by the number of sides.
    have hcube := Real.sin_gt_sub_cube hx hx1
    have key : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 4) < polygonLower n := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left hcube hN
    -- Collapse the left-hand side to `π - π ^ 3 / (64 * 4 ^ n)`.
    have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 4)
        = Real.pi - Real.pi ^ 3 / (64 * 4 ^ n) := by
      rw [hpow, h4n]; field_simp; ring
    rw [hid] at key
    -- `π ≤ 4` gives `π ^ 3 ≤ 64`, so the remainder is below `1 / 4 ^ n`.
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

end ProofRefinement.PolygonPi.Candidates.V0
