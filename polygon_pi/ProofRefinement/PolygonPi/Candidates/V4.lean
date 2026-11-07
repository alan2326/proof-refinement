-- @parent V3
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V4.Taylor
import ProofRefinement.PolygonPi.Candidates.V4.Tan
import ProofRefinement.PolygonPi.Candidates.V4.Polygon

/-!
# V4 — depth-2 inscribed polygon cuts the V2-vintage `π > 3` factor

`kappa = 343/768`, `lambda = 9/32`, score `127/768`.

Attacks the last V0/V2-vintage quantitative piece in the lower conjunct: the
`π > 3` factor (V2-vintage, unchanged since sprint 002). Replaces
`three_lt_pi` with a strictly tighter `pi_gt_thirty_one_over_ten : π > 31/10`
derived from `polygonLower_lt_pi 2` at the depth-2 inscribed polygon plus a
triple-nested √2 chain (`Candidates/V4/Polygon.lean`). That extra ~10% on
`π³` (from `π³ > 27` to `π³ > 29.791`) is enough to lift `lambda` from
`1/4 = 192/768` to `9/32 = 216/768`.

The upper conjunct is preserved word-for-word from V3 (same
`sin_gt_sub_cube_div_six`, same `pi_lt_seven_halves`, same rescaling to
`π - polygonLower n < (343/768)/4^n`).

Score `127/768 = 343/768 − 216/768` is a strict `24/768 = 1/32 ≈ 0.0313`
improvement over V3's `151/768`. Interval width at depth 10 shrinks from
`1.875 × 10⁻⁷` to `1.577 × 10⁻⁷`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V4

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, lifted from V3's `1/4` by tightening `π > 3`
to `π > 31/10`. -/
def lambda : ℝ := 9 / 32

/-- Upper error coefficient. Unchanged from V3. -/
def kappa : ℝ := 343 / 768

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- LOWER CONJUNCT: V3's proof shape, with `three_lt_pi → pi_gt_thirty_one_over_ten`
    -- and constants `7680 → 8640`, `27 → 29791/1000`, `1/4 → 9/32`.
    have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
    have h16n_pos : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
    have h4n_ge_one : (1 : ℝ) ≤ (4 : ℝ) ^ n :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
    have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have h16n : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
    have htay := sin_lt_taylor5 hx
    have key : polygonLower n < 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2)
          - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6
          + (Real.pi / 2 ^ (n + 2)) ^ 5 / 120) := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left htay hN
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2)
          - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6
          + (Real.pi / 2 ^ (n + 2)) ^ 5 / 120)
        = Real.pi - Real.pi ^ 3 / (96 * 4 ^ n)
          + Real.pi ^ 5 / (30720 * 16 ^ n) := by
      rw [hpow, h16n, h4n]; field_simp; ring
    rw [hid] at key
    have hπpos : 0 < Real.pi := Real.pi_pos
    have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
    -- The tightened π-lower: 31/10 < π (was `three_lt_pi` giving 3 < π in V3).
    have hπ_gt : (31 / 10 : ℝ) < Real.pi := pi_gt_thirty_one_over_ten
    have hπ_sq_le : Real.pi ^ 2 ≤ 16 := by nlinarith [hπ4, hπpos]
    -- π³ > (31/10)³ = 29791/1000, in place of V3's `27 < π³`.
    have hπ_cube_gt : (29791 / 1000 : ℝ) < Real.pi ^ 3 := by
      nlinarith [hπ_gt, hπpos, mul_pos hπpos hπpos]
    have hπ_5_le : Real.pi ^ 5 ≤ 16 * Real.pi ^ 3 := by
      have hcube_nn : 0 ≤ Real.pi ^ 3 := by positivity
      have hpow5 : Real.pi ^ 5 = Real.pi ^ 2 * Real.pi ^ 3 := by ring
      rw [hpow5]
      exact mul_le_mul_of_nonneg_right hπ_sq_le hcube_nn
    -- Core arithmetic: π⁵ + 8640 ≤ 320·π³. Numerics:
    -- 320·π³ - π⁵ ≥ (320 - 16)·π³ = 304·π³ > 304 · 29791/1000
    -- = 9_056_464/1000 = 9056.464 > 8640.
    have hcore : Real.pi ^ 5 + 8640 ≤ 320 * Real.pi ^ 3 := by
      have h304pi3 : 304 * (29791 / 1000 : ℝ) < 304 * Real.pi ^ 3 :=
        mul_lt_mul_of_pos_left hπ_cube_gt (by norm_num : (0 : ℝ) < 304)
      linarith
    have hcore_pos : 0 ≤ 320 * Real.pi ^ 3 - 8640 := by
      have : (0 : ℝ) ≤ Real.pi ^ 5 := by positivity
      linarith
    have hstep_ge_one : (4 : ℝ) ^ n - 1 ≥ 0 := by linarith
    have h_prod : 0 ≤ (320 * Real.pi ^ 3 - 8640) * ((4 : ℝ) ^ n - 1) :=
      mul_nonneg hcore_pos hstep_ge_one
    have h_lift : Real.pi ^ 5 + 8640 * (4 : ℝ) ^ n
        ≤ 320 * Real.pi ^ 3 * (4 : ℝ) ^ n := by
      nlinarith [hcore, h_prod]
    have h_diff_id :
        Real.pi ^ 3 / (96 * (4 : ℝ) ^ n)
          - Real.pi ^ 5 / (30720 * (16 : ℝ) ^ n)
          - (9 / 32) / (4 : ℝ) ^ n
        = (320 * Real.pi ^ 3 * (4 : ℝ) ^ n - Real.pi ^ 5 - 8640 * (4 : ℝ) ^ n)
            / (30720 * (16 : ℝ) ^ n) := by
      rw [h16n]; field_simp; ring
    have h_diff_nn :
        0 ≤ Real.pi ^ 3 / (96 * (4 : ℝ) ^ n)
              - Real.pi ^ 5 / (30720 * (16 : ℝ) ^ n)
              - (9 / 32) / (4 : ℝ) ^ n := by
      rw [h_diff_id]
      apply div_nonneg _ (by positivity)
      linarith
    simp only [lambda]
    linarith
  · -- UPPER CONJUNCT: V3's proof verbatim. Unchanged by this sprint.
    have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have hcube := sin_gt_sub_cube_div_six hx
    have key : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6)
        < polygonLower n := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left hcube hN
    have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6)
        = Real.pi - Real.pi ^ 3 / (96 * 4 ^ n) := by
      rw [hpow, h4n]; field_simp; ring
    rw [hid] at key
    have h4npos : (0 : ℝ) < 4 ^ n := by positivity
    have hπ_lt : Real.pi < 7 / 2 := pi_lt_seven_halves
    have hπ_le : Real.pi ≤ 7 / 2 := le_of_lt hπ_lt
    have hpi3 : Real.pi ^ 3 ≤ 343 / 8 := by
      have h := pow_le_pow_left₀ Real.pi_pos.le hπ_le 3
      norm_num at h
      linarith
    have hbound : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (343 / 768) / 4 ^ n := by
      have h1 : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (343 / 8) / (96 * 4 ^ n) := by gcongr
      have h2 : (343 / 8 : ℝ) / (96 * 4 ^ n) = (343 / 768) / 4 ^ n := by
        rw [div_div, div_div]
        congr 1
        ring
      linarith
    simp only [kappa]
    linarith

end ProofRefinement.PolygonPi.Candidates.V4
