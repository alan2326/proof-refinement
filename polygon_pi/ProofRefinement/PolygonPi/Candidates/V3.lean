-- @parent V2
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V3.Taylor
import ProofRefinement.PolygonPi.Candidates.V3.Tan

/-!
# V3 — tan-based upper on `π` cuts the V0-vintage `π ≤ 4` factor

`kappa = 343/768`, `lambda = 1/4`, score `151/768`.

Attacks the last V0-vintage quantitative piece in the upper conjunct: the
`π ≤ 4 ⇒ π³ ≤ 64` factor. Replaces `Real.pi_le_four` with a strict
`pi_lt_seven_halves : π < 7/2` derived from `Real.lt_tan` at `π/8`, yielding
`π³ ≤ 343/8`. Drives `kappa` from `2/3 = 320/768` down to `343/768`.

The lower conjunct is preserved word-for-word from V2 (same
`sin_lt_taylor5`, same `three_lt_pi`, same `Real.pi_le_four` factor — the
lambda side is a separate architectural rung).

Score `151/768 = 343/768 - 192/768` is a strict `169/768 ≈ 0.220`
improvement over V2's `5/12 = 320/768`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V3

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient. Unchanged from V2. -/
def lambda : ℝ := 1 / 4

/-- Upper error coefficient, driven down by replacing `π ≤ 4` with the
tighter `π < 7/2` (i.e. `π³ ≤ 343/8` instead of `π³ ≤ 64`). -/
def kappa : ℝ := 343 / 768

/-- `3 < π`, restated verbatim from V2 (same depth-1 polygon + √2 < 23/16
argument). Candidates never import each other. -/
lemma three_lt_pi : (3 : ℝ) < Real.pi := by
  have hlt : polygonLower 1 < Real.pi := polygonLower_lt_pi 1
  have hpoly : polygonLower 1 = 4 * Real.sqrt (2 - Real.sqrt 2) := by
    unfold polygonLower
    rw [Real.sqrtTwoAddSeries_one]
    norm_num
  have hsqrt2_bound : Real.sqrt 2 < 23 / 16 := by
    have h1 : Real.sqrt 2 < Real.sqrt ((23 / 16 : ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 23 / 16)] at h1
    exact h1
  have hdiff_pos : (9 / 16 : ℝ) < 2 - Real.sqrt 2 := by linarith
  have hbound : ((3 / 4 : ℝ)) ^ 2 < 2 - Real.sqrt 2 := by
    have h : ((3 / 4 : ℝ)) ^ 2 = 9 / 16 := by norm_num
    linarith
  have hinner : (3 / 4 : ℝ) < Real.sqrt (2 - Real.sqrt 2) := by
    have h1 : Real.sqrt (((3 / 4 : ℝ)) ^ 2) < Real.sqrt (2 - Real.sqrt 2) :=
      Real.sqrt_lt_sqrt (by positivity) hbound
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 4)] at h1
    exact h1
  have h_poly_gt : (3 : ℝ) < polygonLower 1 := by
    rw [hpoly]
    have h_rewrite : (3 : ℝ) = 4 * (3 / 4) := by norm_num
    rw [h_rewrite]
    exact mul_lt_mul_of_pos_left hinner (by norm_num)
  linarith

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- LOWER CONJUNCT: V2's proof verbatim (unchanged).
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
    have hπ3 : (3 : ℝ) < Real.pi := three_lt_pi
    have hπ_sq_le : Real.pi ^ 2 ≤ 16 := by nlinarith [hπ4, hπpos]
    have hπ_cube_gt : (27 : ℝ) < Real.pi ^ 3 := by
      nlinarith [hπ3, hπpos, mul_pos hπpos hπpos]
    have hπ_5_le : Real.pi ^ 5 ≤ 16 * Real.pi ^ 3 := by
      have hcube_nn : 0 ≤ Real.pi ^ 3 := by positivity
      have hpow5 : Real.pi ^ 5 = Real.pi ^ 2 * Real.pi ^ 3 := by ring
      rw [hpow5]
      exact mul_le_mul_of_nonneg_right hπ_sq_le hcube_nn
    have hcore : Real.pi ^ 5 + 7680 ≤ 320 * Real.pi ^ 3 := by
      have h304pi3 : 304 * (27 : ℝ) < 304 * Real.pi ^ 3 :=
        mul_lt_mul_of_pos_left hπ_cube_gt (by norm_num : (0 : ℝ) < 304)
      linarith
    have hcore_pos : 0 ≤ 320 * Real.pi ^ 3 - 7680 := by
      have : (0 : ℝ) ≤ Real.pi ^ 5 := by positivity
      linarith
    have hstep_ge_one : (4 : ℝ) ^ n - 1 ≥ 0 := by linarith
    have h_prod : 0 ≤ (320 * Real.pi ^ 3 - 7680) * ((4 : ℝ) ^ n - 1) :=
      mul_nonneg hcore_pos hstep_ge_one
    have h_lift : Real.pi ^ 5 + 7680 * (4 : ℝ) ^ n
        ≤ 320 * Real.pi ^ 3 * (4 : ℝ) ^ n := by
      nlinarith [hcore, h_prod]
    have h_diff_id :
        Real.pi ^ 3 / (96 * (4 : ℝ) ^ n)
          - Real.pi ^ 5 / (30720 * (16 : ℝ) ^ n)
          - (1 / 4) / (4 : ℝ) ^ n
        = (320 * Real.pi ^ 3 * (4 : ℝ) ^ n - Real.pi ^ 5 - 7680 * (4 : ℝ) ^ n)
            / (30720 * (16 : ℝ) ^ n) := by
      rw [h16n]; field_simp; ring
    have h_diff_nn :
        0 ≤ Real.pi ^ 3 / (96 * (4 : ℝ) ^ n)
              - Real.pi ^ 5 / (30720 * (16 : ℝ) ^ n)
              - (1 / 4) / (4 : ℝ) ^ n := by
      rw [h_diff_id]
      apply div_nonneg _ (by positivity)
      linarith
    simp only [lambda]
    linarith
  · -- UPPER CONJUNCT: V1/V2 arithmetic with π ≤ 4 swapped for π < 7/2.
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
    -- The new tan-anchored bound: π < 7/2, hence π^3 ≤ 343/8.
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

end ProofRefinement.PolygonPi.Candidates.V3
