-- @parent V1
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V2.Taylor

/-!
# V2 — fifth-order Taylor upper bound on `sin` opens the `lambda` side

`kappa = 2/3`, `lambda = 1/4`, score `5/12`.

The upper conjunct is V1's proof verbatim (unchanged Taylor cubic lower on
`sin`, unchanged `π ≤ 4` factor). The lower conjunct is new:

* `sin_lt_taylor5 : sin x < x - x^3/6 + x^5/120` for `x > 0`, proved in
  `Candidates/V2/Taylor.lean` by a nested `strictMonoOn_of_deriv_pos` chain
  whose innermost step reuses V1's cubic lower bound `x - x^3/6 < sin x`.
* `three_lt_pi : 3 < π`, proved here from `polygonLower_lt_pi 1` and a
  nested-radical estimate `√2 < 23/16`.
* Rescaling: at `x = π/2^(n+2)`, `sin_lt_taylor5` multiplied by `2^(n+2)`
  gives `polygonLower n < π - π^3/(96·4^n) + π^5/(30720·16^n)`. Combined with
  `π > 3` and `π ≤ 4` (so `π^3·(320 - π^2) > 27·304 > 7680`), this closes
  `polygonLower n + (1/4)/4^n < π`, i.e. `lambda = 1/4`.

Score `5/12 = 2/3 - 1/4` is a strict `1/4` improvement over V1.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V2

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, opened for the first time by the 5th-order
Taylor upper bound. -/
def lambda : ℝ := 1 / 4

/-- Upper error coefficient. Unchanged from V1. -/
def kappa : ℝ := 2 / 3

/-- `3 < π`, proved via the depth-1 polygon and a nested-radical estimate.

Since `polygonLower 1 = 4 · √(2 - √2)` and `√2 < 23/16`, we get
`2 - √2 > 9/16`, so `√(2 - √2) > 3/4`, hence `polygonLower 1 > 3`. The
inscribed-polygon bound `polygonLower 1 < π` then gives `3 < π`. -/
lemma three_lt_pi : (3 : ℝ) < Real.pi := by
  -- Trusted: polygonLower 1 < π.
  have hlt : polygonLower 1 < Real.pi := polygonLower_lt_pi 1
  -- polygonLower 1 = 4 * √(2 - √2), using Real.sqrtTwoAddSeries_one.
  have hpoly : polygonLower 1 = 4 * Real.sqrt (2 - Real.sqrt 2) := by
    unfold polygonLower
    rw [Real.sqrtTwoAddSeries_one]
    norm_num
  -- √2 < 23/16, via sqrt monotonicity and (23/16)^2 > 2.
  have hsqrt2_bound : Real.sqrt 2 < 23 / 16 := by
    have h1 : Real.sqrt 2 < Real.sqrt ((23 / 16 : ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 23 / 16)] at h1
    exact h1
  -- 2 - √2 > 9/16.
  have hdiff_pos : (9 / 16 : ℝ) < 2 - Real.sqrt 2 := by linarith
  -- √(2 - √2) > 3/4, via sqrt monotonicity and (3/4)^2 = 9/16 < 2 - √2.
  have hbound : ((3 / 4 : ℝ)) ^ 2 < 2 - Real.sqrt 2 := by
    have h : ((3 / 4 : ℝ)) ^ 2 = 9 / 16 := by norm_num
    linarith
  have hinner : (3 / 4 : ℝ) < Real.sqrt (2 - Real.sqrt 2) := by
    have h1 : Real.sqrt (((3 / 4 : ℝ)) ^ 2) < Real.sqrt (2 - Real.sqrt 2) :=
      Real.sqrt_lt_sqrt (by positivity) hbound
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 4)] at h1
    exact h1
  -- So polygonLower 1 = 4 · √(2 - √2) > 4 · (3/4) = 3.
  have h_poly_gt : (3 : ℝ) < polygonLower 1 := by
    rw [hpoly]
    have h_rewrite : (3 : ℝ) = 4 * (3 / 4) := by norm_num
    rw [h_rewrite]
    exact mul_lt_mul_of_pos_left hinner (by norm_num)
  linarith

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- LOWER CONJUNCT: polygonLower n + (1/4) / 4^n < π.
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
    -- Taylor 5 upper on sin, scaled by 2^(n+2).
    have htay := sin_lt_taylor5 hx
    have key : polygonLower n < 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2)
          - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6
          + (Real.pi / 2 ^ (n + 2)) ^ 5 / 120) := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left htay hN
    -- Collapse the RHS.
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2)
          - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6
          + (Real.pi / 2 ^ (n + 2)) ^ 5 / 120)
        = Real.pi - Real.pi ^ 3 / (96 * 4 ^ n)
          + Real.pi ^ 5 / (30720 * 16 ^ n) := by
      rw [hpow, h16n, h4n]; field_simp; ring
    rw [hid] at key
    -- π > 3 (proved above) and π ≤ 4.
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
    -- The core arithmetic: π^5 + 7680 ≤ 320 · π^3.
    have hcore : Real.pi ^ 5 + 7680 ≤ 320 * Real.pi ^ 3 := by
      -- 320 π^3 - π^5 ≥ 320 π^3 - 16 π^3 = 304 π^3 > 304 · 27 = 8208 > 7680.
      have h304pi3 : 304 * (27 : ℝ) < 304 * Real.pi ^ 3 :=
        mul_lt_mul_of_pos_left hπ_cube_gt (by norm_num : (0 : ℝ) < 304)
      linarith
    -- Lift by 4^n ≥ 1: π^5 + 7680 · 4^n ≤ 320 · π^3 · 4^n.
    have hcore_pos : 0 ≤ 320 * Real.pi ^ 3 - 7680 := by
      have : (0 : ℝ) ≤ Real.pi ^ 5 := by positivity
      linarith
    have hstep_ge_one : (4 : ℝ) ^ n - 1 ≥ 0 := by linarith
    have h_prod : 0 ≤ (320 * Real.pi ^ 3 - 7680) * ((4 : ℝ) ^ n - 1) :=
      mul_nonneg hcore_pos hstep_ge_one
    have h_lift : Real.pi ^ 5 + 7680 * (4 : ℝ) ^ n
        ≤ 320 * Real.pi ^ 3 * (4 : ℝ) ^ n := by
      nlinarith [hcore, h_prod]
    -- Convert to divisions:
    --   (1/4)/4^n + π^5/(30720·16^n) ≤ π^3/(96·4^n)
    -- via the identity below (h_diff_id) plus divide-by-positive.
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
    -- Combine key + h_diff_nn.
    simp only [lambda]
    linarith
  · -- UPPER CONJUNCT: V1's proof verbatim.
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
    have hpi3 : Real.pi ^ 3 ≤ 64 := by
      have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3
      norm_num at h
      exact h
    have hbound : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (2 / 3) / 4 ^ n := by
      have h1 : Real.pi ^ 3 / (96 * 4 ^ n) ≤ 64 / (96 * 4 ^ n) := by gcongr
      have h2 : (64 : ℝ) / (96 * 4 ^ n) = (2 / 3) / 4 ^ n := by
        field_simp
        ring
      linarith
    simp only [kappa]
    linarith

end ProofRefinement.PolygonPi.Candidates.V2
