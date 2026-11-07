import ProofRefinement.PolygonPi.Proof.Main

/-!
# A global cubic Taylor bound, the uniform deficit bound, and the π bootstrap

Derived theorems for candidate `V5`: copied verbatim from `V4`, namespace
renamed. Theorems and lemmas only — no `axiom`,
no `sorry`, no oracle.

## 1. The global cubic

`ψ t := t ^ 3 / 6 - t + sin t` has `ψ 0 = 0` and

    ψ' t = 3 * t ^ 2 / 6 - 1 + cos t = t ^ 2 / 2 - 1 + cos t ≥ 0

for **every** real `t`, by `Real.one_sub_sq_div_two_lt_cos` (plus a trivial
`t = 0` branch, where `ψ' 0 = 0`). So `ψ` is monotone on all of `ℝ` by
`monotone_of_hasDerivAt_nonneg` and `ψ x ≥ ψ 0 = 0` for `x ≥ 0`, i.e.

    x - sin x ≤ x ^ 3 / 6   for every x ≥ 0,

with **no** upper restriction on `x`. This replaces the Mathlib cubic that `V0`
and `V1` used (`x - x ^ 3 / 4 < sin x`, valid only on `0 < x ≤ 1`) on two counts
at once: the constant is sharp, and the domain hypothesis disappears.

## 2. The uniform deficit bound

With `N = 2 ^ (n + 2)` and `x = π / N`, `polygonLower n = N * sin x` and
`N * x = π`, so

    π - polygonLower n = N * (x - sin x) ≤ N * x ^ 3 / 6
                       = π ^ 3 / (6 * N ^ 2) = π ^ 3 / (6 * 4 ^ (n + 2))
                       = π ^ 3 / (96 * 4 ^ n).

The `n` cancels exactly; there is no per-`n` case analysis and no interval
hypothesis anywhere. The whole upper side of the scored contract is now the
single numeric question `π ^ 3 / 96 < kappa`.

## 3. The bootstrap

`deficit_le` is proved outright with `π ^ 3` symbolic. Only *afterwards* is a
numeric hypothesis `π ≤ c` substituted, at depth `2`, to give

    π ≤ 31214464/10000000 + c ^ 3 / 1536,

where `31214464/10000000` is a certified rational upper bound for
`polygonLower 2 = 8 √(2 - √(2 + √2))`. That is a contraction on `c`, so
iterating it from `Real.pi_le_four` sharpens `π` to its fixed point at depth
`2`: `4 → 3.1631131 → 3.1420505 → 3.1416417 → 3.1416338 → 3.1416336`. Five
rounds already reach the fixed point of the rounded iteration, giving
`π ^ 3 / 96 < 0.3229947` against the true value `0.32298205`. Nothing here is
circular: `deficit_le` never mentions any numeric bound on `π`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open PolygonCore

/-! ### 1. The global cubic Taylor bound -/

/-- The derivative of `ψ t = t ^ 3 / 6 - t + sin t`, in the raw shape the
`HasDerivAt` combinators produce, is non-negative on **all** of `ℝ`. -/
lemma psiDeriv_nonneg (x : ℝ) : 0 ≤ 3 * x ^ 2 / 6 - 1 + Real.cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · linarith [Real.one_sub_sq_div_two_lt_cos hx]

lemma hasDerivAt_psi (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3 / 6 - t + Real.sin t)
      (3 * x ^ 2 / 6 - 1 + Real.cos x) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  exact ((hpow.div_const 6).sub (hasDerivAt_id' (x := x))).add (Real.hasDerivAt_sin x)

lemma psi_monotone : Monotone (fun t : ℝ => t ^ 3 / 6 - t + Real.sin t) :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_psi fun x => psiDeriv_nonneg x

/-- **The sharp global cubic.** For every `x ≥ 0`, `x - sin x ≤ x ^ 3 / 6`.
No upper bound on `x` is needed. -/
theorem sub_sin_le_cube_div_six (x : ℝ) (hx : 0 ≤ x) :
    x - Real.sin x ≤ x ^ 3 / 6 := by
  have h := psi_monotone hx
  simp only [Real.sin_zero] at h
  norm_num at h
  linarith

/-! ### 2. The uniform, domain-free deficit bound -/

/-- **The deficit bound.** `π - polygonLower n ≤ π ^ 3 / (96 * 4 ^ n)` for every
`n`, uniformly: the `n` cancels algebraically out of the cubic. -/
theorem deficit_le (n : ℕ) :
    Real.pi - polygonLower n ≤ Real.pi ^ 3 / (96 * 4 ^ n) := by
  have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (0 : ℝ) ≤ Real.pi / 2 ^ (n + 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (sub_sin_le_cube_div_six (Real.pi / 2 ^ (n + 2)) hx) hN.le
  have hxN : (2 : ℝ) ^ (n + 2) * (Real.pi / 2 ^ (n + 2)) = Real.pi := by
    field_simp
  have hL : (2 : ℝ) ^ (n + 2) *
      (Real.pi / 2 ^ (n + 2) - Real.sin (Real.pi / 2 ^ (n + 2)))
      = Real.pi - polygonLower n := by
    rw [polygonLower_eq_mul_sin, mul_sub, hxN]
  have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
  have hR : (2 : ℝ) ^ (n + 2) * ((Real.pi / 2 ^ (n + 2)) ^ 3 / 6)
      = Real.pi ^ 3 / (96 * 4 ^ n) := by
    rw [hpow, h4n]
    field_simp
    ring
  rw [hL, hR] at hmul
  exact hmul

/-! ### 3. Staged rational certification of `polygonLower 2`, from above

The direction is the mirror image of the one the lower conjunct uses: an
*upper* bound on `polygonLower 2 = 8 √(2 - √(2 + √2))` needs a *lower* bound on
the inner radical's argument, hence *lower* bounds on `√2` and `√(2 + √2)`.
Each stage is one `nlinarith` with the square identity, the sign, and the
previous stage as hints; the nested expression is never handed to a single call.
-/

/-- `√2 > 1.4142135`, since `1.4142135 ^ 2 = 1.99999982358… < 2`. -/
lemma sqrt_two_gt : (14142135/10000000 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√2 < 2`. Used by both directions of the certification, so it lives here
rather than beside the `V1`-direction lemmas in the candidate file. -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√(2 + √2) < 2`, needed only so that `2 - √(2 + √2) ≥ 0`. -/
lemma sqrt_two_add_sqrt_two_lt_two : Real.sqrt (2 + Real.sqrt 2) < 2 := by
  have hnn : (0:ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrt 2), sqrt_two_lt_two]

/-- `√(2 + √2) > 1.8477590`, since
`1.8477590 ^ 2 = 3.41421332… < 3.4142135 < 2 + √2`. -/
lemma sqrt_two_add_sqrt_two_gt :
    (18477590/10000000 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
  have hnn : (0:ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrt 2), sqrt_two_gt]

/-- `√(2 - √(2 + √2)) < 0.3901808`, since
`0.3901808 ^ 2 = 0.15224106… > 0.1522410 > 2 - √(2 + √2)`. -/
lemma sqrt_two_sub_lt :
    Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) < 3901808/10000000 := by
  have hnn : (0:ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith [sqrt_two_add_sqrt_two_lt_two]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2)),
    sqrt_two_add_sqrt_two_gt]

lemma polygonLower_two_eq :
    polygonLower 2 = 8 * Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  rw [polygonLower, Real.sqrtTwoAddSeries_two]
  norm_num

/-- `polygonLower 2 < 3.1214464` (true value `3.12144515…`). -/
lemma polygonLower_two_lt : polygonLower 2 < 31214464/10000000 := by
  rw [polygonLower_two_eq]
  linarith [sqrt_two_sub_lt]

/-! ### 4. The bootstrap

`pi_le_bootstrap_step` is the deficit bound at depth `2` with a numeric
hypothesis substituted for `π ^ 3`. It is stated for an arbitrary `c` so that it
can be applied repeatedly, each application producing a strictly better `c`.
-/

/-- **The bootstrap step.** Any rational (or real) upper bound `c` for `π` is
sharpened by feeding it back through the depth-`2` deficit bound. -/
theorem pi_le_bootstrap_step (c : ℝ) (hc : Real.pi ≤ c) :
    Real.pi ≤ 31214464/10000000 + c ^ 3 / 1536 := by
  have h : Real.pi - polygonLower 2 ≤ Real.pi ^ 3 / 1536 := by
    have h0 := deficit_le 2
    norm_num at h0
    linarith
  have h3 : Real.pi ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ Real.pi_pos.le hc 3
  linarith [polygonLower_two_lt]

lemma pi_le_round_one : Real.pi ≤ 31631131/10000000 := by
  have h := pi_le_bootstrap_step 4 Real.pi_le_four
  norm_num at h
  linarith

lemma pi_le_round_two : Real.pi ≤ 31420505/10000000 := by
  have h := pi_le_bootstrap_step _ pi_le_round_one
  norm_num at h
  linarith

lemma pi_le_round_three : Real.pi ≤ 31416417/10000000 := by
  have h := pi_le_bootstrap_step _ pi_le_round_two
  norm_num at h
  linarith

lemma pi_le_round_four : Real.pi ≤ 31416338/10000000 := by
  have h := pi_le_bootstrap_step _ pi_le_round_three
  norm_num at h
  linarith

/-- After five bootstrap rounds the rounded iteration has reached its fixed
point: `π ≤ 3.1416336`. -/
theorem pi_le_round_five : Real.pi ≤ 31416336/10000000 := by
  have h := pi_le_bootstrap_step _ pi_le_round_four
  norm_num at h
  linarith

/-- **The single number the upper side of the contract reduces to.**
`π ^ 3 / 96 < 0.3229947` (true value `0.32298205…`). -/
theorem pi_cube_div_lt : Real.pi ^ 3 / 96 < 3229947/10000000 := by
  have h3 : Real.pi ^ 3 ≤ (31416336/10000000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ Real.pi_pos.le pi_le_round_five 3
  norm_num at h3 ⊢
  linarith

end ProofRefinement.PolygonPi.Candidates.V5
