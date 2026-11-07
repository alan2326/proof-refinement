import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V5.CubicDeficit

/-!
# The quintic Taylor bound, the uniform *lower* deficit bound, and the π bootstrap

Derived theorems for candidate `V5`: copied verbatim from `V4`, namespace
renamed. Theorems and lemmas only — no `axiom`,
no `sorry`, no oracle.

`V2` gave the upper side its own analytic ingredient (the global cubic
`x - sin x ≤ x ^ 3 / 6`, hence `π - polygonLower n ≤ π ^ 3 / (96 · 4 ^ n)`) and
left the lower side with nothing but a rational certification of
`polygonLower 2`. This file supplies the missing companion: a *lower* bound on
the deficit, uniform in `n`, from the next Taylor rung in the opposite
direction.

## 1. `cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24`, globally

No second derivative and no `MonotoneOn` is needed: the half-angle identity
turns this into the cubic sine bound `CubicDeficit.lean` already proves. If
`12 ≤ t ^ 2` the right-hand side is already `≥ 1 ≥ cos t`, since
`1 - t ^ 2 / 2 + t ^ 4 / 24 - 1 = t ^ 2 (t ^ 2 - 12) / 24`. Otherwise write
`t = 2 u` with `u ^ 2 < 3`; then `u - u ^ 3 / 6` is non-negative and below
`sin u`, so squaring is monotone, and `cos t = 1 - 2 sin u ^ 2` gives

    cos t ≤ 1 - 2 (u - u ^ 3 / 6) ^ 2 = 1 - 2u² + 2u⁴/3 - u⁶/18
          ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24.

Both sides are even, so the negative branch is the positive one at `-t`.

## 2. `sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120` for `x ≥ 0`

With step 1 in hand the cheap global idiom applies again:
`χ t := t - t ^ 3 / 6 + t ^ 5 / 120 - sin t` has

    χ' t = 1 - 3 t ^ 2 / 6 + 5 t ^ 4 / 120 - cos t ≥ 0

on **all** of `ℝ`, so `monotone_of_hasDerivAt_nonneg` applies with no
`ContinuousOn`, no `interior` and no `Convex` side goal.

## 3. The uniform lower deficit bound

The same `n`-cancellation as `deficit_le`, with the inequality reversed:

    π - polygonLower n ≥ π ^ 3 / (96 · 4 ^ n) - π ^ 5 / (30720 · 4 ^ n · 4 ^ n).

Stated with `4 ^ n * 4 ^ n` rather than `16 ^ n` so the `field_simp; ring`
normalisation is the one already known to work.

## 4. The lower bootstrap

`deficit_ge` is proved with `π ^ 3` and `π ^ 5` symbolic; only afterwards are
numeric bounds substituted. At depth `2` it reads

    π ≥ polygonLower 2 + π ^ 3 / 1536 - π ^ 5 / 7864320,

so any *lower* bound `c ≤ π` gives the better `π ≥ p₂ + c ^ 3 / 1536 - ε`,
where `p₂ = 3.121445136` is a certified rational lower bound for
`polygonLower 2 = 8 √(2 - √(2 + √2))` and `ε = 3.891496e-5` is a certified
rational *upper* bound for `π ^ 5 / 7864320`, obtained from `V2`'s
`pi_le_round_five`. The `π ^ 5` correction is the only place where the two
sides of the workspace meet, and nothing is circular: `pi_le_round_five` never
mentions the quintic, and `deficit_ge` mentions no numeric bound on `π`.

Five rounds from the seed `polygonLower 2` reach

    3.121445136 → 3.1412067 → 3.14158515 → 3.14159244 → 3.14159259 → 3.141592597,

i.e. `π` to nine correct digits, from the polygon itself, with no radical
deeper than the one `V2` already certifies.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open PolygonCore

/-! ### 1. The global quartic cosine bound -/

/-- `cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24` for `t ≥ 0`, via the half-angle
identity and the cubic sine bound. -/
lemma cos_le_quartic_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  rcases le_or_gt 12 (t ^ 2) with h12 | h12
  · -- `1 - t ^ 2 / 2 + t ^ 4 / 24 - 1 = t ^ 2 * (t ^ 2 - 12) / 24 ≥ 0`
    nlinarith [Real.cos_le_one t, sq_nonneg t]
  · obtain ⟨u, rfl⟩ : ∃ u : ℝ, t = 2 * u := ⟨t / 2, by ring⟩
    have hu0 : 0 ≤ u := by linarith
    have hu2 : u ^ 2 < 3 := by nlinarith
    -- the cubic sine bound, rearranged
    have hs : u - u ^ 3 / 6 ≤ Real.sin u := by
      have h := sub_sin_le_cube_div_six u hu0
      linarith
    have hnn : 0 ≤ u - u ^ 3 / 6 := by
      have hp : 0 ≤ u * (6 - u ^ 2) :=
        mul_nonneg hu0 (by linarith)
      linarith
    have hsq : (u - u ^ 3 / 6) ^ 2 ≤ Real.sin u ^ 2 := pow_le_pow_left₀ hnn hs 2
    have hc : Real.cos (2 * u) = 1 - 2 * Real.sin u ^ 2 := by
      have h2 : Real.cos (2 * u) = 2 * Real.cos u ^ 2 - 1 := Real.cos_two_mul u
      have h3 : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
      linarith
    rw [hc]
    linarith [hsq, pow_nonneg hu0 6]

/-- **The global quartic cosine bound.** Both sides are even, so the sign of `t`
does not matter. -/
theorem cos_le_quartic (t : ℝ) : Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  rcases le_or_gt 0 t with ht | ht
  · exact cos_le_quartic_of_nonneg t ht
  · have h := cos_le_quartic_of_nonneg (-t) (by linarith)
    have e2 : (-t) ^ 2 = t ^ 2 := by ring
    have e4 : (-t) ^ 4 = t ^ 4 := by ring
    rw [Real.cos_neg, e2, e4] at h
    exact h

/-! ### 2. The global quintic Taylor bound on `sin` -/

/-- The derivative of `χ t = t - t ^ 3 / 6 + t ^ 5 / 120 - sin t`, in the raw
shape the `HasDerivAt` combinators produce, is non-negative on **all** of `ℝ`.
`3 * x ^ 2 / 6` and `x ^ 2 / 2` are the same linear multiple of the atom
`x ^ 2`, and likewise for `5 * x ^ 4 / 120` and `x ^ 4 / 24`, so `linarith`
sees step 1 directly. -/
lemma chiDeriv_nonneg (x : ℝ) :
    0 ≤ 1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - Real.cos x := by
  linarith [cos_le_quartic x]

lemma hasDerivAt_chi (x : ℝ) :
    HasDerivAt (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - Real.cos x) x := by
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h5 : HasDerivAt (fun t : ℝ => t ^ 5) (5 * x ^ 4) x := by
    simpa using hasDerivAt_pow 5 x
  exact (((hasDerivAt_id' (x := x)).sub (h3.div_const 6)).add
    (h5.div_const 120)).sub (Real.hasDerivAt_sin x)

lemma chi_monotone :
    Monotone (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_chi fun x => chiDeriv_nonneg x

/-- **The global quintic.** For every `x ≥ 0`,
`sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120`. No upper bound on `x` is needed, and
nothing numeric about `π` enters anywhere in the chain. -/
theorem sin_le_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := chi_monotone hx
  simp only [Real.sin_zero] at h
  norm_num at h
  linarith

/-! ### 3. The uniform, domain-free *lower* deficit bound -/

/-- **The lower deficit bound.** For every `n`,
`π ^ 3 / (96 · 4 ^ n) - π ^ 5 / (30720 · 4 ^ n · 4 ^ n) ≤ π - polygonLower n`.
The mirror image of `deficit_le`, with the same exact `n`-cancellation. -/
theorem deficit_ge (n : ℕ) :
    Real.pi ^ 3 / (96 * 4 ^ n) - Real.pi ^ 5 / (30720 * 4 ^ n * 4 ^ n)
      ≤ Real.pi - polygonLower n := by
  have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (0 : ℝ) ≤ Real.pi / 2 ^ (n + 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (sin_le_quintic (Real.pi / 2 ^ (n + 2)) hx) hN.le
  have hxN : (2 : ℝ) ^ (n + 2) * (Real.pi / 2 ^ (n + 2)) = Real.pi := by
    field_simp
  have hL : (2 : ℝ) ^ (n + 2) * Real.sin (Real.pi / 2 ^ (n + 2))
      = polygonLower n := by
    rw [polygonLower_eq_mul_sin]
  have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
  have hR : (2 : ℝ) ^ (n + 2) *
      (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6
        + (Real.pi / 2 ^ (n + 2)) ^ 5 / 120)
      = Real.pi - Real.pi ^ 3 / (96 * 4 ^ n)
        + Real.pi ^ 5 / (30720 * 4 ^ n * 4 ^ n) := by
    rw [hpow, h4n]
    field_simp
    ring
  rw [hL, hR] at hmul
  linarith

/-! ### 4. Nine-digit staged certification of the nested radical, *upper*
direction

The lower conjunct and the bootstrap seed both want `polygonLower 2` from
*below*, hence `√(2 - √(2 + √2))` from below, hence `√(2 + √2)` and `√2` from
*above* — the opposite direction to `CubicDeficit.lean`'s family, and at nine
digits rather than seven, because the error is amplified at the outer radical.
At eight digits the third stage is *false*.

One `nlinarith` per radical level, one multiplication per call, exactly as
sprint 002 recorded.
-/

/-- `√2 < 1.414213563`, since `1.414213563 ^ 2 = 2.000000001773… > 2`.
True value `1.41421356237…`. -/
lemma sqrt_two_lt : Real.sqrt 2 < 1414213563/1000000000 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√(2 + √2) < 1.847759066`, since
`1.847759066 ^ 2 = 3.414213565985… > 2 + 1.414213563`.
True value `1.84775906502…`. -/
lemma sqrt_two_add_sqrt_two_lt :
    Real.sqrt (2 + Real.sqrt 2) < 1847759066/1000000000 := by
  have hnn : (0:ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  nlinarith [sqrt_two_lt, Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrt 2)]

/-- `√(2 - √(2 + √2)) > 0.390180642`, since
`0.390180642 ^ 2 = 0.152240933… < 0.152240934 = 2 - 1.847759066`.
True value `0.39018064403…`. -/
lemma sqrt_two_sub_gt :
    (390180642/1000000000 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
  have hnn : (0:ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith [sqrt_two_add_sqrt_two_lt]
  nlinarith [sqrt_two_add_sqrt_two_lt, Real.sq_sqrt hnn,
    Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2))]

/-- `polygonLower 2 > 3.121445136` (true value `3.12144515226…`). -/
theorem polygonLower_two_gt : (3121445136/1000000000 : ℝ) < polygonLower 2 := by
  rw [polygonLower_two_eq]
  linarith [sqrt_two_sub_gt]

/-! ### 5. The lower bootstrap -/

/-- The one big-number lemma: the `π ^ 5` correction term, bounded above by
`V2`'s upper bound on `π`. True value `3.89122e-5`. -/
theorem pi_pow_five_div_lt : Real.pi ^ 5 / 7864320 < 3891496/100000000000 := by
  have h5 : Real.pi ^ 5 ≤ (31416336/10000000 : ℝ) ^ 5 :=
    pow_le_pow_left₀ Real.pi_pos.le pi_le_round_five 5
  have hb : ((31416336/10000000 : ℝ)) ^ 5
      < 7864320 * (3891496/100000000000) := by norm_num
  linarith

/-- **The lower bootstrap step.** Any rational (or real) lower bound `c` for `π`
is sharpened by feeding it back through the depth-`2` lower deficit bound. -/
theorem pi_ge_bootstrap_step (c : ℝ) (h0 : 0 ≤ c) (hc : c ≤ Real.pi) :
    3121445136/1000000000 + c ^ 3 / 1536 - 3891496/100000000000 ≤ Real.pi := by
  have h : Real.pi ^ 3 / 1536 - Real.pi ^ 5 / 7864320
      ≤ Real.pi - polygonLower 2 := by
    have h0' := deficit_ge 2
    norm_num at h0'
    linarith
  have h3 : c ^ 3 ≤ Real.pi ^ 3 := pow_le_pow_left₀ h0 hc 3
  linarith [polygonLower_two_gt, pi_pow_five_div_lt]

/-- The seed: the certified `polygonLower 2` together with the trusted
`polygonLower_lt_pi 2`. -/
lemma pi_ge_round_zero : (3121445136/1000000000 : ℝ) ≤ Real.pi :=
  (polygonLower_two_gt.trans (polygonLower_lt_pi 2)).le

lemma pi_ge_round_one : (31412067/10000000 : ℝ) ≤ Real.pi := by
  have h := pi_ge_bootstrap_step _ (by norm_num) pi_ge_round_zero
  norm_num at h
  linarith

lemma pi_ge_round_two : (62831703/20000000 : ℝ) ≤ Real.pi := by
  have h := pi_ge_bootstrap_step _ (by norm_num) pi_ge_round_one
  norm_num at h
  linarith

lemma pi_ge_round_three : (78539811/25000000 : ℝ) ≤ Real.pi := by
  have h := pi_ge_bootstrap_step _ (by norm_num) pi_ge_round_two
  norm_num at h
  linarith

lemma pi_ge_round_four : (314159259/100000000 : ℝ) ≤ Real.pi := by
  have h := pi_ge_bootstrap_step _ (by norm_num) pi_ge_round_three
  norm_num at h
  linarith

/-- **π to nine correct digits, from the polygon itself.**
`π ≥ 3.141592597` (true value `3.14159265358…`). No radical deeper than the
depth-2 one is certified anywhere in the chain. -/
theorem pi_ge_round_five : (3141592597/1000000000 : ℝ) ≤ Real.pi := by
  have h := pi_ge_bootstrap_step _ (by norm_num) pi_ge_round_four
  norm_num at h
  linarith

end ProofRefinement.PolygonPi.Candidates.V5
