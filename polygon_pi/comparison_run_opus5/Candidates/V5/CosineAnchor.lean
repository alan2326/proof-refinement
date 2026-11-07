import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V5.QuinticDeficit

/-!
# The cosine anchor: a second, independent route from the nested radical to `π`

Derived theorems for candidate `V5`: copied verbatim from `V4`, namespace
renamed. Theorems and lemmas only — no `axiom`,
no `sorry`, no oracle.

Every numeric bound on `π` in `V1`–`V3` came from one place: the *sine* anchor
`polygonLower n = 2 ^ (n+2) sin (π / 2 ^ (n+2))`, i.e.
`sin (π / 2 ^ (n+2)) = √(2 - s_n) / 2`, used at depth `2`. That choice has two
costs which have never been questioned.

1. **It forces an iteration.** `π ≤ p₂⁺ + π ^ 3 / 1536` is self-referential, so
   `V2` needed five bootstrap rounds, and the fixed point is pinned `4.1e-5`
   above `π` by the truncation error of the Taylor bound *at depth 2*.
2. **It is badly conditioned.** `√(2 - s_n)` subtracts two nearly equal
   quantities (`2 - s₂ = 0.152…`, `2 - s₄ = 0.0096…`), so the certification
   error *grows* by roughly two decimal digits per extra level. That is why no
   sprint went deeper than depth `2`.

This file uses the *cosine* anchor instead,

    cos (π / 2 ^ (k+1)) = sqrtTwoAddSeries 0 k / 2        (`Real.cos_pi_over_two_pow`)

at `k = 5`, i.e. `cos (π / 64) = s₅ / 2`. Neither cost survives.

* `s_k` is built by `+`-nesting only (`s_{k+1} = √(2 + s_k)`), so the
  certification error **contracts** by a factor `≈ 4` per level. Twelve decimal
  places at `√2` still leave `9.8e-13` of margin at `s₅` — no extra digits are
  needed going outward, and this is the structural claim the sprint tests.
  Measured margins `2 + a_{k-1} - a_k ^ 2`, from
  `Scratch/cosine_anchor_v4.py`:
  `2.69e-13`, `2.02e-12`, `1.23e-12`, `1.11e-12`, `9.84e-13`.
* Inverting `cos` through the **already proved** global quartic
  `cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24` (`QuinticDeficit.lean`'s
  `cos_le_quartic`, here used at full strength for the first time — `V3` proved
  it globally and then only ever consumed it as a derivative sign) gives a plain
  quartic inequality in `π` that is solved in **one** step: the quartic is
  antitone on `[0, 1/16]`, so a lower bound on `cos (π/64)` is directly an upper
  bound on `π/64`. There is no fixed point and no iteration anywhere.

The result is `π ≤ 3.1415926848`, `3.12e-8` above `π`, against the incumbent
bootstrap's `3.1416336`. Of that `3.12e-8`, the quartic truncation at
`y = π/64` contributes `y ^ 6 / 720 = 1.9e-11` amplified by
`1 / sin(π/64) · 64`, i.e. `2.5e-8`; the radical certification contributes
`< 4e-10`; the rest is rounding to a ten-digit literal. The Taylor *order*,
which sprints 002 and 003 both attacked, has stopped mattering: at depth 5 the
quartic is three orders of magnitude sharper than a septic rung would be at
depth 2.

Nothing in this file mentions `polygonLower`, `deficit_le`, `deficit_ge`, or
either bootstrap. The only import it consumes is `cos_le_quartic`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open PolygonCore

/-! ### 1. The outward recursion of the `+`-nested radical

`Real.sqrtTwoAddSeries_succ` peels the series from the *inside*
(`x.sqrtTwoAddSeries (n+1) = (√(2 + x)).sqrtTwoAddSeries n`), which is the wrong
end for a staged certification. The outward form is definitional. -/

lemma series_succ (n : ℕ) :
    Real.sqrtTwoAddSeries 0 (n + 1) = Real.sqrt (2 + Real.sqrtTwoAddSeries 0 n) :=
  rfl

lemma series_two : Real.sqrtTwoAddSeries 0 2
    = Real.sqrt (2 + Real.sqrtTwoAddSeries 0 1) := series_succ 1

lemma series_three : Real.sqrtTwoAddSeries 0 3
    = Real.sqrt (2 + Real.sqrtTwoAddSeries 0 2) := series_succ 2

lemma series_four : Real.sqrtTwoAddSeries 0 4
    = Real.sqrt (2 + Real.sqrtTwoAddSeries 0 3) := series_succ 3

lemma series_five : Real.sqrtTwoAddSeries 0 5
    = Real.sqrt (2 + Real.sqrtTwoAddSeries 0 4) := series_succ 4

/-! ### 2. Five-stage lower certification at twelve decimal places

One `nlinarith` per radical level, one multiplication per call, exactly the rule
sprint 002 recorded. The hints are always the same three: the square identity
for the current radical, its non-negativity, and the previous stage. -/

/-- `s₁ = √2 > 1.414213562373`. Margin `2 - a₁ ^ 2 = 2.69e-13`.
True value `1.414213562373095…`. -/
theorem s1_gt : (1414213562373/1000000000000 : ℝ) < Real.sqrtTwoAddSeries 0 1 := by
  rw [Real.sqrtTwoAddSeries_one]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `s₂ > 1.847759065022`. Margin `(2 + a₁) - a₂ ^ 2 = 2.02e-12`.
True value `1.847759065022573…`. -/
theorem s2_gt : (1847759065022/1000000000000 : ℝ) < Real.sqrtTwoAddSeries 0 2 := by
  have hprev := s1_gt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 1 := by linarith
  rw [series_two]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 1), hprev]

/-- `s₃ > 1.961570560806`. Margin `(2 + a₂) - a₃ ^ 2 = 1.23e-12`.
True value `1.961570560806460…`. -/
theorem s3_gt : (1961570560806/1000000000000 : ℝ) < Real.sqrtTwoAddSeries 0 3 := by
  have hprev := s2_gt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 2 := by linarith
  rw [series_three]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 2), hprev]

/-- `s₄ > 1.990369453344`. Margin `(2 + a₃) - a₄ ^ 2 = 1.11e-12`.
True value `1.990369453344393…`. -/
theorem s4_gt : (1990369453344/1000000000000 : ℝ) < Real.sqrtTwoAddSeries 0 4 := by
  have hprev := s3_gt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 3 := by linarith
  rw [series_four]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 3), hprev]

/-- `s₅ > 1.997590912410`. Margin `(2 + a₄) - a₅ ^ 2 = 9.84e-13`.
True value `1.997590912410344…`. The error has **contracted** at every stage;
compare the `+2` decimal digits per level that the `√(2 - ·)` chain of
`V3/QuinticDeficit.lean` costs. -/
theorem s5_gt : (1997590912410/1000000000000 : ℝ) < Real.sqrtTwoAddSeries 0 5 := by
  have hprev := s4_gt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 4 := by linarith
  rw [series_five]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 4), hprev]

/-! ### 3. The anchor -/

/-- The anchor identity at depth `5`, with the power evaluated:
`cos (π / 64) = s₅ / 2`. -/
lemma cos_pi_div_64_eq : Real.cos (Real.pi / 64) = Real.sqrtTwoAddSeries 0 5 / 2 := by
  have h := Real.cos_pi_over_two_pow 5
  have h64 : Real.pi / 2 ^ (5 + 1) = Real.pi / 64 := by norm_num
  rwa [h64] at h

/-- **The cosine anchor.** `cos (π / 64) > 0.998795456205`, from the five-stage
radical certification alone. True value `0.99879545620517239…`; the certified
bound is `1.72e-13` below it. -/
theorem cos_pi_div_64_gt :
    (998795456205/1000000000000 : ℝ) < Real.cos (Real.pi / 64) := by
  rw [cos_pi_div_64_eq]
  linarith [s5_gt]

/-! ### 4. The quartic is antitone on `[0, 1/16]`

    (1 - a²/2 + a⁴/24) - (1 - b²/2 + b⁴/24) = (b² - a²) * (1/2 - (a² + b²)/24),

and both factors are non-negative when `0 ≤ a ≤ b ≤ 1/16`, since then
`a² + b² ≤ 2/256 ≪ 12`. After ring normalisation the product hint *is* the
goal, so `nlinarith` has no search to do. -/

lemma quartic_antitone {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 16) :
    1 - b ^ 2 / 2 + b ^ 4 / 24 ≤ 1 - a ^ 2 / 2 + a ^ 4 / 24 := by
  have h1 : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 / 2 - (a ^ 2 + b ^ 2) / 24 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-! ### 5. The inversion — one step, no bootstrap

Write `h y := 1 - y ^ 2 / 2 + y ^ 4 / 24` and `r := 0.0490873857`, so
`64 r = 3.1415926848`. Suppose `π > 64 r`. Then `r ≤ π/64 ≤ 1/16` (the upper
end from `Real.pi_le_four`), so

    L < cos (π/64) ≤ h (π/64) ≤ h r < L,

where the first inequality is the anchor, the second is the global quartic, the
third is antitonicity, and the fourth is a comparison of two exact rationals
(margin `4.33e-12`). Contradiction. -/

/-- **The sharp upper bound on `π`, without any iteration.**
`π ≤ 3.1415926848`; the true value is `3.14159265358979…`, so this is `3.12e-8`
high, against the depth-2 bootstrap's `4.1e-5`. -/
theorem pi_le_sharp : Real.pi ≤ 31415926848/10000000000 := by
  by_contra hcon
  push_neg at hcon
  have hy1 : Real.pi / 64 ≤ 1 / 16 := by linarith [Real.pi_le_four]
  have hy0 : (0:ℝ) ≤ 490873857/10000000000 := by norm_num
  have hab : (490873857/10000000000 : ℝ) ≤ Real.pi / 64 := by linarith
  have hanti := quartic_antitone hy0 hab hy1
  have hq := cos_le_quartic (Real.pi / 64)
  have hr : 1 - (490873857/10000000000 : ℝ) ^ 2 / 2
      + (490873857/10000000000 : ℝ) ^ 4 / 24
      < 998795456205/1000000000000 := by norm_num
  linarith [cos_pi_div_64_gt]

/-! ### 6. The single number the upper side of the contract reduces to -/

/-- `π ^ 3 / 96 < 0.32298206`, against the permanent floor
`π ^ 3 / 96 = 0.32298204875…`. Margin `1.62e-9`. -/
theorem pi_cube_div_lt_sharp : Real.pi ^ 3 / 96 < 32298206/100000000 := by
  have h3 : Real.pi ^ 3 ≤ (31415926848/10000000000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ Real.pi_pos.le pi_le_sharp 3
  have hb : ((31415926848/10000000000 : ℝ)) ^ 3 < 96 * (32298206/100000000) := by
    norm_num
  linarith

/-! ### 7. The depth-3 lower anchor (new in `V5`)

The lower conjunct's ceiling is `π - 2√2`, so the only thing that can widen
`lambda` is a sharper *lower* bound on `π`. `V3`'s bootstrap gave
`π ≥ 3.141592597`, and its `5.8e-8` of slack is not rounding: the depth-2
quintic truncation `16 · x ⁷ / 5040` at `x = π/16` is `3.62e-8` and pins the
depth-2 fixed point there however many rounds are run. Moving to **depth 3**
cuts that term to `5.6e-10`.

Depth 3 also needs no iteration at all. `deficit_ge 3` reads

    π  ≥  polygonLower 3 + π ^ 3 / 6144 − π ^ 5 / 125829120,

and both correction terms can be supplied outright from bounds already in the
file — `pi_ge_round_five` for the `π ^ 3` term (which only needs nine digits of
`π` to give twelve of `π ^ 3 / 6144`) and `pi_le_sharp`, weakened to
`π ≤ 3.1415927`, for the `π ^ 5` term. Nothing is circular and nothing is
self-referential.

The cost is the one thing sprint 004 warned about: the radical
`√(2 − s₃)` is on the badly-conditioned `2 − ·` side, so the outer stage loses
digits. It is affordable here because the three *inner* stages are on the
well-conditioned `+`-nested chain and, in the upper direction, twelve decimal
places carry through with margins `2.56e-12`, `6.71e-13`, `1.69e-12`; the outer
subtraction then still leaves `2.93e-13`. This is the mirror image of §2 (which
certifies the same `s_k` from below) and reuses `series_two` / `series_three`
unchanged.
-/

/-- `s₁ = √2 < 1.414213562374`. Margin `a₁ ^ 2 - 2 = 2.56e-12`.
True value `1.414213562373095…`. -/
theorem s1_lt : Real.sqrtTwoAddSeries 0 1 < 1414213562374/1000000000000 := by
  rw [Real.sqrtTwoAddSeries_one]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `√2 < 1.414213562374`, the same bound with the series unfolded. -/
theorem sqrt_two_lt_sharp : Real.sqrt 2 < 1414213562374/1000000000000 := by
  have h := s1_lt
  rwa [Real.sqrtTwoAddSeries_one] at h

/-- `s₂ < 1.847759065023`. Margin `a₂ ^ 2 - (2 + a₁) = 6.71e-13`.
True value `1.847759065022573…`. -/
theorem s2_lt : Real.sqrtTwoAddSeries 0 2 < 1847759065023/1000000000000 := by
  have hprev := s1_lt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 1 := by linarith [s1_gt]
  rw [series_two]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 1), hprev]

/-- `s₃ < 1.961570560807`. Margin `a₃ ^ 2 - (2 + a₂) = 1.69e-12`.
True value `1.961570560806460…`. -/
theorem s3_lt : Real.sqrtTwoAddSeries 0 3 < 1961570560807/1000000000000 := by
  have hprev := s2_lt
  have hnn : (0:ℝ) ≤ 2 + Real.sqrtTwoAddSeries 0 2 := by linarith [s2_gt]
  rw [series_three]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (2 + Real.sqrtTwoAddSeries 0 2), hprev]

/-- The outer, badly-conditioned stage: `√(2 - s₃) > 0.196034280657`.
`2 - s₃ = 0.0384294391935…` cancels a leading digit, and the margin
`(2 - a₃) - c ^ 2 = 2.93e-13` is what survives.
True value `0.19603428065912…`. -/
theorem sqrt_two_sub_s3_gt :
    (196034280657/1000000000000 : ℝ) < Real.sqrt (2 - Real.sqrtTwoAddSeries 0 3) := by
  have hnn : (0:ℝ) ≤ 2 - Real.sqrtTwoAddSeries 0 3 := by linarith [s3_lt]
  nlinarith [s3_lt, Real.sq_sqrt hnn,
    Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 3)]

/-- `polygonLower 3 = 16 √(2 - s₃)`: the 32-gon. The power is rewritten
separately so that `norm_num` never sees the `sqrtTwoAddSeries` argument and
cannot fire its simp set on it. -/
lemma polygonLower_three_eq :
    polygonLower 3 = 16 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 3) := by
  have h : (2:ℝ) ^ (3 + 1) = 16 := by norm_num
  rw [polygonLower, h]

/-- `polygonLower 3 > 3.136548490512` (true value `3.13654849054593…`).
`16 · 0.196034280657 = 3.136548490512` exactly, and the strictness is the
radical bound's. -/
theorem polygonLower_three_gt :
    (3136548490512/1000000000000 : ℝ) < polygonLower 3 := by
  rw [polygonLower_three_eq]
  linarith [sqrt_two_sub_s3_gt]

/-- The `π ^ 5` correction at depth 3, from `pi_le_sharp` weakened to seven
digits. Raising the eleven-digit literal to the fifth power would make 55-digit
intermediates for a bound that needs seven; `3.1415927` costs `9e-14` of the
`2.43e-6` term and saves all of that. True value `2.4320261…e-6`. -/
theorem pi_pow_five_div_depth_three_lt :
    Real.pi ^ 5 / 125829120 < 2432027/1000000000000 := by
  have h : Real.pi ≤ 31415927/10000000 := pi_le_sharp.trans (by norm_num)
  have h5 : Real.pi ^ 5 ≤ (31415927/10000000 : ℝ) ^ 5 :=
    pow_le_pow_left₀ Real.pi_pos.le h 5
  have hb : ((31415927/10000000 : ℝ)) ^ 5 < 125829120 * (2432027/1000000000000) := by
    norm_num
  linarith

/-- The `π ^ 3` correction at depth 3, from `pi_ge_round_five`. Nine digits of
`π` give twelve of `π ^ 3 / 6144`. True value `0.00504659450…`. -/
theorem pi_cube_div_6144_gt :
    (5046594239/1000000000000 : ℝ) < Real.pi ^ 3 / 6144 := by
  have h3 : ((3141592597/1000000000 : ℝ)) ^ 3 ≤ Real.pi ^ 3 :=
    pow_le_pow_left₀ (by norm_num) pi_ge_round_five 3
  have hb : (6144 : ℝ) * (5046594239/1000000000000)
      < ((3141592597/1000000000 : ℝ)) ^ 3 := by norm_num
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 6144)]
  linarith

/-- **π from the 32-gon, in one step.** `π ≥ 3.141592652724`; the true value is
`3.14159265358979…`, so this is `8.66e-10` low, against the depth-2 bootstrap's
`5.8e-8`.

    π  ≥  3.136548490512 + 0.005046594239 − 0.000002432027  =  3.141592652724.
-/
theorem pi_ge_depth_three : (3141592652724/1000000000000 : ℝ) ≤ Real.pi := by
  have h := deficit_ge 3
  norm_num at h
  linarith [polygonLower_three_gt, pi_cube_div_6144_gt,
    pi_pow_five_div_depth_three_lt]

end ProofRefinement.PolygonPi.Candidates.V5
