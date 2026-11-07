-- @parent V3
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V4.DeficitMonotone
import ProofRefinement.PolygonPi.Candidates.V4.CubicDeficit
import ProofRefinement.PolygonPi.Candidates.V4.QuinticDeficit
import ProofRefinement.PolygonPi.Candidates.V4.CosineAnchor

/-!
# V4 — a cosine anchor, and the end of the bootstrap

`lambda = 313165471/1000000000`, `kappa = 32298206/100000000`, score
`9816589/1000000000 = 0.009816589`, against the parent `V3`'s `0.0098297` and
the theoretical optimum of the whole problem,
`π ^ 3 / 96 - (π - 2√2) = 0.00981651991…`.

## The upper side (new)

`V1`–`V3` all extracted the numeric value of `π` from the polygon *deficit* at
depth `2`, through the sine anchor `sin (π / 2 ^ (n+2)) = √(2 - s_n) / 2`. That
anchor makes the bound self-referential (`π ≤ p₂⁺ + π ^ 3 / 1536`), so it had to
be bootstrapped, and it is badly conditioned, since `√(2 - s_n)` cancels a
leading digit at every level — which is why no sprint ever went past depth `2`,
and why the bootstrap's fixed point sits `4.1e-5` above `π`.

`Candidates/V4/CosineAnchor.lean` replaces it with the *cosine* anchor
`cos (π / 2 ^ (k+1)) = s_k / 2` at `k = 5`. The `+`-nested `s_k` is
well conditioned — the certification error contracts by `≈ 4` per level, so
twelve decimal places at `√2` still leave `9.8e-13` of margin at `s₅` — and
inverting `cos` through `V3`'s own global quartic
`cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24` needs no iteration at all: the quartic is
antitone on `[0, 1/16]`, so

    0.998795456205 < cos (π/64) ≤ 1 - (π/64) ^ 2 / 2 + (π/64) ^ 4 / 24

inverts in one step to `π ≤ 3.1415926848`, `3.12e-8` above `π`. Hence

    π ^ 3 / 96 < 0.32298206,

against the permanent floor `π ^ 3 / 96 = 0.32298204875…`: `kappa` is now
`1.6e-9` above a quantity it can never reach, down from `V3`'s `1.27e-5`.

Note what has *not* been used: no `polygonLower`, no `deficit_le`, no
bootstrap round appears anywhere in `pi_le_sharp`'s proof. `cos_le_quartic` is
the one thing carried over, and it is used at full strength for the first time —
`V3` proved it globally and then only ever consumed it as a derivative sign.
The Taylor *order* that sprints 002 and 003 both attacked has stopped mattering:
at `y = π/64` the quartic's truncation error `y ^ 6 / 720 = 1.9e-11` is three
orders of magnitude better than a septic rung would buy at depth `2`.

## The lower side (free)

No new mathematics. `V3` already proved `pi_ge_round_five : π ≥ 3.141592597`
and `sqrt_two_lt : √2 < 1.414213563`, and
`3.141592597 - 2 · 1.414213563 = 0.313165471` exactly, with strictness supplied
by the `√2` bound; `V3` simply spent those lemmas on a six-digit literal and
left `4.71e-7` of proved headroom on the table. `lambda_lt_deficit_zero` is
unchanged apart from the literal. The exact ceiling is
`π - 2√2 = 0.31316552884…`, attained at `n = 0`, so the lower side is now
`5.8e-8` from a bound it can never exceed.

## Where that leaves the problem

Both sides are within `1e-7` of ceilings that are now proved to be permanent:
`4 ^ n (π - polygonLower n) ↗ π ^ 3 / 96` from below, so no admissible `kappa`
lies under `0.32298204875…`; and the lower conjunct is binding and attained at
`n = 0`, so no admissible `lambda` exceeds `0.31316552884…`. The remaining
score gap is `7e-8` and every part of it is decimal digits.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V4

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, `5.8e-8` below the exact ceiling `π - 2√2`. -/
def lambda : ℝ := 313165471/1000000000

/-- Upper error coefficient, `1.6e-9` above the analytic floor `π ^ 3 / 96`. -/
def kappa : ℝ := 32298206/100000000

lemma polygonLower_zero_eq : polygonLower 0 = 2 * Real.sqrt 2 := by
  simp [polygonLower]

/-- The exact ceiling for `lambda`, certified from below by the nine-digit
bootstrapped lower bound on `π` and the nine-digit upper bound on `√2`. -/
lemma lambda_lt_deficit_zero : lambda < Real.pi - polygonLower 0 := by
  rw [polygonLower_zero_eq, lambda]
  linarith [sqrt_two_lt, pi_ge_round_five]

/-! ### The scored contract -/

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- Lower conjunct: monotonicity of the scaled deficit reduces it to `n = 0`.
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hd : Real.pi - polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n) :=
      deficit_ge_zero_deficit n
    have hlt : lambda / 4 ^ n < Real.pi - polygonLower n := by
      rw [div_lt_iff₀' h4n]
      linarith [lambda_lt_deficit_zero]
    linarith
  · -- Upper conjunct: the uniform cubic deficit bound plus the cosine-anchored
    -- numeric bound on `π ^ 3 / 96`.
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hscaled : (Real.pi - polygonLower n) * 4 ^ n ≤ Real.pi ^ 3 / 96 := by
      calc (Real.pi - polygonLower n) * 4 ^ n
          ≤ Real.pi ^ 3 / (96 * 4 ^ n) * 4 ^ n :=
            mul_le_mul_of_nonneg_right (deficit_le n) h4n.le
        _ = Real.pi ^ 3 / 96 := by field_simp
    have hstrict : (Real.pi - polygonLower n) * 4 ^ n < kappa := by
      rw [kappa]
      exact lt_of_le_of_lt hscaled pi_cube_div_lt_sharp
    have : Real.pi - polygonLower n < kappa / 4 ^ n := by
      rw [lt_div_iff₀ h4n]
      exact hstrict
    linarith

end ProofRefinement.PolygonPi.Candidates.V4
