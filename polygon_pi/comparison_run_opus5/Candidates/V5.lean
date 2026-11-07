-- @parent V4
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V5.DeficitMonotone
import ProofRefinement.PolygonPi.Candidates.V5.CubicDeficit
import ProofRefinement.PolygonPi.Candidates.V5.QuinticDeficit
import ProofRefinement.PolygonPi.Candidates.V5.CosineAnchor
import ProofRefinement.PolygonPi.Candidates.V5.Optimality

/-!
# V5 — the optimality certificate, and the closing of the frontier

`lambda = 313165527/1000000000` and `kappa = 32298206/100000000`, score
`9816533/1000000000 = 0.009816533` against `V4`'s `0.009816589`. The score moved
by `5.6e-8`, but that is the smaller half of the sprint.

## What is new

`V1`–`V4` each proved a statement about one candidate. `Candidates/V5/Optimality.lean`
proves statements about *all* of them, in both directions:

    ValidPolygonBound lam kap  →  0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 ≤ kap
    0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 < kap  →  ValidPolygonBound lam kap

(`admissible_lambda_lt`, `admissible_kappa_ge`, `valid_of_bracket`; the packaged
equivalence is `valid_iff_bracket_of_ne`). So the admissible set of the scored
contract is exactly

    { lam : 0 ≤ lam < π − 2√2 } × { kap : π ^ 3 / 96 < kap },

determined except at the single boundary point `kap = π ^ 3 / 96`. That point is
irrational, so no rational literal the evaluator accepts can sit on it; closing
the boundary case rigorously would need `4 ^ n (π − polygonLower n) < π ^ 3 / 96`
*strictly* for every `n`, i.e. a septic Taylor rung
`x − sin x ≤ x ³/6 − x ⁵/120 + x ⁷/5040`, and that was deliberately left open —
it cannot change which candidates exist.

Until now `π ^ 3 / 96` being a floor and `π − 2√2` a ceiling were **prose in a
docstring**, asserted by every sprint since `V1` and proved by none. They are
now theorems.

The upper half is the only genuinely new mathematics: `admissible_kappa_ge` is
*false at every finite depth* — for each `n` the scaled deficit
`D n = 4 ^ n (π − polygonLower n)` sits strictly below `π ^ 3 / 96`, and the
contract at depth `n` only forces `kap > D n`. What pushes `kap` over the floor
is `V3`'s quintic lower deficit bound used asymptotically for the first time
(it had only ever been a bootstrap input) plus an Archimedean step. The proof
carries `π ^ 3` and `π ^ 5` symbolically from start to finish; no decimal
literal appears anywhere in it, and every quantity cancels.

## What it says about the score

    inf { kappa − lambda : ValidPolygonBound lambda kappa }
      = π ^ 3 / 96 − (π − 2√2) = 0.009816519909519985…,   approached, not attained.

`optimum_gt` certifies that real number from below (`pi_ge_depth_three`,
`pi_le_sharp`, `s1_gt`), and the shipped score certifies it from above, giving
`optimum_bracket`:

    9816488/1000000000  <  π ^ 3 / 96 − (π − 2√2)  <  kappa − lambda
                                                   =  9816533/1000000000.

The benchmark's true optimum is therefore pinned to a window of width `4.5e-8`
(`optimality_gap_lt`), with the incumbent at its top edge. The incumbent's true
slack is `1.309e-8`; the remaining `3.2e-8` of the window is slack in the
*certification* of the floor, almost all of it `pi_le_sharp`'s quartic
truncation. `admissible_score_gt_rat` states the permanent part: **no candidate,
ever, scores below `0.009816488`.**

A correction to `V4`'s docstring and to sprint 004's `Experience.md` table,
which the exact arithmetic in `Scratch/optimality_certificate_v5.py` turns up:
`kappa = 0.32298206` is **`1.12e-8`** above the floor `0.322982048753…`, not
`1.6e-9`. The `1.6e-9` figure is the margin of `pi_cube_div_lt_sharp` against
the *certified* value `(3.1415926848) ^ 3 / 96 = 0.3229820584…`, not against the
floor. So the upper side, not the lower, still holds most of the remaining
score: `1.12e-8` of the `1.309e-8`.

## The second half of the sprint: the depth-3 lower anchor

`CosineAnchor.lean` §7 replaces `V3`'s depth-2 quintic bootstrap
(`π ≥ 3.141592597`, `5.8e-8` low) as the source of the lower side. At depth 2
the quintic truncation `16 · x ⁷/5040` at `x = π/16` is `3.62e-8` and pins that
bootstrap's fixed point there however many rounds are run; at depth 3 the same
term is `5.6e-10`. Depth 3 also needs **no iteration**, because both correction
terms in `deficit_ge 3` can be supplied outright from bounds already in the
file. Result: `π ≥ 3.141592652724`, `8.66e-10` low, hence
`lambda = 0.313165527` against the ceiling `0.313165528843…`.

The cost was the one thing sprint 004 warned about — the outer radical
`√(2 − s₃)` is on the badly-conditioned `2 − ·` side — and it was affordable
because the three inner stages are `+`-nested. Measured margins:
`2.56e-12`, `6.71e-13`, `1.69e-12` inward, `2.93e-13` at the subtraction.

## What is left

`1.309e-8` of score: `1.125e-8` on `kappa` (the gap from `0.32298206` to the
floor) and `1.844e-9` on `lambda`. Neither part is structurally unreachable —
only the boundary point `kap = π ^ 3 / 96` itself is — so in principle all of it
is available to a sharp enough rational certification.

Every remaining sprint is therefore a one-literal change plus a sharper
certification of one of exactly two one-dimensional quantities: how tightly
`π ^ 3 / 96` can be bounded from above, and `π − 2√2` from below. Nothing about
polygons, deficits, monotonicity or Taylor order can matter again —
`valid_of_bracket` has absorbed all of it, and the contract proof below is three
lines. The concrete next moves, both cheap: run the cosine anchor at `k = 6`
(`Real.cos_pi_over_two_pow 6`, one more `+`-nested stage; the inverted quartic
truncation falls by `16×` per level, from a measured `2.53e-8` at `k = 5` to
`1.58e-9`, taking `kappa` to about `0.3229820492` — worth `1.08e-8`, i.e. 82% of
everything left), and widen `lambda` to the value already proved here and then
rounded away, `313165527976/1000000000000` (worth a further `9.76e-10`).
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, `1.8e-9` below the exact ceiling `π - 2√2`
(`admissible_lambda_lt`). -/
def lambda : ℝ := 313165527/1000000000

/-- Upper error coefficient, `1.12e-8` above the analytic floor `π ^ 3 / 96`
(`admissible_kappa_ge`), of which `1.6e-9` is the rounding of
`pi_cube_div_lt_sharp` and the rest is `pi_le_sharp`'s `3.12e-8` on `π`. -/
def kappa : ℝ := 32298206/100000000

/-- `lambda` sits below the exact ceiling, certified from below by the depth-3
lower anchor and from above by the twelve-digit upper bound on `√2`:
`3.141592652724 - 2 · 1.414213562374 = 0.313165527976`, so the literal clears it
by `9.76e-10`. -/
lemma lambda_lt_ceiling : lambda < Real.pi - 2 * Real.sqrt 2 := by
  rw [lambda]
  linarith [sqrt_two_lt_sharp, pi_ge_depth_three]

/-! ### The scored contract

Three lines. Every analytic ingredient — the cubic and quintic Taylor rungs, the
uniform deficit bounds, the monotonicity of the scaled deficit — is inside
`valid_of_bracket`, and all that is left here is to check two rational literals
against the two certified endpoints. -/

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa :=
  valid_of_bracket (by norm_num [lambda]) lambda_lt_ceiling
    (by rw [kappa]; exact pi_cube_div_lt_sharp)

/-! ### The optimality certificate, instantiated -/

/-- **The bracket on the benchmark's true optimum.** The left half is
`optimum_gt`, a rational certification; the right half is the candidate's own
contract applied to itself through `admissible_score_gt`. Width of the window:
`4.5e-8`. -/
theorem optimum_bracket :
    (9816488/1000000000 : ℝ) < Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) ∧
      Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) < kappa - lambda :=
  ⟨optimum_gt, admissible_score_gt polygon_pi_constant_search⟩

/-- The arithmetic form of the same statement: the shipped score is within
`4.5e-8` of the infimum of all achievable scores. (The true distance is
`1.309e-8`; the rest is slack in the rational certification of the floor, which
is `pi_le_sharp`'s quartic truncation.) -/
theorem optimality_gap_lt :
    kappa - lambda - (Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2))
      < 45/1000000000 := by
  have hk : kappa - lambda = 9816533/1000000000 := by
    rw [kappa, lambda]; norm_num
  rw [hk]
  linarith [optimum_gt]

/-- **The permanent floor of the benchmark**, restated at the top level: no pair
of constants satisfying the scored contract scores below `0.009816488`. -/
theorem no_candidate_below :
    ∀ lam kap : ℝ, ValidPolygonBound lam kap →
      (9816488/1000000000 : ℝ) < kap - lam :=
  fun _ _ h => admissible_score_gt_rat h

/-! ### The optional secondary frontier, at the frozen benchmark depth

Never declared in five sprints, and it costs no new mathematics: it is the
finite-`n` shadow of exactly the sandwich that proves optimality. At a frozen
depth the *lower* conjunct no longer has to survive `n = 0`, so it is not pinned
by `π - 2√2`; instead `deficit_scaled_ge 10` and the main contract pin
`4 ^ 10 (π - polygonLower 10) = 0.32298204873…` between two rationals `2.2e-8`
apart, against the uniform frontier's `9.82e-3`.

This is **not** a substitute for `polygon_pi_constant_search`, and declaring it
changes neither `kappa` nor `lambda` nor the main contract; the evaluator logs
it separately. A candidate that had only this would be claiming a bound it could
not establish uniformly in `n`. -/

/-- Secondary upper coefficient, the same literal as `kappa`. -/
def kappaDepth10 : ℝ := 32298206/100000000

/-- Secondary lower coefficient. At depth 10 the scaled deficit has already
climbed to within `9.8e-9` of the floor `π ^ 3 / 96`, so the lower coefficient
is nearly the upper one. -/
def lambdaDepth10 : ℝ := 322982038/1000000000

/-- The `π ^ 5` tail of `deficit_ge` at depth 10:
`π ^ 5 / (30720 · 4 ^ 10) = π ^ 5 / 32212254720 < 9.500103e-9`
(true value `9.5001013572…e-9`). -/
theorem pi_pow_five_depth_ten_lt :
    Real.pi ^ 5 / (30720 * 4 ^ 10) < 9500103/1000000000000000 := by
  have h : Real.pi ≤ 31415927/10000000 := pi_le_sharp.trans (by norm_num)
  have h5 : Real.pi ^ 5 ≤ (31415927/10000000 : ℝ) ^ 5 :=
    pow_le_pow_left₀ Real.pi_pos.le h 5
  have hden : (30720 : ℝ) * 4 ^ 10 = 32212254720 := by norm_num
  have hb : ((31415927/10000000 : ℝ)) ^ 5
      < 9500103/1000000000000000 * 32212254720 := by norm_num
  rw [hden, div_lt_iff₀ (by norm_num : (0:ℝ) < 32212254720)]
  linarith

/-- **The secondary contract at the benchmark depth.** The upper conjunct is the
main contract's, instantiated at `n = 10`. The lower conjunct is
`deficit_scaled_ge 10` together with the certified floor `π ^ 3 / 96 >
0.32298204848` and the tail bound above:

    4 ^ 10 (π - polygonLower 10)  ≥  0.32298204848 - 0.000000009500103
                                  =  0.322982038979897 > lambdaDepth10,

a margin of `9.80e-10`. Reported interval width at depth 10:
`(kappaDepth10 - lambdaDepth10) / 4 ^ 10 = 2.2e-8 / 4 ^ 10 = 2.1e-14`. -/
theorem polygon_pi_depth10_search :
    ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10 := by
  refine ⟨by norm_num [lambdaDepth10], by norm_num [kappaDepth10], ?_, ?_⟩
  · have h4n : (0 : ℝ) < 4 ^ (10 : ℕ) := by positivity
    have hD : (322982038/1000000000 : ℝ) < 4 ^ 10 * (Real.pi - polygonLower 10) := by
      linarith [deficit_scaled_ge 10, pi_cube_div_gt, pi_pow_five_depth_ten_lt]
    have hlt : lambdaDepth10 / 4 ^ 10 < Real.pi - polygonLower 10 := by
      rw [div_lt_iff₀' h4n, lambdaDepth10]
      exact hD
    linarith
  · have h := (polygon_pi_constant_search.2.2 10).2
    have hk : kappaDepth10 = kappa := by rw [kappaDepth10, kappa]
    rw [hk]
    exact h

end ProofRefinement.PolygonPi.Candidates.V5
