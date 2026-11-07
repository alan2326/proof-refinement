-- @parent V2
import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V3.DeficitMonotone
import ProofRefinement.PolygonPi.Candidates.V3.CubicDeficit
import ProofRefinement.PolygonPi.Candidates.V3.QuinticDeficit

/-!
# V3 — giving the lower side its own analytic ingredient

`lambda = 313165/1000000`, `kappa = 3229947/10000000` (unchanged), score
`98297/10000000 = 0.0098297`, against the parent `V2`'s `0.0329947`.

## The lower side (new)

`V1` and `V2` both derived `lambda` from a single fact: `polygonLower d < π` for
a certified rational lower bound on `polygonLower d`. That route has a hard
ceiling of its own — the best it can ever produce is `π - polygonLower d`
approaching `π - 2√2` from a long way below, `0.3081` at `d = 3` and `0.3117` at
`d = 4`, each level costing another radical stage.

`Candidates/V3/QuinticDeficit.lean` replaces it with the missing companion of
`V2`'s `deficit_le`: a *lower* bound on the deficit, uniform in `n`,

    π - polygonLower n  ≥  π ^ 3 / (96 · 4 ^ n) - π ^ 5 / (30720 · 4 ^ n · 4 ^ n),

from the next Taylor rung `sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120` (`x ≥ 0`). That
rung in turn needs `cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24`, which is obtained with
no new calculus at all: the half-angle identity `cos 2u = 1 - 2 sin²u` reduces
it to squaring `V2`'s own cubic sine bound.

The lower deficit bound is then bootstrapped exactly as `V2` bootstrapped the
upper one, but in the other direction. At depth `2`,

    π  ≥  polygonLower 2 + π ^ 3 / 1536 - π ^ 5 / 7864320,

so every lower bound `c ≤ π` yields the better `π ≥ 3.121445136 + c ^ 3 / 1536
- 3.891496e-5`. Five rounds from the seed `polygonLower 2` give

    3.121445136 → 3.1412067 → 3.14158515 → 3.14159244 → 3.14159259 → 3.141592597,

i.e. **π to nine correct digits, from the polygon itself**, with no radical
deeper than the depth-2 one `V2` already certifies. The `π ^ 5` correction
enters with a minus sign, so it needs an *upper* bound on `π`; that is `V2`'s
`pi_le_round_five`, and this is the first time the two sides of the workspace
feed each other. Nothing is circular: `pi_le_round_five` never mentions the
quintic, and `deficit_ge` is proved with `π ^ 3` and `π ^ 5` symbolic.

Combined with `DeficitMonotone.lean`'s reduction of the lower conjunct to
`n = 0` and a nine-digit upper bound on `√2`, this pins

    π - polygonLower 0 = π - 2√2 ≥ 3.141592597 - 2 · 1.414213563 = 0.313165471

against the exact ceiling `0.31316552…`. `lambda = 0.313165` clears it with
margin `4.7e-7`, so the lower side is now within `5.3e-7` of a bound it can
never exceed.

## The upper side (carried over from `V2`)

Unchanged, and now permanently so: `4 ^ n (π - polygonLower n) → π ^ 3 / 96`
from below, so `π ^ 3 / 96 = 0.32298205…` is the exact infimum of admissible
`kappa` for *any* Taylor order, and `kappa = 0.3229947` sits `1.27e-5` above it.
`Candidates/V3/CubicDeficit.lean` is `V2`'s file verbatim; it also supplies the
cubic sine bound that the new quartic cosine bound consumes, and the `π ^ 5`
upper bound.

The remaining score `0.0098297` is `1.4e-5` above the theoretical optimum of the
whole problem, `π ^ 3 / 96 - (π - 2√2) = 0.00981652…`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V3

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient, `5.3e-7` below the exact ceiling `π - 2√2`. -/
def lambda : ℝ := 313165/1000000

/-- Upper error coefficient, strictly above the analytic floor `π ^ 3 / 96`. -/
def kappa : ℝ := 3229947/10000000

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
  · -- Upper conjunct: the uniform cubic deficit bound plus the bootstrapped
    -- numeric bound on `π ^ 3 / 96`.
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hscaled : (Real.pi - polygonLower n) * 4 ^ n ≤ Real.pi ^ 3 / 96 := by
      calc (Real.pi - polygonLower n) * 4 ^ n
          ≤ Real.pi ^ 3 / (96 * 4 ^ n) * 4 ^ n :=
            mul_le_mul_of_nonneg_right (deficit_le n) h4n.le
        _ = Real.pi ^ 3 / 96 := by field_simp
    have hstrict : (Real.pi - polygonLower n) * 4 ^ n < kappa := by
      rw [kappa]
      exact lt_of_le_of_lt hscaled pi_cube_div_lt
    have : Real.pi - polygonLower n < kappa / 4 ^ n := by
      rw [lt_div_iff₀ h4n]
      exact hstrict
    linarith

end ProofRefinement.PolygonPi.Candidates.V3
