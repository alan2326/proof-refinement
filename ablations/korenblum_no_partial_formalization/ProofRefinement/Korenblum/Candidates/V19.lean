-- @parent V18
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct
import ProofRefinement.Korenblum.Proof.CirclePolynomialParseval
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval
import ProofRefinement.Korenblum.Proof.PolarIntegrability
import ProofRefinement.Korenblum.Proof.RadialIntegrability
import ProofRefinement.Korenblum.Proof.CleanConditional
import ProofRefinement.Korenblum.Proof.InnerRadialReduction
import ProofRefinement.Korenblum.Proof.AnnulusBergmanParseval
import ProofRefinement.Korenblum.Proof.CircleMeanLogConvex
import ProofRefinement.Korenblum.Proof.CauchyL2Estimate
import ProofRefinement.Korenblum.Proof.SubMeanValue
import ProofRefinement.Korenblum.Proof.CircleMeanContinuous

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V19

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V18. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input.

Wang (2025) proved the Korenblum maximum principle holds at radius
`c = 0.3554` at the Bergman A² level. This single axiom asserts the entire
Wang theorem at this radius.

V19 adds two public theorems in `Proof/CircleMeanContinuous.lean`:

* `continuousAt_circleMeanSq_of_analyticOn_unitDisk` — for `f` analytic on
  `UnitDisk`, the function `r ↦ circleMeanSq f r` is continuous at every
  `r₀ ∈ [0, 1)`. Proved via sprint 010's canonical-witness Parseval identity
  plus a Weierstrass M-test on the resulting `tsum` via Mathlib's
  `continuousOn_tsum`. The boundary case `r₀ = 0` is handled by combining
  right-continuity at `0` with the symmetry `circleMeanSq f r = circleMeanSq
  f |r|` (the polar pull-back integrand is `2π`-periodic in `θ`, and
  `polarCoord.symm (-r, θ) = polarCoord.symm (r, θ + π)`).

* `cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq` — boundary form
  of sprint 017's cross-function Cauchy L² estimate. For `f, g` analytic and
  pointwise dominated on the outer annulus, every Cauchy coefficient of `f`
  is bounded at the inner-disk-boundary radius `c`:
  `(2π) · ‖a_k(f)‖² · c^(2k) ≤ circleMeanSq g c`. Proved by picking a
  decreasing sequence `r_n := c + (1 - c)/(n + 2) ↘ c`, applying sprint 017's
  outer-radius bound at each `r_n`, and passing to the limit using continuity
  of `r ↦ circleMeanSq g r` at `r = c` (theorem (1) above) plus continuity
  of `r ↦ r^(2k)`.

This is the **boundary coefficient bound**: the natural primitive for any
future Hayman-style extremal-function or c-push consumer that wants a
coefficient-level upper bound at the inner-disk-boundary radius `c`. The
score `c_value = 3554/10000` is unchanged from V18.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V19 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V18; this sprint is scaffolding-only and
adds the continuity of `circleMeanSq f r` plus the boundary form of the
cross-function Cauchy L² coefficient estimate in
`Proof/CircleMeanContinuous.lean`, exercised by the build via import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V19
