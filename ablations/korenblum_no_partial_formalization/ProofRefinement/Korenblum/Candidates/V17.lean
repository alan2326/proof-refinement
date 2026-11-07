-- @parent V16
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V17

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V16. -/
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

V17 adds the Cauchy L² coefficient estimate plus outer-annulus
cross-function bridge (sprint 017) in `Proof/CauchyL2Estimate.lean`. Three
new public theorems are exposed:

* `cauchyPowerSeries_normSq_pow_le_circleMeanSq` — single-coefficient
  Cauchy L² estimate.  For `f` analytic on `UnitDisk` and any `r ∈ (0, 1)`,
  `(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq f r`.
* `outer_circleMeanSq_dom_of_pointwise_dom` — outer-half radial
  comparison, lifted to a public lemma.
* `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` — cross-function
  corollary chaining the above two.

The score `c_value = 3554/10000` is unchanged from V16.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V17 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V16; this sprint is scaffolding-only and
adds the Cauchy L² coefficient estimate plus outer-annulus cross-function
bridge in `Proof/CauchyL2Estimate.lean`, exercised by the build via
import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V17
