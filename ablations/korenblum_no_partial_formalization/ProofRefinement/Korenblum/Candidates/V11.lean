-- @parent V10
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V11

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V10. -/
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

V11 imports `Proof.BergmanParseval` so that the new Bergman A² Parseval
identity, the radius-independence of Cauchy power-series coefficient norms,
and the headline `bergmanNormSq_termwise_mono` consumer compile as part of
V11's build graph. With these in hand, every future c-push consumer can
compare `bergmanNormSq f` to `bergmanNormSq g` at the coefficient level —
the same way `circleMeanSq_termwise_mono` (sprint 010) compares the
circle-mean.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V11 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V10; this sprint is scaffolding-only and
adds the Bergman A² Parseval identity in `Proof/BergmanParseval.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V11
