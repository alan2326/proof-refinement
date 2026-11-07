-- @parent V9
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V10

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V9. -/
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

V10 imports `Proof.CircleMeanRadial` so that the new canonical-witness
analytic Bergman-Parseval identity, the termwise-comparison consumer, and the
headline radial-monotonicity statement
`circleMeanSq_radial_mono` compile as part of V10's build graph. With these
in hand, every future inner-half c-push consumer can compare `circleMeanSq f r`
to `circleMeanSq g r` at the coefficient level *across* radii, against the
canonical Cauchy power series.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V10 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V9; this sprint is scaffolding-only and adds
the radial-monotonicity-of-`circleMeanSq` lemma family in
`Proof/CircleMeanRadial.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V10
