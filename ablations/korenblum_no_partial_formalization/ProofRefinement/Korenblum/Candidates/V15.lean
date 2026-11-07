-- @parent V14
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V15

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V14. -/
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

V15 adds the half-disc Bergman A² Parseval expansions (sprint 015) in
`Proof/AnnulusBergmanParseval.lean`. The four new theorems
(`outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`,
`innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries`,
`outerAnnulus_bergmanNormSq_termwise_mono`,
`innerDisk_bergmanNormSq_termwise_mono`) are imported into V15's
compile graph; they expose the c-dependent coefficient-level handle
that any future c-push consumer must factor through. The score
`c_value = 3554/10000` is unchanged from V14.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V15 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V14; this sprint is scaffolding-only and
adds the half-disc Bergman A² Parseval expansions in
`Proof/AnnulusBergmanParseval.lean`, exercised by the build via import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V15
