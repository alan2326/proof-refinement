-- @parent V12
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V13

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V12. -/
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

V13 imports `Proof.RadialIntegrability` and `Proof.CleanConditional` so
that the new radial / per-θ integrability bridges and the headline clean
conditional Korenblum reduction
`validKorenblum_of_inner_outer_dom_of_analyticOn` compile as part of
V13's build graph. With these in hand, every existing scaffolding consumer
can be threaded directly from the contract's
`Integrable (‖f z‖²) (volume.restrict UnitDisk)` plus `AnalyticOn ℂ f
UnitDisk` hypotheses, with the only remaining mathematical content being
the inner-half radial dominance hypothesis `h_inner` — the genuine
Korenblum content.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V13 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V12; this sprint is scaffolding-only and
adds the radial / per-θ integrability bridges plus the clean conditional
Korenblum reduction in `Proof/RadialIntegrability.lean` and
`Proof/CleanConditional.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V13
