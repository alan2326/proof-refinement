-- @parent V15
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V16

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V15. -/
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

V16 adds the Hadamard three-circles theorem for `circleMeanSq` (sprint 016)
in `Proof/CircleMeanLogConvex.lean`. Two new theorems are exposed:
`circleMeanSq_geometric_mean_le` (Cauchy–Schwarz / `a = 1/2` form, the
headline) and `circleMeanSq_log_convex` (general Hölder / `a ∈ [0, 1]`
form). They pin in Lean the multiplicative Hadamard three-circles
inequality for the A² circle mean of an analytic function on the unit
disk, derived from sprint 010's canonical-witness Parseval identity plus
Mathlib's tsum-level Hölder inequality. The score
`c_value = 3554/10000` is unchanged from V15.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V16 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V15; this sprint is scaffolding-only and
adds the Hadamard three-circles theorem for `circleMeanSq` in
`Proof/CircleMeanLogConvex.lean`, exercised by the build via import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V16
