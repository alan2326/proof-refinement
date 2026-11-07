-- @parent seed
import ProofRefinement.Korenblum.Proof.CandidateContract

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V0

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. -/
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

In the no-partial-formalization ablation arm, the trust surface contains no
Wang Section 2 hypothesis bundle and no equation chain — so the seed leaf
is the full conclusion at `c = 0.3554` rather than an intermediate
sub-claim.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
Seed candidate: the published `c = 0.3554` is a valid Korenblum lower bound.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V0
