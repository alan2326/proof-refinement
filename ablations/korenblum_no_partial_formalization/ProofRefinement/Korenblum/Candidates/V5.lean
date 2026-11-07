-- @parent V4
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V5

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V4. -/
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

V5 imports `Proof.RadialSplit` so that the new radial-integral split
(`radialIntegral_split`) and the conditional Korenblum reduction
(`validKorenblum_of_innerCircleMean_dom`) compile as part of V5's build
graph. These two lemmas reduce the entire function-level Korenblum max
principle to a single radial inequality on the inner half — the only
remaining mathematical obstruction for any future inner-half attack.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V5 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V4; this sprint is scaffolding-only and
adds the radial-integral split plus the conditional Korenblum reduction
in `Proof/RadialSplit.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V5
