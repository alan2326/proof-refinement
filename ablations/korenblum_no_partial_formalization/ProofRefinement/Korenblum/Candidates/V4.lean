-- @parent V3
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V4

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V3. -/
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

V4 imports `Proof.CircleMeanCompare` so that the radial-form outer-annulus
comparison — both the circle-mean comparison lemma at fixed radius and the
parallel re-derivation of `outerAnnulus_norm_sq_mono` routed through the
radial polar form — compiles as part of V4's build graph. These are the
canonical bridge from "pointwise dominance on outerAnnulus" to "radial-form
dominance of the outer Bergman integral", which any inner-half attack
must compose with.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V4 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V3; this sprint is scaffolding-only and
adds the circle-mean / radial-form outer-annulus comparison in
`Proof/CircleMeanCompare.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V4
