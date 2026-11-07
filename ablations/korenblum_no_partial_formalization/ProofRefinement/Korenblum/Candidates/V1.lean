-- @parent V0
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V1

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V0. -/
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

V1 imports `Proof.PolarBergman` so that the polar-coordinate decomposition
of `bergmanNormSq` (the natural bridge from `∫_𝔻 ‖f‖² dA` to
radial-against-circle integrals) compiles as part of V1's build graph.
The polar lemma is not yet structurally invoked in the final theorem; it
is scaffolding for follow-up sprints aiming to push `c_value` past
`0.3554` without expanding the trust surface.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V1 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V0; this sprint is scaffolding-only and
adds the polar Bergman bridge in `Proof/PolarBergman.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V1
