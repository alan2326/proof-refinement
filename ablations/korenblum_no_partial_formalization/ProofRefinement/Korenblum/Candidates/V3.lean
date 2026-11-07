-- @parent V2
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V3

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V2. -/
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

V3 imports `Proof.RadialBergman` so that the radial polar form of the
inner / outer Bergman integrals — together with the canonical `circleMeanSq`
abstraction — compiles as part of V3's build graph. These are the missing
bridge between `Proof.PolarBergman` (polar pull-back of the whole disk)
and `Proof.AnnulusBergman` (the inner / outer set-integral split). Every
honest route past `c = 0.3554` factors through some monotone-mean argument
on `r ↦ circleMeanSq f r`, which cannot even be stated without this file.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V3 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V2; this sprint is scaffolding-only and
adds the radial polar form in `Proof/RadialBergman.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V3
