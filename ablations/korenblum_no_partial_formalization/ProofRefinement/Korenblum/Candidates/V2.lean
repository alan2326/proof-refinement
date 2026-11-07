-- @parent V1
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V2

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V1. -/
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

V2 imports `Proof.AnnulusBergman` so that the annulus-decomposition split
of `bergmanNormSq` together with the outer-annulus monotonicity corollary
compile as part of V2's build graph. These are the next-smallest Bergman
scaffolding handle after the polar decomposition; together they isolate
the easy half of any Korenblum-style comparison and leave the inner-disk
integral as the explicit obstruction for follow-up sprints.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V2 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V1; this sprint is scaffolding-only and
adds the annulus split + outer-annulus monotonicity in
`Proof/AnnulusBergman.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V2
