-- @parent V5
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.CircleExpBridge

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V6

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V5. -/
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

V6 imports `Proof.CircleExpBridge` so that the new bridge from
`Complex.polarCoord.symm` to `Complex.exp` and the seed monomial /
constant-multiplication / scaling identities for `circleMeanSq` compile as
part of V6's build graph. These five lemmas are the seed building blocks
for the Bergman-Parseval / monomial-decomposition direction.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V6 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V5; this sprint is scaffolding-only and
adds the `Complex.exp` parametrisation bridge plus the first monomial
circle-mean identities in `Proof/CircleExpBridge.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V6
