-- @parent V6
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V7

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V6. -/
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

V7 imports `Proof.CircleInnerProduct` so that the new `ℂ`-valued circle
inner-product pairing on `(ℂ → ℂ)`-functions, the `exp(ikθ)` orthogonality
identity, and the diagonal / off-diagonal monomial identities compile as
part of V7's build graph. These are the off-diagonal seed building blocks
for the Bergman-Parseval / monomial-decomposition direction. With
`CircleExpBridge` (diagonal seeds, sprint 006) and `CircleInnerProduct`
(off-diagonal seeds, this sprint) both in place, the polynomial Parseval
identity is unlocked for a subsequent sprint.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V7 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V6; this sprint is scaffolding-only and
adds the off-diagonal monomial circle-mean identities in
`Proof/CircleInnerProduct.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V7
