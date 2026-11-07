-- @parent V13
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V14

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V13. -/
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

V14 adds the contract-shaped composition layer above sprint 013's clean
conditional in `Proof/InnerRadialReduction.lean`. The new theorem
`validKorenblumBound_of_inner_radial_dominance` lifts the per-pair clean
conditional Korenblum reduction to the universal contract-shaped form.
The score `c_value = 3554/10000` is unchanged; this is the final Lean-side
composition layer required before a future trust-reduction sprint can
replace `hKorenblum_published_3554` with a strictly smaller leaf
`hWang_inner_radial_dominance_3554` (filed as
`Proposals/proposal_001_replace_seed_with_inner_radial_dominance.md`,
status `pending`).
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V14 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V13; this sprint is scaffolding-only and
adds the contract-shaped reduction
`validKorenblumBound_of_inner_radial_dominance` in
`Proof/InnerRadialReduction.lean`, which is exercised by the build via
import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V14
