-- EVOLVE-BLOCK-START
-- @parent seed
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.ShinkaTrustedSeed

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.SHINKA_PLACEHOLDER

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value]
theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value]

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => by
    have h : Eq15ScalarBound K ((3554 : ℝ) / 10000) :=
      ProofRefinement.Korenblum.ShinkaTrustedSeed.hEq15_seed_3554 K
    simpa [c_value] using h)

end ProofRefinement.Korenblum.Candidates.SHINKA_PLACEHOLDER
-- EVOLVE-BLOCK-END