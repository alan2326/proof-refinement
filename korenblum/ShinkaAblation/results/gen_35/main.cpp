-- EVOLVE-BLOCK-START
-- @parent seed
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.ShinkaTrustedSeed

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.SHINKA_PLACEHOLDER

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

def c_value : ℝ := 3554 / 10000
-- Note: the trusted seed pins c = 3554/10000 exactly. Increasing c_value
-- would require either proving Eq15ScalarBound at a larger c from Mathlib
-- (open problem) or a new registered oracle.

theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value]
theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value]

theorem eq15_bound_at_seed (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value := by
  simpa [c_value] using
    ProofRefinement.Korenblum.ShinkaTrustedSeed.hEq15_seed_3554 K

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => eq15_bound_at_seed K)

end ProofRefinement.Korenblum.Candidates.SHINKA_PLACEHOLDER
-- EVOLVE-BLOCK-END