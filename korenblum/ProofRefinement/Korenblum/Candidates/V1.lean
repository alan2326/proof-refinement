-- @parent V0
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V1

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0 — Sprint 001 is a
*structural* refactor, not a numerical push. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0, listed in `lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 001 side lemma: exercise the new `valid_of_eq12_eq13` reduction at the
seed paper context. The adjacency hypothesis
`annulusLeftExcess + annulusRightExcess ≤ annulusExcess` is exposed as a
hypothesis here; the next sprint will derive it inside the workspace.

This compiles because Wang's `(15)` (delivered by `hEq15_seed_3554`) is exactly
`1 ≤ scalarCriterion`, which is the second hypothesis of `valid_of_eq12_eq13`.
-/
theorem v1_eq12_eq13_chain_compiles
    (h_adjacency :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
          PaperAxioms.annulusLeftExcess paper.circleGap c_value
              + PaperAxioms.annulusRightExcess paper.circleGap c_value
            ≤ annulusExcess paper.circleGap c_value) :
    ValidKorenblumBound c_value :=
  valid_of_eq12_eq13 c_value_pos c_value_lt_one h_adjacency
    (fun {K} => by
      have := hEq15_seed_3554 K
      simpa [ProblemAxioms.Eq15ScalarBound, PaperAxioms.Eq15ScalarBound]
        using this)

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the new `(12)+(13)` chain is still materialised
above in `v1_eq12_eq13_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V1
