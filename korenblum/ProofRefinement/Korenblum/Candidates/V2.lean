-- @parent V1
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V2

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1 — Sprint 002 is a
*structural* refactor exposing a new analytical chain, not a numerical push. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1, listed in `lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 002 side lemma: exercise the new `(2)+(3)+(4)` inner-disk bound at the
seed paper context. The free parameter `ρ ∈ (c_value, 1)` is exposed as a
`forall` so a downstream sprint can integrate this bound over `r ∈ [0, c_value]`
with `ρ` chosen as a function of integration variables.

This compiles by direct application of the new
`circleGap_inner_bound_of_eq2_eq3_eq4` lemma in `Reduction.lean`.
-/
theorem v2_eq2_eq3_eq4_chain_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {r ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c_value)
    (hcρ : c_value < ρ)
    (hρ1 : ρ < 1) :
    PaperAxioms.circleGap a b r ≤
      (c_value ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value
        + r ^ 2 * ((c_value ^ 2 - r ^ 2) / (ρ ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ :=
  circleGap_inner_bound_of_eq2_eq3_eq4 paper hr_nonneg hr_lt hcρ hρ1

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the new `(2)+(3)+(4)` inner-disk chain is still
materialised above in `v2_eq2_eq3_eq4_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V2
