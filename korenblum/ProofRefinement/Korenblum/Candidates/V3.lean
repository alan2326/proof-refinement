-- @parent V2
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V3

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2 — Sprint 003 is a
*structural* refactor exposing a new closed-form upper bound on `diskExcess`,
not a numerical push. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2, listed in `lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 003 side lemma: exercise the new closed-form `diskExcess` upper bound
chain at the seed paper context. The integrability hypothesis on
`2r · paper.circleGap r` is exposed as a hypothesis here (it is intentionally
left out of `Section2Assumptions` and will be the subject of a future sprint).

This compiles by direct application of the new
`diskExcess_upper_bound_of_eq2_eq3_eq4` lemma in `Reduction.lean`.
-/
theorem v3_diskExcess_upper_bound_chain_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ : ℝ}
    (hcρ : c_value < ρ)
    (hρ1 : ρ < 1)
    (hInt : IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r)
              volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c_value ^ 2)
          / (ρ ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ :=
  diskExcess_upper_bound_of_eq2_eq3_eq4 paper c_value_pos hcρ hρ1 hInt

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the new closed-form `diskExcess` upper bound is
still materialised above in `v3_diskExcess_upper_bound_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V3
