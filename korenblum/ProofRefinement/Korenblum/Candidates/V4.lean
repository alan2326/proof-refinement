-- @parent V3
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V4

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3 — Sprint 004
exposes a brand-new `(2)+(3)+(4)`-only end-to-end reduction route via
`valid_of_eq2_eq3_eq4_annulus_budget`, but the sink theorem is still
discharged via `valid_of_eq15` so the score does not regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 004 side lemma: exercise the new `(2)+(3)+(4)`-only end-to-end reduction
chain at the seed `c_value` against an *abstract* annulus-side budget
hypothesis. The budget is intentionally accepted as an explicit premise
(mirroring sprint 001's `h_adjacency` and sprint 003's `hInt`); discharging it
from `Section2Assumptions` is the subject of a future sprint. This side lemma
materialises the new reduction route — it is not `axiom`-ed and does not call
the seed axiom.
-/
theorem v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles
    (h_budget :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ : ℝ, c_value < ρ ∧ ρ < 1 ∧
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r)
            volume 0 c_value ∧
          (c_value ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c_value ^ 2)
              / (ρ ^ 2 - c_value ^ 2)
              * PaperAxioms.sigmaZeroMinus a b c_value
            + (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ
            ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value) :
    ValidKorenblumBound c_value :=
  valid_of_eq2_eq3_eq4_annulus_budget c_value_pos c_value_lt_one h_budget

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new `(2)+(3)+(4)`-only reduction route
is materialised above in `v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V4
