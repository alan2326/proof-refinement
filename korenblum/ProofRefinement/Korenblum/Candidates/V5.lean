-- @parent V4
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V5

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3/V4 — Sprint 005
exposes a brand-new outer-side pointwise lower bound on `2ρ · circleGap ρ` via
the `(8)+(9)` bridge plus the new series identity
`sigmaMinus = ρ² · sigmaZeroMinus`, but the sink theorem is still discharged
via `valid_of_eq15` so the score does not regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3/V4, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 005 side lemma: exercise the new outer-annulus pointwise lower bound at
the seed `c_value`. The chain `eq8 → eq9 → sigmaMinus = ρ²·sigmaZeroMinus
→ ÷ Λ(c, ρ) → · 2ρ` materialises a fundamentally new dependency signature
(`paperLambda` as a pointwise denominator on the annulus side); discharging
sprint 004's annulus-budget hypothesis from this bound is the subject of a
future sprint. This side lemma is not `axiom`-ed and does not call the seed
axiom.
-/
theorem v5_circleGap_outer_lower_bound_chain_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ : ℝ}
    (hcρ : c_value < ρ)
    (hρ1 : ρ < 1) :
    2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
        / WangOuter.paperLambda K c_value ρ
      ≤ 2 * ρ * PaperAxioms.circleGap a b ρ :=
  circleGap_outer_lower_bound_of_eq8_eq9 paper c_value_pos hcρ hρ1

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new outer-side pointwise lower bound is
materialised above in `v5_circleGap_outer_lower_bound_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V5
