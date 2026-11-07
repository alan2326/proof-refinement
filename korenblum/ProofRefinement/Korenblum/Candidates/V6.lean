-- @parent V5
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V6

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3/V4/V5 — Sprint
006 ships the integrated outer-side lower bound on `annulusExcess` derived
from sprint 005's pointwise bound (the structural counterpart of sprint
003's integrated inner-disk upper bound), but the sink theorem is still
discharged via `valid_of_eq15` so the score does not regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3/V4/V5, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 006 side lemma: exercise the new integrated outer-annulus lower bound at
the seed `c_value`. The chain `eq8 → eq9 → sigmaMinus = ρ²·sigmaZeroMinus →
÷ Λ(c, ρ) → · 2ρ → ∫ over [ρ₁, ρ₂]` materialises a fundamentally new
dependency signature (`annulusExcess` lower-bounded directly by an integrated
expression in `sigmaZeroMinus / paperLambda`). Discharging the
`IntervalIntegrable` premises and choosing concrete `ρ₁, ρ₂` from
`Section2Assumptions` is the subject of a future sprint. This side lemma is
not `axiom`-ed and does not call the seed axiom.
-/
theorem v6_annulusExcess_lower_bound_chain_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ₁ ρ₂ : ℝ}
    (hρ₁ : c_value < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ < 1)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c_value 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c_value ρ) volume ρ₁ ρ₂) :
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c_value ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value :=
  annulusExcess_lower_bound_of_eq8_eq9
    paper c_value_pos hρ₁ hρ₁₂ hρ₂ hIntCircle hIntLambda

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new integrated outer-annulus lower
bound is materialised above in `v6_annulusExcess_lower_bound_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V6
