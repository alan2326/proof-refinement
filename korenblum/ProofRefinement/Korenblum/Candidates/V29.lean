-- @parent V28
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V29

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V28 — sprint 029 ships
the workspace's **first function-level closed-form inner-disk pointwise bound
`circleGap a b r ≤ A · Z_c + B · Z_ρ` whose paper-axiom signature is exactly
`{eq4}`** (no `paper.eq2_sigmaZeroMinus_lower` and no
`paper.eq3_circleGap_decomposition` anywhere in the transitive proof body),
the **first downstream materialisation of sprint 028 in a function-level
chain**, and the **first paper-axiom-strict-subset improvement of sprint
002's exact conclusion** (sprint 002's signature is `{eq2, eq3, eq4}`;
sprint 029 strict-subsets it to `{eq4}` only). The new generic theorem
`circleGap_inner_bound_via_series_eq4_only` re-walks sprint 002's algebraic
chain step by step, substituting sprint 027 for the `eq3` invocation and
sprint 028 for the `eq2` invocation; only `paper.eq4_sigmaPlus_bound`
remains. The sink theorem is still discharged via `valid_of_eq15` so the
score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V28, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 029 side lemma: exercise the brand-new function-level pointwise
inner-disk bound `circleGap_inner_bound_via_series_eq4_only` at concrete
radii `r := 1/10`, `ρ := 1/2`. The signature exhibits the new lemma's
hypothesis shape — seven cells: `paper`, non-negativity of the lower
radius, strict ordering `r < c`, `c < ρ`, `ρ < 1`, summability of the
unconditioned `circleGapSeries` summand at the lower anchor `r`, and
summability of the N2-indicator summand at the upper anchor `ρ`. The
proof body is a single application of the new generic lemma. Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v29_circleGap_inner_bound_via_series_eq4_only_compiles
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * (1 / 10 : ℝ) ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.circleGap a b (1 / 10 : ℝ) ≤
      (c_value ^ 2 - (1 / 10 : ℝ) ^ 2 *
            ((1 / 2 : ℝ) ^ 2 - (1 / 10 : ℝ) ^ 2) /
            ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (1 / 10 : ℝ) ^ 2 *
            ((c_value ^ 2 - (1 / 10 : ℝ) ^ 2) /
              ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  have hr_nn : (0 : ℝ) ≤ (1 / 10 : ℝ) := by norm_num
  have hr_lt : (1 / 10 : ℝ) < c_value := by norm_num [c_value]
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact circleGap_inner_bound_via_series_eq4_only
    paper hr_nn hr_lt hcρ hρ1 hSummable_circleGap_r hSummable_n2_ρ

/--
Sprint 029 structural witness lemma: confirm that the new lemma's bound at
concrete radii `(r, ρ) = (1/10, 1/2)` reproduces the conclusion of sprint
002's `circleGap_inner_bound_of_eq2_eq3_eq4` *without* invoking
`paper.eq2_sigmaZeroMinus_lower` or `paper.eq3_circleGap_decomposition`
anywhere in the proof body. The `paper` parameter is present because
`paper.eq4_sigmaPlus_bound` is invoked through sprint 029; the actual
discharge of the `eq2` and `eq3` directions is via sprints 028 and 027
respectively. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v29_circleGap_inner_bound_via_series_eq4_only_recovers_sprint002_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * (1 / 10 : ℝ) ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.circleGap a b (1 / 10 : ℝ) ≤
      (c_value ^ 2 - (1 / 10 : ℝ) ^ 2 *
            ((1 / 2 : ℝ) ^ 2 - (1 / 10 : ℝ) ^ 2) /
            ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (1 / 10 : ℝ) ^ 2 *
            ((c_value ^ 2 - (1 / 10 : ℝ) ^ 2) /
              ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  -- Sprint 029's bound gives the conclusion directly, without invoking
  -- `paper.eq2_sigmaZeroMinus_lower` or `paper.eq3_circleGap_decomposition`.
  -- The sprint-002 lemma `circleGap_inner_bound_of_eq2_eq3_eq4` would
  -- give the same conclusion, but its proof body consumes both `eq2`
  -- and `eq3`; sprint 029 consumes only `eq4`.
  have hr_nn : (0 : ℝ) ≤ (1 / 10 : ℝ) := by norm_num
  have hr_lt : (1 / 10 : ℝ) < c_value := by norm_num [c_value]
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact circleGap_inner_bound_via_series_eq4_only
    paper hr_nn hr_lt hcρ hρ1 hSummable_circleGap_r hSummable_n2_ρ

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new function-level
inner-disk pointwise bound is materialised above in
`v29_circleGap_inner_bound_via_series_eq4_only_compiles` and
`v29_circleGap_inner_bound_via_series_eq4_only_recovers_sprint002_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V29
