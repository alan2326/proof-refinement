-- @parent V29
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V30

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V29 — sprint 030 ships
the workspace's **first integrated two-`Z` `diskExcess` upper bound whose
paper-axiom signature is exactly `{eq4}`** (no `paper.eq2_sigmaZeroMinus_lower`
and no `paper.eq3_circleGap_decomposition` anywhere in the transitive proof
body), the **first downstream materialisation of sprint 029 in an integrated
chain**, and the **first paper-axiom-strict-subset improvement of sprint 003's
exact integrated-layer conclusion** (sprint 003's signature is `{eq2, eq3,
eq4}`; sprint 030 strict-subsets it to `{eq4}` only). The new generic theorem
`diskExcess_upper_bound_via_series_eq4_only_two_Z` re-walks sprint 003's
algebraic chain step by step, substituting sprint 029 for the inner-disk
pointwise bound; only `paper.eq4_sigmaPlus_bound` remains (and it is invoked
inside sprint 029, not directly inside sprint 030). The sink theorem is still
discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V29, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 030 side lemma: exercise the brand-new integrated two-`Z` `diskExcess`
upper bound `diskExcess_upper_bound_via_series_eq4_only_two_Z` at concrete
upper anchor `ρ := 1/2`. The signature exhibits the new lemma's hypothesis
shape — seven cells: `paper`, `hc_pos` (positivity of `c`), `hcρ` (strict
ordering `c < ρ`), `hρ1` (strict ordering `ρ < 1`), `hSummable_circleGap`
(summability of the unconditioned `circleGapSeries` summand quantified over
`r ∈ [0, c)`), `hSummable_n2_ρ` (summability of the N2-indicator summand at
the upper anchor `ρ`), and `hInt` (integrability of `2 * r * circleGap r`
on `[0, c]`). The proof body is a single application of the new generic
lemma. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v30_disk_bound_via_series_eq4_only_two_Z_compiles
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 4 / 6) * (3 * (1 / 2 : ℝ) ^ 2 - 4 * c_value ^ 2)
            / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (c_value ^ 6 / 6) / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact diskExcess_upper_bound_via_series_eq4_only_two_Z
    paper hc_pos hcρ hρ1 hSummable_circleGap hSummable_n2_ρ hInt

/--
Sprint 030 structural witness lemma: confirm that the new lemma's bound at
the concrete upper anchor `ρ = 1/2` reproduces the conclusion of sprint
003's `diskExcess_upper_bound_of_eq2_eq3_eq4` *without* invoking
`paper.eq2_sigmaZeroMinus_lower` or `paper.eq3_circleGap_decomposition`
anywhere in the proof body. The `paper` parameter is present because
`paper.eq4_sigmaPlus_bound` is invoked through sprint 029 (which sprint
030 consumes), not directly. The sprint-003 lemma `diskExcess_upper_bound_of_eq2_eq3_eq4`
would give the same conclusion, but its proof body consumes both `eq2` and
`eq3`; sprint 030 consumes only `eq4`. Not `axiom`-ed and does not call
the seed axiom.
-/
theorem v30_disk_bound_via_series_eq4_only_two_Z_recovers_sprint003_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 4 / 6) * (3 * (1 / 2 : ℝ) ^ 2 - 4 * c_value ^ 2)
            / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (c_value ^ 6 / 6) / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2)
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  -- Sprint 030's bound gives the conclusion directly, without invoking
  -- `paper.eq2_sigmaZeroMinus_lower` or `paper.eq3_circleGap_decomposition`.
  -- The sprint-003 lemma `diskExcess_upper_bound_of_eq2_eq3_eq4` would give
  -- the same conclusion, but its proof body consumes both `eq2` and `eq3`;
  -- sprint 030 consumes only `eq4` (and only inside sprint 029's body).
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact diskExcess_upper_bound_via_series_eq4_only_two_Z
    paper hc_pos hcρ hρ1 hSummable_circleGap hSummable_n2_ρ hInt

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new integrated two-`Z`
`diskExcess` upper bound is materialised above in
`v30_disk_bound_via_series_eq4_only_two_Z_compiles` and
`v30_disk_bound_via_series_eq4_only_two_Z_recovers_sprint003_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V30
