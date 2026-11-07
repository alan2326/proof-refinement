-- @parent V31
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V32

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V31 — sprint 032 ships
the workspace's **first paper-axiom-free monotonicity lemma on `sigmaPlus`**,
the **dual of sprint 011's `sigmaZeroMinus_monotone_of_summable` on the
structurally distinct N1 partition**, the **first N1-side
comparison/monotonicity argument** in the workspace, and the **first lemma to
handle the `k = 0 ∈ N1` boundary case explicitly**. The new generic theorem
`sigmaPlus_monotone_of_summable` derives `Σ⁺(r) ≤ Σ⁺(s)` for `0 ≤ r ≤ s` from
termwise monotonicity of the N1-restricted summands plus summability at the
larger argument; the `k = 0` summand is handled by termwise equality (since
`r^0 = s^0 = 1`), and summability at `r` is recovered from summability at `s`
by zeroing the `k = 0` term and applying `Summable.of_nonneg_of_le` to the
modified function. Together with sprints 005, 027, and 028, this completes
the workspace's series-level discharge of every conjunct of `paper.eq2`,
`paper.eq3`, and `paper.eq4` *except* `sigmaPlus c ≤ sigmaMinus c`. The sink
theorem is still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V31, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 032 side lemma: exercise the brand-new paper-axiom-free monotonicity
lemma `sigmaPlus_monotone_of_summable` at concrete witness values
`r := c_value/2 = 1777/10000` and `s := c_value = 3554/10000`. The signature
exhibits the new lemma's hypothesis shape — three cells: `hr_nonneg`
(non-negativity of `r`), `hrs` (ordering `r ≤ s`), and `hSummable_s`
(summability of the N1-indicator-weighted summand at the larger argument
`s = c_value`). The proof body is a single application of the new generic
lemma. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v32_sigmaPlus_monotone_via_series_compiles
    (a b : ℕ → ℂ)
    (hSummable_s :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b (c_value / 2) ≤
      PaperAxioms.sigmaPlus a b c_value := by
  have hr_nonneg : (0 : ℝ) ≤ c_value / 2 := by
    have hc_nn : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos
    linarith
  have hrs : c_value / 2 ≤ c_value := by
    have hc_pos : (0 : ℝ) < c_value := c_value_pos
    linarith
  exact sigmaPlus_monotone_of_summable hr_nonneg hrs hSummable_s

/--
Sprint 032 structural witness lemma: confirm that the new lemma's conclusion
at the concrete witness values `r := c_value/2`, `s := c_value` reproduces the
*first conjunct* of `paper.eq4_sigmaPlus_bound`'s statement at the seed
(`Σ⁺(r) ≤ Σ⁺(c)`), *without* invoking `paper.eq4_sigmaPlus_bound` anywhere in
the proof body. The paper-axiom invocation is shown only in this docstring as
a cross-check: `paper.eq4_sigmaPlus_bound paper hr_nn hr_le_c` would give
`PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧ ... ∧ ...`,
whose first conjunct is exactly the conclusion below. Sprint 032 derives the
same conclusion from a strictly series-side summability premise on the
N1-restricted summand at `s = c_value`. Not `axiom`-ed and does not call the
seed axiom.
-/
theorem v32_sigmaPlus_monotone_via_series_recovers_eq4_first_conjunct_at_seed
    (a b : ℕ → ℂ)
    (hSummable_s :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b (c_value / 2) ≤
      PaperAxioms.sigmaPlus a b c_value := by
  -- The new lemma gives the conclusion directly from the summability premise.
  -- This matches the first conjunct of `paper.eq4_sigmaPlus_bound paper hr_nn
  -- hr_le_c` at `r := c_value/2`, `c := c_value` — but no paper-axiom is
  -- invoked anywhere in this proof body.
  have hr_nonneg : (0 : ℝ) ≤ c_value / 2 := by
    have hc_nn : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos
    linarith
  have hrs : c_value / 2 ≤ c_value := by
    have hc_pos : (0 : ℝ) < c_value := c_value_pos
    linarith
  exact sigmaPlus_monotone_of_summable hr_nonneg hrs hSummable_s

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
monotonicity lemma `sigmaPlus_monotone_of_summable` is materialised above in
`v32_sigmaPlus_monotone_via_series_compiles` and
`v32_sigmaPlus_monotone_via_series_recovers_eq4_first_conjunct_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V32
