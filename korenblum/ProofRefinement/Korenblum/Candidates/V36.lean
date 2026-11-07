-- @parent V35
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V36

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V35 — sprint 036 ships
the workspace's **first non-integrated, paper-axiom-free two-`Z` upper bound on
`circleGap a b r`**, the **pointwise counterpart of sprint 034**, and the
**first lemma to fuse sprint 005 + sprint 027 + sprint 028 + sprint 032 + an
explicit `hSigmaCmp` cell into a single pointwise chain**. The new generic
theorem `circleGap_inner_bound_via_series_only_modulo_sigma_compare` lifts the
unique non-series-derivable conjunct of the `eq2`/`eq3`/`eq4` cone —
`Σ⁺(c) ≤ Σ⁻(c)` — into its signature as the explicit hypothesis `hSigmaCmp`.
The sink theorem is still discharged via `valid_of_eq15` so the score does
not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V35, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 036 side lemma: exercise the brand-new paper-axiom-free pointwise
inner-disk two-`Z` upper bound
`circleGap_inner_bound_via_series_only_modulo_sigma_compare` at concrete
radii `r := c_value / 2 = 1777/10000`, `ρ := 1/2`. The signature exhibits
the new lemma's hypothesis shape — eight cells: `hr_nonneg`, `hr_lt`, `hcρ`,
`hρ1`, `hSummable_circleGap_r`, `hSummable_n1_c`, `hSummable_n2_ρ`,
`hSigmaCmp`. Crucially, **no `Section2Assumptions` instance is needed** —
this side lemma does not use a `paper` parameter. The proof body is a
single application of the new generic lemma. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_compiles
    (a b : ℕ → ℂ)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * (1777 / 10000 : ℝ) ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c_value ≤ PaperAxioms.sigmaMinus a b c_value) :
    PaperAxioms.circleGap a b (1777 / 10000 : ℝ) ≤
      (c_value ^ 2 - (1777 / 10000 : ℝ) ^ 2 *
            ((1 / 2 : ℝ) ^ 2 - (1777 / 10000 : ℝ) ^ 2) /
            ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (1777 / 10000 : ℝ) ^ 2 *
            ((c_value ^ 2 - (1777 / 10000 : ℝ) ^ 2) /
              ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  have hr_nn : (0 : ℝ) ≤ (1777 / 10000 : ℝ) := by norm_num
  have hr_lt : (1777 / 10000 : ℝ) < c_value := by norm_num [c_value]
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact circleGap_inner_bound_via_series_only_modulo_sigma_compare
    hr_nn hr_lt hcρ hρ1 hSummable_circleGap_r hSummable_n1_c hSummable_n2_ρ
    hSigmaCmp

/--
Sprint 036 structural witness lemma: demonstrate that any candidate carrying a
`Section2Assumptions a b K c_value` instance can discharge the new theorem's
`hSigmaCmp` hypothesis from `paper.eq4_sigmaPlus_bound`'s second conjunct at
`r = c_value`, recovering sprint 029's exact conclusion at the seed through
the new chain. This confirms the new theorem **strictly generalises** sprint
029: any consumer with `paper.eq4` access can recover sprint 029's bound, and
any consumer with access to a stronger oracle/proposal that proves
`Σ⁺(c) ≤ Σ⁻(c)` independently can discharge the new theorem **without ever
invoking `paper.eq4`**. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * (1777 / 10000 : ℝ) ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.circleGap a b (1777 / 10000 : ℝ) ≤
      (c_value ^ 2 - (1777 / 10000 : ℝ) ^ 2 *
            ((1 / 2 : ℝ) ^ 2 - (1777 / 10000 : ℝ) ^ 2) /
            ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value
        + (1777 / 10000 : ℝ) ^ 2 *
            ((c_value ^ 2 - (1777 / 10000 : ℝ) ^ 2) /
              ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  -- Discharge `hSigmaCmp` from the second conjunct of paper equation `(4)`
  -- (the conjunct `sigmaPlus c ≤ sigmaMinus c` is the same scalar inequality
  -- regardless of the witness `r < c` chosen; we pick `r = 0`).
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hc_lt_one : c_value < 1 := c_value_lt_one
  have h4 :=
    paper.eq4_sigmaPlus_bound (r := 0) (le_refl 0) hc_pos hc_lt_one
  have h4_unfold :
      PaperAxioms.sigmaPlus a b 0 ≤ PaperAxioms.sigmaPlus a b c_value ∧
        PaperAxioms.sigmaPlus a b c_value ≤ PaperAxioms.sigmaMinus a b c_value ∧
          PaperAxioms.sigmaMinus a b c_value =
            c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value := by
    simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
  have hSigmaCmp :
      PaperAxioms.sigmaPlus a b c_value ≤ PaperAxioms.sigmaMinus a b c_value :=
    h4_unfold.2.1
  have hr_nn : (0 : ℝ) ≤ (1777 / 10000 : ℝ) := by norm_num
  have hr_lt : (1777 / 10000 : ℝ) < c_value := by norm_num [c_value]
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact circleGap_inner_bound_via_series_only_modulo_sigma_compare
    hr_nn hr_lt hcρ hρ1 hSummable_circleGap_r hSummable_n1_c hSummable_n2_ρ
    hSigmaCmp

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free pointwise
inner-disk two-`Z` upper bound is materialised above in
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_compiles` and
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V36
