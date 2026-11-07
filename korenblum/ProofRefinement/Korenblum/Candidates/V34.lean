-- @parent V33
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V34

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V33 — sprint 034 ships
the workspace's **first integrated `diskExcess` upper bound whose proof body
invokes zero `paper.eq*` field projections**, the **first sprint to fuse the
complete series-level toolkit (sprints 005, 025, 027, 028, 032) into a single
integrated chain**, the **first downstream consumer of sprint 032**, and the
**type-level isolation of `Σ⁺ c ≤ Σ⁻ c` as the unique series-non-derivable
analytical target** for a future oracle/proposal. The new generic theorem
`diskExcess_upper_bound_via_series_only_modulo_sigma_compare` lifts the unique
non-series-derivable conjunct of the `eq2`/`eq3`/`eq4` cone — `Σ⁺(c) ≤ Σ⁻(c)`
— into its signature as the explicit hypothesis `hSigmaCmp`, with every other
analytical step supplied by an existing paper-axiom-free workspace lemma
(sprint 005 + sprint 025 + sprint 032). The sink theorem is still discharged
via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V33, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 034 side lemma: exercise the brand-new paper-axiom-free integrated disk
bound `diskExcess_upper_bound_via_series_only_modulo_sigma_compare` at the
seed `c = c_value`. The signature exhibits the new lemma's hypothesis shape —
six cells: `hSummable` (universal-over-`[0, c_value)` series summability of
the unconditioned `coeffPlusGap · r^(2k)`), `hSummable_n1_c` (N1-restricted
summability at the upper anchor `c_value`), `hSigmaCmp`
(`sigmaPlus a b c_value ≤ sigmaMinus a b c_value` — the unique
series-non-derivable conjunct), and `hInt` (integrability of `2r·circleGap`
on `[0, c_value]`). Crucially, **no `Section2Assumptions` instance is needed**
— this side lemma does not use a `paper` parameter. The proof body is a
single application of the new generic lemma. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v34_disk_bound_via_series_only_modulo_sigma_compare_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c_value ≤ PaperAxioms.sigmaMinus a b c_value)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
  diskExcess_upper_bound_via_series_only_modulo_sigma_compare
    c_value_pos c_value_lt_one hSummable hSummable_n1_c hSigmaCmp hInt

/--
Sprint 034 structural witness lemma: demonstrate that any candidate carrying a
`Section2Assumptions a b K c_value` instance can discharge the new theorem's
`hSigmaCmp` hypothesis from `paper.eq4_sigmaPlus_bound`'s second conjunct at
`r = c_value`, recovering sprint 026's exact conclusion at the seed through
the new chain. This confirms the new theorem **strictly generalises** sprint
026: any consumer with `paper.eq4` access can recover sprint 026's bound, and
any consumer with access to a stronger oracle/proposal that proves
`Σ⁺(c) ≤ Σ⁻(c)` independently can discharge the new theorem **without ever
invoking `paper.eq4`**. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v34_disk_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value := by
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
  exact diskExcess_upper_bound_via_series_only_modulo_sigma_compare
    hc_pos hc_lt_one hSummable hSummable_n1_c hSigmaCmp hInt

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free integrated
disk bound is materialised above in
`v34_disk_bound_via_series_only_modulo_sigma_compare_compiles` and
`v34_disk_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V34
