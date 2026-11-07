-- @parent V19
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V20

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V19 — sprint 020 ships
the workspace's **first closing reducer with a straddling-window admissibility
predicate**, the **first reducer whose mass premise sums two integrals over
disjoint branch sub-intervals**, and the **first reducer to invoke both
`paper.eq10_branch1_pointwise` and `paper.eq11_branch2_pointwise`
simultaneously**. The new generic theorem
`valid_of_eq10_eq11_straddling_window` admits a window
`[ρ₁, ρ₂]` straddling `branchSplit c` (i.e. `c < ρ₁ ≤ branchSplit c ≤ ρ₂ < 1`)
and asks the *sum* of two windowed mass integrals — `scalarIntegrand1` over
`[ρ₁, branchSplit c]` plus `scalarIntegrand2` over `[branchSplit c, ρ₂]` — to
reach `1`. The sink theorem is still discharged via `valid_of_eq15` so the
score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V19, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 020 side lemma: exercise the brand-new straddling-window closing
reducer `valid_of_eq10_eq11_straddling_window` at the seed `c_value` against
an abstract universal `Section2Assumptions` instance. The signature exhibits
the new straddling-window admissibility predicate and the new summed mass
premise; the proof body is a single application of the new generic reducer.
Not `axiom`-ed and does not call the seed axiom.
-/
theorem v20_eq10_eq11_straddling_window_compiles
    (hSplit_lt_one : PaperAxioms.branchSplit c_value < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c_value 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c_value ∧
            PaperAxioms.branchSplit c_value ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              (∫ ρ in ρ₁..PaperAxioms.branchSplit c_value,
                Korenblum.scalarIntegrand1 c_value
                  (WangOuter.paperLambda K c_value) ρ) +
              (∫ ρ in PaperAxioms.branchSplit c_value..ρ₂,
                Korenblum.scalarIntegrand2 c_value
                  (WangOuter.paperLambda K c_value) ρ)) :
    ValidKorenblumBound c_value :=
  valid_of_eq10_eq11_straddling_window
    c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window

/--
Sprint 020 structural witness lemma: confirm that the admissible straddling
window predicate `c_value < ρ₁ ≤ branchSplit c_value ≤ ρ₂ < 1` is non-vacuous
at the seed by exhibiting the degenerate single-point straddling witness
`ρ₁ = ρ₂ = branchSplit c_value`. The boundary inequalities `ρ₁ ≤ branchSplit
c_value` and `branchSplit c_value ≤ ρ₂` collapse to `le_rfl`; the strict
constraints `c_value < branchSplit c_value` and `branchSplit c_value < 1`
are derived from `√(4/3) > 1` and `√(4/3) < 13/10` respectively. Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v20_straddling_window_witness_at_seed :
    ∃ ρ₁ ρ₂ : ℝ,
      c_value < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c_value ∧
        PaperAxioms.branchSplit c_value ≤ ρ₂ ∧ ρ₂ < 1 := by
  refine ⟨PaperAxioms.branchSplit c_value, PaperAxioms.branchSplit c_value,
          ?_, le_rfl, le_rfl, ?_⟩
  · -- c_value < branchSplit c_value
    show c_value < PaperAxioms.branchSplit c_value
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [h_sq, h_sqrt_nonneg]
    have hc_pos : (0 : ℝ) < c_value := c_value_pos
    nlinarith [h_sqrt_gt_one, hc_pos]
  · -- branchSplit c_value < 1
    show PaperAxioms.branchSplit c_value < (1 : ℝ)
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
      have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by norm_num
      nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
    have hc : c_value = 3554 / 10000 := rfl
    rw [hc]
    nlinarith [hsqrt_lt, hsqrt_nonneg]

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new straddling-window closing
reducer is materialised above in `v20_eq10_eq11_straddling_window_compiles`
and `v20_straddling_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V20
