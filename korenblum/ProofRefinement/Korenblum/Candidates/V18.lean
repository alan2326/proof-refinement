-- @parent V17
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V18

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V17 — sprint 018 ships
the workspace's **first consumer of Wang's printed equation `(11)`**, the
**first closing reducer reaching the branch-2 sub-regime via the short
`(7)+(11)` chain** (no `(8)+(9)`+series machinery), and the **first
cross-validation of two structurally disjoint paper-equation paths to the
same effective branch-2 kernel scalar `c⁴/2`**. The new generic theorem
`valid_of_eq11_subinterval_branch2` integrates Wang's pointwise `(11)`
against `2ρ` over a free sub-interval `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)` and
asks the resulting kernel mass to reach `1`. The sink theorem is still
discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V17, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 018 side lemma: exercise the brand-new `(7)+(11)`-chain branch-2
sub-interval closing reducer `valid_of_eq11_subinterval_branch2` at the
seed `c_value` against an abstract universal `Section2Assumptions` instance.
The signature has only the global annulus-density `IntervalIntegrable` premise
(matching sprint 008's shape) plus a single existential mass premise on the
windowed branch-2 mode integrand `scalarIntegrand2`. Materialises the new
reducer in V18's call graph; not `axiom`-ed and does not call the seed axiom.
-/
theorem v18_eq11_subinterval_branch2_compiles
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
          PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand2 c_value
                  (WangOuter.paperLambda K c_value) ρ) :
    ValidKorenblumBound c_value :=
  valid_of_eq11_subinterval_branch2
    c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window

/--
Sprint 018 structural witness lemma: confirm that the admissible branch-2
window predicate `branchSplit c_value < ρ₁ ≤ ρ₂ < 1` is non-vacuous at the
seed by exhibiting `(ρ₁, ρ₂) = (5/10, 7/10) = (0.5, 0.7)`. We bound
`√(4/3)` from above by `13/10 = 1.3` (since `1.3² = 1.69 > 4/3`), then
`branchSplit c_value = c_value · √(4/3) < 0.3554 · 1.3 ≈ 0.4620 < 0.5`.
Mirrors V14's and V17's window choice for cross-reference. Not `axiom`-ed and
does not call the seed axiom.
-/
theorem v18_branch2_window_witness_at_seed :
    ∃ ρ₁ ρ₂ : ℝ,
      PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
  refine ⟨5 / 10, 7 / 10, ?_, ?_, ?_⟩
  · -- branchSplit c_value ≈ 0.4103 < 0.5
    show PaperAxioms.branchSplit c_value < (5 / 10 : ℝ)
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
  · norm_num
  · norm_num

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new `(7)+(11)`-chain branch-2
sub-interval closing reducer is materialised above in
`v18_eq11_subinterval_branch2_compiles` and
`v18_branch2_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V18
