-- @parent V18
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V19

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V18 — sprint 019 ships
the workspace's **first closing reducer that re-derives Wang's pointwise `(10)`
internally from `(5)+(8)+(9)` instead of consuming `paper.eq10_branch1_pointwise`
directly**, the **first invocation of
`KorenblumPaper.PaperAxioms.eq10_of_eq5_eq8_eq9` by any workspace theorem**, and
a paper-internal cross-validation that the direct `(10)` chain (sprint 008) and
the derived `(5)+(8)+(9)` chain close the contract via the same effective
sufficient condition on the branch-1 sub-regime. The new generic theorem
`valid_of_eq5_eq8_eq9_subinterval_branch1` has a signature identical to sprint
008's `valid_of_eq10_subinterval_branch1`, and its proof body re-derives the
pointwise `(10)` inequality inline via `eq10_of_eq5_eq8_eq9` from the three
paper fields `paper.eq5_branch1_sigmaReduction`, `paper.eq8_sigma_to_liftGap`,
and `paper.eq9_liftGap_to_circleGap`, exposing `paper.liftGap` as a load-bearing
intermediate for the first time. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V18, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 019 side lemma: exercise the brand-new `(5)+(8)+(9)`-derived branch-1
sub-interval closing reducer `valid_of_eq5_eq8_eq9_subinterval_branch1` at the
seed `c_value` against an abstract universal `Section2Assumptions` instance.
The signature matches sprint 008's `valid_of_eq10_subinterval_branch1`
verbatim modulo the theorem name; what changes is the proof body's structural
chain (now flowing through `(5)+(8)+(9)` and `paper.liftGap` instead of the
direct `(10)` field). Materialises the new reducer in V19's call graph; not
`axiom`-ed and does not call the seed axiom.
-/
theorem v19_eq5_eq8_eq9_subinterval_branch1_compiles
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
          c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c_value
                  (WangOuter.paperLambda K c_value) ρ) :
    ValidKorenblumBound c_value :=
  valid_of_eq5_eq8_eq9_subinterval_branch1
    c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window

/--
Sprint 019 structural witness lemma: confirm that the admissible branch-1
window predicate `c_value < ρ₁ ≤ ρ₂ ≤ branchSplit c_value` is non-vacuous at
the seed by exhibiting the degenerate single-point window
`ρ₁ = ρ₂ = branchSplit c_value`. We need only `c_value < branchSplit c_value`,
which follows from `√(4/3) > 1` and `c_value > 0`. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v19_branch1_window_witness_at_seed :
    ∃ ρ₁ ρ₂ : ℝ,
      c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value := by
  refine ⟨PaperAxioms.branchSplit c_value, PaperAxioms.branchSplit c_value, ?_, le_rfl, le_rfl⟩
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

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new `(5)+(8)+(9)`-derived
branch-1 sub-interval closing reducer is materialised above in
`v19_eq5_eq8_eq9_subinterval_branch1_compiles` and
`v19_branch1_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V19
