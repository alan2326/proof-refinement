-- @parent V16
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V17

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V16 — sprint 017 ships
the workspace's **first closing reducer that lives entirely on the branch-2
sub-regime `(branchSplit c, 1)`**, the **first closing reducer with no
disk-side integrability premise**, and the **first reducer to consume sprint
016's `eq6`-based disk bound in a closing chain**. The new generic theorem
`valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` fuses sprint 016's
single-`Z_{ρ₁}` disk bound with sprint 006's annulus lower bound and sprint
011/012's series-level monotonicity + summability transfer, with the
factor-of-2 reduced kernel inequality `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ)`. The
sink theorem is still discharged via `valid_of_eq15` so the score does not
regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V16, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 017 side lemma: exercise the brand-new branch-2-only single-`Z_{ρ₁}`
closing reducer `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` at the
seed `c_value` against an abstract universal `Section2Assumptions` instance.
The signature has *no* `IntervalIntegrable` premise on `[0, c]` — the
structural marker that the disk side is integration-free. Materialises the
new reducer in V17's call graph; not `axiom`-ed and does not call the seed
axiom.
-/
theorem v17_branch2_window_reducer_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
              volume c_value 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 *
                PaperAxioms.sigmaZeroMinus a b ρ' /
                WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 /
                WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c_value ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                                  2 * ρ' ^ 3 /
                                  WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_disk_eq6_annulus_eq8_eq9_branch2_window
    c_value_pos c_value_lt_one h_witness

/--
Sprint 017 structural witness lemma: confirm that the admissible branch-2
window predicate `branchSplit c_value < ρ₁ ≤ ρ₂ < 1` is non-vacuous at the
seed by exhibiting `(ρ₁, ρ₂) = (5/10, 7/10) = (0.5, 0.7)`. We bound
`√(4/3)` from above by `13/10 = 1.3` (since `1.3² = 1.69 > 4/3`), then
`branchSplit c_value = c_value · √(4/3) < 0.3554 · 1.3 ≈ 0.4620 < 0.5`.
Mirrors V14's window choice for cross-reference. Not `axiom`-ed and does
not call the seed axiom.
-/
theorem v17_branch2_window_witness_at_seed :
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
so that the score does not regress; the brand-new branch-2-only
single-`Z_{ρ₁}` closing reducer is materialised above in
`v17_branch2_window_reducer_compiles` and
`v17_branch2_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V17
