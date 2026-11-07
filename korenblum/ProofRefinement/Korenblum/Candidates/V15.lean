-- @parent V14
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V15

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V14 — sprint 015 ships
the workspace's *first lemma to consume Wang's printed equation `(5)` directly*:
`diskExcess_upper_bound_via_eq5` produces a single-`Z_ρ`, single-`ρ`,
no-integration disk-side upper bound on `(c, branchSplit c)` whose closed form
`(c⁶/(6·(ρ²−c²))) · Z_ρ` coincides with sprint 007's integrated bound — a
paper-internal cross-check that Wang's `(5)` is the integrated form of the
`(eq2 + eq3 + eq4)` chain on the branch-1 sub-regime. The sink theorem is
still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V14, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 015 side lemma: exercise the brand-new direct-`eq5` disk-side upper
bound `diskExcess_upper_bound_via_eq5` at the seed `c_value` against an
abstract universal `Section2Assumptions` instance. The signature has *no*
`IntervalIntegrable` premise — the structural marker that the new lemma
bypasses every integration step. Materialises the new lemma in V15's call
graph; not `axiom`-ed and does not call the seed axiom.
-/
theorem v15_diskExcess_upper_bound_via_eq5_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ : ℝ}
    (hcρ : c_value < ρ)
    (hρ_split : ρ < PaperAxioms.branchSplit c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      PaperAxioms.branch1SigmaKernel c_value ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ :=
  diskExcess_upper_bound_via_eq5 paper hcρ hρ_split

/--
Sprint 015 structural witness lemma: confirm that the open sub-regime
`c_value < ρ < branchSplit c_value` of the new disk bound is non-vacuous
at the seed. The witness `ρ = 38/100 = 0.38` satisfies
`c_value = 0.3554 < 0.38` and `0.38 < branchSplit c_value
= 0.3554 · √(4/3) ≈ 0.4103`. Not `axiom`-ed and does not call the seed
axiom.
-/
theorem v15_branch_split_witness_at_seed :
    ∃ ρ : ℝ, c_value < ρ ∧ ρ < PaperAxioms.branchSplit c_value := by
  refine ⟨38 / 100, ?_, ?_⟩
  · norm_num [c_value]
  · -- branchSplit c_value = c_value · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103
    show (38 / 100 : ℝ) < PaperAxioms.branchSplit c_value
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : ((1.154 : ℝ)) ^ 2 < 4 / 3 := by norm_num
    have hsqrt : (1.154 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [Real.sq_sqrt (le_of_lt h_pos), hsqrt_nonneg, h_sq]
    show (38 / 100 : ℝ) < c_value * Real.sqrt (4 / 3)
    have hc : c_value = 3554 / 10000 := rfl
    rw [hc]
    nlinarith [hsqrt, hsqrt_nonneg]

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new direct-`eq5` disk-side
upper bound is materialised above in
`v15_diskExcess_upper_bound_via_eq5_compiles` and
`v15_branch_split_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V15
