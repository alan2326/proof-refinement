-- @parent V15
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V16

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V15 — sprint 016 ships
the workspace's *first lemma to consume Wang's printed equation `(6)` directly*:
`diskExcess_upper_bound_via_eq6` produces a single-`Z_ρ`, single-`ρ`,
no-integration disk-side upper bound on the branch-2 sub-regime
`(branchSplit c, 1)` whose closed form `(c⁴/2) · Z_ρ` (after the algebraic
collapse `branch2SigmaKernel c ρ · ρ² = c⁴/2`) is the **first workspace
disk-bound coefficient that is constant in `ρ`**. Together with sprint 015,
this completes the disk-side coverage of Wang's equations
{`eq2`, `eq3`, `eq4`, `eq5`, `eq6`}. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V15, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 016 side lemma: exercise the brand-new direct-`eq6` disk-side upper
bound `diskExcess_upper_bound_via_eq6` at the seed `c_value` against an
abstract universal `Section2Assumptions` instance. The signature has *no*
`IntervalIntegrable` premise — the structural marker that the new lemma
bypasses every integration step. Materialises the new lemma in V16's call
graph; not `axiom`-ed and does not call the seed axiom.
-/
theorem v16_diskExcess_upper_bound_via_eq6_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ : ℝ}
    (hρ_split : PaperAxioms.branchSplit c_value < ρ)
    (hρ1 : ρ < 1) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      PaperAxioms.branch2SigmaKernel c_value ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ :=
  diskExcess_upper_bound_via_eq6 paper hρ_split hρ1

/--
Sprint 016 structural witness lemma: confirm that the open sub-regime
`branchSplit c_value < ρ < 1` of the new disk bound is non-vacuous at the
seed. The witness `ρ = 5/10 = 0.5` satisfies `branchSplit c_value
= c_value · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103 < 0.5 < 1`. We bound
`√(4/3)` from above by `13/10 = 1.3` (since `1.3² = 1.69 > 4/3`), then
`c_value · √(4/3) < 0.3554 · 1.3 ≈ 0.4620 < 0.5`. Not `axiom`-ed and does
not call the seed axiom.
-/
theorem v16_branch2_witness_at_seed :
    ∃ ρ : ℝ, PaperAxioms.branchSplit c_value < ρ ∧ ρ < 1 := by
  refine ⟨5 / 10, ?_, ?_⟩
  · -- branchSplit c_value = c_value · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103
    show PaperAxioms.branchSplit c_value < (5 / 10 : ℝ)
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    -- `√(4/3) < 13/10` since `(13/10)² = 169/100 > 4/3 = 133.33.../100`.
    have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
      have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by norm_num
      nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
    have hc : c_value = 3554 / 10000 := rfl
    rw [hc]
    nlinarith [hsqrt_lt, hsqrt_nonneg]
  · norm_num

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new direct-`eq6` disk-side
upper bound is materialised above in
`v16_diskExcess_upper_bound_via_eq6_compiles` and
`v16_branch2_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V16
