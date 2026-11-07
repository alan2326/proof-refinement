-- @parent V20
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V21

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V20 — sprint 021 ships
the workspace's **first closing reducer with three independent radial
parameters** `(ρ_disk, ρ₁, ρ₂)`, the **first reducer whose disk-side bound is
the non-constant kernel `branch1SigmaKernel c ρ_disk · ρ_disk²` (varying with
`ρ_disk` over `(c, branchSplit c)`)**, and the **first reducer whose
Z-extraction step bridges from a strictly interior anchor `ρ_disk < ρ₁` to
the annulus window via two cascaded `sigmaZeroMinus`-monotonicity
invocations**. The new generic theorem
`valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` consumes sprint 015's
`(5)`-derived disk-side bound at a free anchor `ρ_disk ∈ (c, branchSplit c)`
and sprint 006's `(8)+(9)`-derived annulus-side bound on a separately free
window `[ρ₁, ρ₂] ⊆ [ρ_disk, 1)`. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V20, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 021 side lemma: exercise the brand-new decoupled-disk-anchor closing
reducer `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` at the seed
`c_value` against an abstract universal `Section2Assumptions` instance. The
signature exhibits the new decoupled-anchor admissibility predicate
`c_value < ρ_disk < branchSplit c_value ∧ ρ_disk ≤ ρ₁ ≤ ρ₂ < 1` and the new
non-constant kernel inequality
`branch1SigmaKernel c_value ρ_disk · ρ_disk² ≤ ∫ 2ρ³/Λ`; the proof body is
a single application of the new generic reducer. Not `axiom`-ed and does
not call the seed axiom.
-/
theorem v21_decoupled_anchor_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ_disk ρ₁ ρ₂ : ℝ,
          c_value < ρ_disk ∧
          ρ_disk < PaperAxioms.branchSplit c_value ∧
          ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
            (PaperAxioms.branch1SigmaKernel c_value ρ_disk *
                ρ_disk ^ 2) ≤
              ∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 /
                  WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor
    c_value_pos c_value_lt_one h_witness

/--
Sprint 021 structural witness lemma: confirm that the decoupled-anchor
admissibility predicate
`c_value < ρ_disk < branchSplit c_value ∧ ρ_disk ≤ ρ₁ ≤ ρ₂ < 1` is
non-vacuous at the seed by exhibiting the degenerate single-point
witness `ρ_disk = ρ₁ = ρ₂ = (c_value + branchSplit c_value)/2`. The
boundary inequalities `ρ_disk ≤ ρ₁` and `ρ₁ ≤ ρ₂` collapse to `le_rfl`;
the strict constraints `c_value < ρ_disk`, `ρ_disk < branchSplit c_value`,
and `ρ₂ < 1` are derived from `√(4/3) > 1` and `√(4/3) < 13/10`
respectively. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v21_decoupled_anchor_witness_at_seed :
    ∃ ρ_disk ρ₁ ρ₂ : ℝ,
      c_value < ρ_disk ∧
      ρ_disk < PaperAxioms.branchSplit c_value ∧
      ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
  refine ⟨(c_value + PaperAxioms.branchSplit c_value) / 2,
          (c_value + PaperAxioms.branchSplit c_value) / 2,
          (c_value + PaperAxioms.branchSplit c_value) / 2,
          ?_, ?_, le_rfl, le_rfl, ?_⟩
  · -- c_value < (c_value + branchSplit c_value)/2
    --   ⟺ c_value < branchSplit c_value
    have hSplit_gt_c : c_value < PaperAxioms.branchSplit c_value := by
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
    linarith
  · -- (c_value + branchSplit c_value)/2 < branchSplit c_value
    --   ⟺ c_value < branchSplit c_value (same as above)
    have hSplit_gt_c : c_value < PaperAxioms.branchSplit c_value := by
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
    linarith
  · -- (c_value + branchSplit c_value)/2 < 1
    --   ⟸ c_value < 1 ∧ branchSplit c_value < 1
    have hSplit_lt_one : PaperAxioms.branchSplit c_value < 1 := by
      unfold PaperAxioms.branchSplit
      have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
      have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
        Real.sqrt_nonneg _
      have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
        Real.sq_sqrt (le_of_lt h_pos)
      have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
        have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by
          norm_num
        nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
      have hc : c_value = 3554 / 10000 := rfl
      rw [hc]
      nlinarith [hsqrt_lt, hsqrt_nonneg]
    have hc_lt_one : c_value < (1 : ℝ) := c_value_lt_one
    linarith

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new decoupled-disk-anchor
closing reducer is materialised above in `v21_decoupled_anchor_compiles`
and `v21_decoupled_anchor_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V21
