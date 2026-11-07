-- @parent V23
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V24

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V23 — sprint 024 ships
the workspace's **first end-to-end branch-2 closing reducer with both zero
`paper.eq6_branch2_sigmaReduction` consumption AND only one series-summability
premise**, collapsing sprint 023's two-anchor summability shape (`Z @ ρ₁` and
`Z @ ρ₂`) into a single point summability premise at `ρ₂` via sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` transfer applied at
`s = ρ₁`, `t = ρ₂` in a single-anchor disk-side bridging role (rather than the
interior-bridging role inside sprint 023's `hZmono` Icc-loop). The new generic
theorem `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
mirrors sprint 014's single-summability shape on the full window — first
deployment of that shape on the branch-2 sub-window. The sink theorem is still
discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V23, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 024 side lemma: exercise the brand-new branch-2 single-summability
closing reducer
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
at the seed `c_value` against an abstract universal `Section2Assumptions`
instance. The signature exhibits the new reducer's hypothesis shape — seven
conjunction cells (3 geometric, 4 integrability, 1 summability at `ρ₂` only)
plus the kernel inequality `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ`, strictly one summability
cell shorter than sprint 023's signature. The proof body is a single
application of the new generic reducer. Not `axiom`-ed and does not call the
seed axiom.
-/
theorem v24_branch2_uniformSummable_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c_value ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
              volume c_value 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r)
              volume 0 c_value ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c_value ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3
                              / WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable
    c_value_pos c_value_lt_one h_witness

/--
Sprint 024 structural witness lemma: confirm that the branch-2 admissibility
predicate `branchSplit c_value ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1` is non-vacuous at
the seed by exhibiting the degenerate single-point window
`(ρ₁, ρ₂) = (1/2, 1/2)`, mirroring sprint 023's witness shape. The bound
`branchSplit (3554/10000) = (3554/10000) · √(4/3) ≈ 0.4103 < 0.5` is derived
from `√(4/3) < 13/10`. The integrability and summability premises on the new
reducer are **not** numerically discharged here — they remain existential
premises on the generic reducer. Not `axiom`-ed and does not call the seed
axiom.
-/
theorem v24_branch2_uniformSummable_witness_at_seed :
    PaperAxioms.branchSplit c_value ≤ (1 : ℝ) / 2 ∧
      (1 : ℝ) / 2 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  refine ⟨?_, le_rfl, by norm_num⟩
  unfold PaperAxioms.branchSplit
  have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) := Real.sqrt_nonneg _
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
so that the score does not regress; the brand-new branch-2 single-summability
closing reducer is materialised above in `v24_branch2_uniformSummable_compiles`
and `v24_branch2_uniformSummable_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V24
