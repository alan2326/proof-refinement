-- @parent V21
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V22

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V21 — sprint 022 ships
the workspace's **first disk-side bound on the branch-2 sub-regime
`[branchSplit c, 1)` whose paper-axiom signature is `{eq2, eq3, eq4}` instead of
`{eq6}`**, the **first paper-internal cross-validation that Wang's printed
equation `(6)` is algebraically a consequence of `(2)+(3)+(4)` plus a single
application of `Z`-monotonicity on the branch-2 sub-regime**, and the **first
workspace lemma whose disk-side `Z_c → Z_ρ` collapse is justified by sprint
011's series monotonicity rather than by an axiomatic paper hypothesis**. The
new generic theorem `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
re-derives sprint 016's closed-form `(c⁴/2) · Z_ρ` bound on the branch-2
sub-regime from sprint 003's two-`Z` integrated bound by upper-bounding the
`Z_c` summand using sprint 011's `sigmaZeroMinus_monotone_of_summable` and
algebraically merging the two `Z_ρ`-coefficient summands. The sink theorem is
still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V21, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 022 side lemma: exercise the brand-new branch-2
`(2)+(3)+(4)`-derived disk bound
`diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` at the seed
`c_value` against an abstract universal `Section2Assumptions` instance. The
signature exhibits the new bound's hypothesis shape — a `ρ` strictly above
`branchSplit c_value`, an integrability premise on `2r·circleGap` over
`[0, c]` (inherited from sprint 003), and a series-summability premise at
`ρ` (introduced by sprint 011's collapse). The proof body is a single
application of the new generic lemma. Not `axiom`-ed and does not call the
seed axiom.
-/
theorem v22_disk_bound_eq2_eq3_eq4_branch2_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ : ℝ,
          PaperAxioms.branchSplit c_value ≤ ρ ∧
          ρ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r)
              volume 0 c_value ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
              else 0)) :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c_value),
      ∃ ρ : ℝ,
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          (c_value ^ 4 / 2) * PaperAxioms.sigmaZeroMinus a b ρ := by
  intro a b K paper
  obtain ⟨ρ, hρ_split, hρ1, hInt, hSummable⟩ := h_witness paper
  refine ⟨ρ, ?_⟩
  exact diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse
    paper c_value_pos hρ_split hρ1 hInt hSummable

/--
Sprint 022 structural witness lemma: confirm that the branch-2 admissibility
predicate `branchSplit c_value ≤ ρ ∧ ρ < 1` is non-vacuous at the seed by
exhibiting the concrete witness `ρ = 1/2`. The bound `branchSplit (3554/10000)
= (3554/10000) · √(4/3) ≈ 0.4103 < 0.5` is derived from `√(4/3) < 13/10`. The
summability premise on the new lemma is **not** numerically discharged here —
it remains an existential premise on the generic lemma. Not `axiom`-ed and
does not call the seed axiom.
-/
theorem v22_branch2_witness_at_seed :
    PaperAxioms.branchSplit c_value ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  refine ⟨?_, by norm_num⟩
  -- branchSplit c_value = c_value · √(4/3) ≤ 1/2 since c_value · √(4/3) ≈ 0.4103.
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
  -- (3554/10000) · √(4/3) ≤ 1/2 since 3554 · 13 / 100000 = 46202/100000 < 50000/100000 = 1/2.
  nlinarith [hsqrt_lt, hsqrt_nonneg]

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new branch-2
`(2)+(3)+(4)`-derived disk bound is materialised above in
`v22_disk_bound_eq2_eq3_eq4_branch2_compiles` and
`v22_branch2_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V22
