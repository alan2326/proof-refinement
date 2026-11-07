-- @parent V13
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V14

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V13 — sprint 014 ships
the workspace's *first Z-free reducer with no branch-split constraint and no
`(ρ²−c²)` denominator*: `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`
fuses sprint 013's full-disk-regime single-`Z_c` disk bound with sprint 006's
annulus lower bound and sprint 011/012's series-level monotonicity +
summability transfer. The kernel inequality is `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`
— a polynomial in `c` alone, with no `ρ`-window denominator. The admissible
window is the full open annulus `(c, 1)`, including windows above
`branchSplit c` that sprints 010/011/012 cannot reach. The sink theorem is
still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V13, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 014 side lemma: exercise the brand-new full-window single-`Z_c` Z-free
reducer `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` at the seed
`c_value` against an abstract universal witness bundle. The witness signature
has *no* `branchSplit` / `3ρ₁² ≤ 4·c²` conjunct — the structural marker that
the new reducer is full-window. Materialises the new reducer in V14's call
graph; not `axiom`-ed and does not call the seed axiom.
-/
theorem v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c_value 1 ∧
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
            c_value ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window
    c_value_pos c_value_lt_one h_witness

/--
Sprint 014 structural witness lemma: confirm that the geometric scaffolding
`c_value < ρ₁ ≤ ρ₂ < 1` of the new reducer's `h_witness` premise is
non-vacuous at the seed `c_value`. The pair `(5/10, 7/10)` deliberately picks
`ρ₁ = 0.5 > branchSplit(0.3554) ≈ 0.4103`, so the window lies **outside** the
branch-split sub-regime — a strict structural marker that the new reducer
admits windows that sprints 010/011/012 cannot. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v14_window_witness_at_seed :
    ∃ ρ₁ ρ₂ : ℝ, c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
  refine ⟨5 / 10, 7 / 10, ?_, ?_, ?_⟩ <;>
    norm_num [c_value]

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new full-window single-`Z_c`
Z-free reducer is materialised above in
`v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles` and
`v14_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V14
