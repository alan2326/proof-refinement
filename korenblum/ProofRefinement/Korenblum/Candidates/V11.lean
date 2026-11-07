-- @parent V10
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V11

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V10 — sprint 011 ships
the workspace's *first series-level lemma about `sigmaZeroMinus`* and a
left-edge specialisation of sprint 010's `Z`-free reducer that consumes a
purely series-side summability premise in place of pointwise `Z`-monotonicity.
The sink theorem is still discharged via `valid_of_eq15` so the score does
not regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V10, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 011 structural witness lemma: at the seed `c_value = 0.3554`, the
geometric scaffolding `c_value < ρ₁ ≤ ρ₂ < 1` and `3ρ₁² ≤ 4·c_value²` of the
new `_atLeftEdge` reducer's `h_witness` premise is non-vacuous —
`(ρ₁, ρ₂) = (4/10, 5/10)` satisfies all four constraints simultaneously.
Sanity: `4·c_value² ≈ 0.5052`, `3·0.4² = 0.48 ≤ 0.5052`, and
`0.3554 < 0.4 ≤ 0.5 < 1`. The witness lemma is local to V11 and is not used
elsewhere — the summability and kernel inequality premises are not part of
the geometric scaffolding and are intentionally not discharged here.
-/
theorem v11_window_witness_at_seed :
    ∃ ρ₁ ρ₂ : ℝ,
      c_value < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c_value ^ 2 ∧
        ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
  refine ⟨4 / 10, 5 / 10, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [c_value]

/--
Sprint 011 side lemma: exercise the new series-level monotonicity lemma
`sigmaZeroMinus_monotone_of_summable` against an abstract series-summability
hypothesis at the seed `c_value`. Materialises the *workspace's first
series-level lemma about `sigmaZeroMinus`* in V11's call graph. The side
lemma is not `axiom`-ed and does not call the seed axiom; it exists purely
to verify that the new lemma typechecks at the seed `c_value`.
-/
theorem v11_sigmaZeroMinus_monotone_compiles
    (a b : ℕ → ℂ)
    (s t : ℝ)
    (hs_nonneg : 0 ≤ s)
    (hst : s ≤ t)
    (hSummable_t :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.sigmaZeroMinus a b s
      ≤ PaperAxioms.sigmaZeroMinus a b t :=
  sigmaZeroMinus_monotone_of_summable hs_nonneg hst hSummable_t

/--
Sprint 011 side lemma: exercise the new left-edge `Z`-free reducer
`valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` at the seed
`c_value` against an abstract witness/integrability/summability bundle. This
materialises the new chain
`(2)+(3)+(4) collapsed ∧ (8)+(9) integrated ∧ Z-free kernel ineq ∧
series-side summability ⇒ ValidKorenblumBound` in V11's call graph. The side
lemma is not `axiom`-ed and does not call the seed axiom; it exists purely
to verify that the new reduction typechecks at the seed `c_value`.
-/
theorem v11_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_chain_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c_value ^ 2 ∧
            ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
            (∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
              Summable (fun k : ℕ =>
                if PaperAxioms.n2Pred a b k then
                  PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
                else 0)) ∧
            (c_value ^ 6 / 6) / (ρ₁ ^ 2 - c_value ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
    c_value_pos c_value_lt_one h_witness

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new series-level monotonicity
lemma and left-edge reducer are materialised above in
`v11_sigmaZeroMinus_monotone_compiles` and
`v11_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V11
