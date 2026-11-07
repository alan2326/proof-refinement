-- @parent V27
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V28

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V27 — sprint 028 ships
the workspace's **first paper-axiom-free proof of the inequality direction of
`paper.eq2_sigmaZeroMinus_lower`** (Wang's printed equation `(2)`,
`Z_r ≥ ((ρ²-r²)/(ρ²-c²)) · Z_c − ((c²-r²)/(ρ²-c²)) · Z_ρ`), and the **first
workspace `tsum_le_tsum` argument that consumes a Mathlib `ConvexOn` instance**
(`convexOn_pow (k-1)` from `Mathlib/Analysis/Convex/Mul.lean:157`). The new
generic theorem `sigmaZeroMinus_lower_via_series_convexity` is parameterised
only by `(a, b)`, three radii `0 ≤ r < c < ρ`, and a single summability
premise on the N2-restricted summand at the upper anchor `ρ`; it is **not** a
closing reducer for `ValidKorenblumBound c`, but a structural cross-radius
inequality that opens the `Z`-side `eq2`-substitution axis for downstream
consumers. The sink theorem is still discharged via `valid_of_eq15` so the
score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V27, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 028 side lemma: exercise the brand-new series-level cross-radius
*convexity* inequality `sigmaZeroMinus_lower_via_series_convexity` at the
seed via concrete radii `r := 0`, `c := c_value`, `ρ := 1/2`. The signature
exhibits the new lemma's hypothesis shape — only four cells: non-negativity
of the lower radius, strict ordering `r < c < ρ`, summability of the
N2-indicator summand at the upper anchor `ρ`. The proof body is a single
application of the new generic lemma. Not `axiom`-ed and does not call the
seed axiom.
-/
theorem v28_sigmaZeroMinus_eq2_via_series_convexity_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.sigmaZeroMinus a b 0 ≥
      (((1 / 2 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c_value -
        ((c_value ^ 2 - (0 : ℝ) ^ 2) / ((1 / 2 : ℝ) ^ 2 - c_value ^ 2))
          * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ) := by
  have hr_nn : (0 : ℝ) ≤ 0 := le_refl _
  have hr_lt_c : (0 : ℝ) < c_value := c_value_pos
  have hc_lt_ρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  exact sigmaZeroMinus_lower_via_series_convexity
    a b hr_nn hr_lt_c hc_lt_ρ hSummable

/--
Sprint 028 structural witness lemma: confirm that the new lemma's inequality
at concrete radii `(r, c, ρ) = (0, c_value, 1/2)` reproduces the conclusion
of `paper.eq2_sigmaZeroMinus_lower` *without* invoking
`paper.eq2_sigmaZeroMinus_lower` anywhere in the proof body. The `paper`
parameter is present only as a structural witness that the inequality's
*type* matches what `paper.eq2` would produce; the actual proof discharges
through sprint 028 alone. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v28_sigmaZeroMinus_eq2_via_series_convexity_recovers_eq2_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (1 / 2 : ℝ) ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.Eq2SigmaZeroMinusLower
      (PaperAxioms.sigmaZeroMinus a b) 0 c_value (1 / 2 : ℝ) := by
  -- Sprint 028's inequality gives the conclusion directly,
  -- without invoking `paper.eq2_sigmaZeroMinus_lower`.
  have hr_nn : (0 : ℝ) ≤ 0 := le_refl _
  have hr_lt_c : (0 : ℝ) < c_value := c_value_pos
  have hc_lt_ρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  exact sigmaZeroMinus_lower_via_series_convexity
    a b hr_nn hr_lt_c hc_lt_ρ hSummable

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new series-level cross-radius
*convexity* inequality is materialised above in
`v28_sigmaZeroMinus_eq2_via_series_convexity_compiles` and
`v28_sigmaZeroMinus_eq2_via_series_convexity_recovers_eq2_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V28
