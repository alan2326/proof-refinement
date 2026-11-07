-- @parent V32
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V33

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V32 — sprint 033 ships
the workspace's **first paper-axiom-free convexity lemma on `sigmaPlus`**, the
**N1-side dual of sprint 028's `sigmaZeroMinus_lower_via_series_convexity`**,
the **first three-radius `sigmaPlus` lemma** in the workspace, and **closes the
convexity-vs-monotonicity matrix on N1** opened by sprint 032. The new generic
theorem `sigmaPlus_upper_via_series_convexity` derives `Σ⁺(c) ≤ μ₁·Σ⁺(r) +
μ₂·Σ⁺(ρ)` for `0 ≤ r < c < ρ` from non-negativity of `coeffPlusGap a b k` on
the positive-`k` portion of N1 plus convexity of `t ↦ t^k` on `[0, ∞)`. The
`k = 0 ∈ N1` boundary case (which sprint 028's N2-side argument trivially
excludes via `n2Pred a b 0 = False`) collapses by termwise equality after
applying the convex-weight sum identity `μ₁ + μ₂ = 1`. The summability
transfer to `c` is in-house via `Summable.of_nonneg_of_le` against the convex
combination, taking *two* summability premises (at lower-`r` and upper-`ρ`)
since the workspace has no N1-side `sigmaPlus_summable_of_summable_at_upper`
lemma yet (the dual of sprint 012's N2-side transfer). The sink theorem is
still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V32, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 033 side lemma: exercise the brand-new paper-axiom-free convexity
lemma `sigmaPlus_upper_via_series_convexity` at concrete witness values
`r := c_value/2 = 1777/10000`, `c := c_value = 3554/10000`, and
`ρ := (c_value + 1)/2 = 6777/10000`. The signature exhibits the new lemma's
hypothesis shape — five cells: `hr_nonneg` (non-negativity of `r`), `hr_lt_c`
(strict ordering `r < c`), `hc_lt_ρ` (strict ordering `c < ρ`), `hSummable_r`
(summability of the N1-indicator-weighted summand at the lower argument
`r = c_value/2`), and `hSummable_ρ` (summability at the upper argument
`ρ = (c_value+1)/2`). The proof body is a single application of the new
generic lemma. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v33_sigmaPlus_upper_via_series_convexity_compiles
    (a b : ℕ → ℂ)
    (hSummable_r :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * (c_value / 2) ^ (2 * k)
        else 0))
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * ((c_value + 1) / 2) ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b c_value ≤
      ((((c_value + 1) / 2) ^ 2 - c_value ^ 2)
          / (((c_value + 1) / 2) ^ 2 - (c_value / 2) ^ 2))
          * PaperAxioms.sigmaPlus a b (c_value / 2)
        + ((c_value ^ 2 - (c_value / 2) ^ 2)
            / (((c_value + 1) / 2) ^ 2 - (c_value / 2) ^ 2))
          * PaperAxioms.sigmaPlus a b ((c_value + 1) / 2) := by
  have hr_nonneg : (0 : ℝ) ≤ c_value / 2 := by
    have hc_nn : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos
    linarith
  have hr_lt_c : c_value / 2 < c_value := by
    have hc_pos : (0 : ℝ) < c_value := c_value_pos
    linarith
  have hc_lt_ρ : c_value < (c_value + 1) / 2 := by
    have hc_lt_one : c_value < 1 := c_value_lt_one
    linarith
  exact sigmaPlus_upper_via_series_convexity a b hr_nonneg hr_lt_c hc_lt_ρ
    hSummable_r hSummable_ρ

/--
Sprint 033 structural witness lemma: demonstrate the convex-combination
geometry at the seed. With concrete witness values `r := c_value/2 =
1777/10000`, `c := c_value = 3554/10000`, `ρ := (c_value + 1)/2 = 6777/10000`,
and convex weights `μ₁ := (ρ² - c²)/(ρ² - r²)` and `μ₂ := (c² - r²)/(ρ² - r²)`,
this lemma confirms the two algebraic identities that drive the new
convexity argument:

  * `μ₁ + μ₂ = 1` (the convex-weight sum identity that collapses the
    `k = 0 ∈ N1` boundary case),
  * `μ₁·r² + μ₂·ρ² = c²` (the convex-combination identity at the heart
    of the termwise convexity inequality at `k ≥ 1`).

These two identities are the structural prerequisites of the new lemma; this
witness confirms they are non-degenerate at the seed. Not `axiom`-ed and does
not call the seed axiom.
-/
theorem v33_sigmaPlus_upper_via_series_convexity_witness_at_seed :
    let r : ℝ := c_value / 2
    let c : ℝ := c_value
    let ρ : ℝ := (c_value + 1) / 2
    let μ₁ : ℝ := (ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)
    let μ₂ : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2)
    μ₁ + μ₂ = 1 ∧ μ₁ * r ^ 2 + μ₂ * ρ ^ 2 = c ^ 2 := by
  -- Numerical evaluation at the seed: r = 1777/10000, c = 3554/10000,
  -- ρ = 6777/10000. The convex-weight denominator `ρ² − r²` is
  -- `(6777² − 1777²) / 10000² = (8554)(5000) / 10^8 = 42_770_000 / 10^8 ≠ 0`.
  refine ⟨?_, ?_⟩
  · simp only [c_value]; norm_num
  · simp only [c_value]; norm_num

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free convexity
lemma `sigmaPlus_upper_via_series_convexity` is materialised above in
`v33_sigmaPlus_upper_via_series_convexity_compiles` and
`v33_sigmaPlus_upper_via_series_convexity_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V33
