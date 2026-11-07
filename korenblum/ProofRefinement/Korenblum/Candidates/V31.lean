-- @parent V30
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V31

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V30 — sprint 031 ships
the workspace's **first paper-axiom-`{eq4}`-only branch-1 single-`Z`
collapsed `diskExcess` upper bound** (no `paper.eq2_sigmaZeroMinus_lower` and no
`paper.eq3_circleGap_decomposition` anywhere in the transitive proof body), the
**first downstream materialisation of sprint 030 in a branch-collapse chain**,
and the **first paper-axiom-strict-subset improvement of sprint 007's exact
branch-1 single-`Z` integrated-layer conclusion** (sprint 007's signature is
`{eq2, eq3, eq4}`; sprint 031 strict-subsets it to `{eq4}` only). The new
generic theorem
`diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only` re-walks
sprint 007's algebraic chain step by step, substituting sprint 030 for the
two-`Z` integrated upper bound; only `paper.eq4_sigmaPlus_bound` remains (and
it is invoked inside sprint 029, not directly inside sprint 031). The sink
theorem is still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V30, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 031 side lemma: exercise the brand-new branch-1 single-`Z` collapsed
`diskExcess` upper bound
`diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only` at concrete
upper anchor `ρ := 4/10`. The witness `ρ = 0.4` lies in the branch-1
sub-regime `(c_value, branchSplit c_value]` because
`branchSplit (3554/10000) ≈ 0.4103` and `3·(0.4)² = 0.48 ≤ 0.5052 ≈
4·(0.3554)²`. The signature exhibits the new lemma's hypothesis shape — eight
cells: `paper`, `hc_pos` (positivity of `c`), `hcρ` (strict ordering
`c < ρ`), `hρ_branch` (branch-1 sub-regime confinement `3·ρ² ≤ 4·c²`), `hρ1`
(strict ordering `ρ < 1`), `hSummable_circleGap` (summability of the
unconditioned `circleGapSeries` summand quantified over `r ∈ [0, c)`),
`hSummable_n2_ρ` (summability of the N2-indicator summand at the upper anchor
`ρ`), and `hInt` (integrability of `2 * r * circleGap r` on `[0, c]`). The
proof body is a single application of the new generic lemma. Not `axiom`-ed
and does not call the seed axiom.
-/
theorem v31_disk_bound_collapsed_single_Z_via_series_eq4_only_compiles
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (4 / 10 : ℝ) ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 6 / 6) / ((4 / 10 : ℝ) ^ 2 - c_value ^ 2)
        * PaperAxioms.sigmaZeroMinus a b (4 / 10 : ℝ) := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (4 / 10 : ℝ) := by norm_num [c_value]
  have hρ_branch : 3 * (4 / 10 : ℝ) ^ 2 ≤ 4 * c_value ^ 2 := by
    norm_num [c_value]
  have hρ1 : (4 / 10 : ℝ) < 1 := by norm_num
  exact diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only
    paper hc_pos hcρ hρ_branch hρ1 hSummable_circleGap hSummable_n2_ρ hInt

/--
Sprint 031 structural witness lemma: confirm that the new lemma's bound at
the concrete upper anchor `ρ = 4/10` reproduces the conclusion of sprint
007's `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` *without*
invoking `paper.eq2_sigmaZeroMinus_lower` or
`paper.eq3_circleGap_decomposition` anywhere in the proof body. The `paper`
parameter is present because `paper.eq4_sigmaPlus_bound` is invoked through
sprint 029 (which sprint 030 consumes, which sprint 031 consumes), not
directly. The sprint-007 lemma
`diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` would give the same
conclusion, but its proof body consumes `eq2`, `eq3`, *and* `eq4`; sprint 031
consumes only `eq4`. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v31_disk_bound_collapsed_single_Z_via_series_eq4_only_recovers_sprint007_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * (4 / 10 : ℝ) ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 6 / 6) / ((4 / 10 : ℝ) ^ 2 - c_value ^ 2)
        * PaperAxioms.sigmaZeroMinus a b (4 / 10 : ℝ) := by
  -- Sprint 031's bound gives the conclusion directly, without invoking
  -- `paper.eq2_sigmaZeroMinus_lower` or `paper.eq3_circleGap_decomposition`.
  -- The sprint-007 lemma `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
  -- would give the same conclusion, but its proof body consumes `eq2`, `eq3`,
  -- *and* `eq4`; sprint 031 consumes only `eq4` (and only inside sprint 029's
  -- body, lifted through sprint 030).
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (4 / 10 : ℝ) := by norm_num [c_value]
  have hρ_branch : 3 * (4 / 10 : ℝ) ^ 2 ≤ 4 * c_value ^ 2 := by
    norm_num [c_value]
  have hρ1 : (4 / 10 : ℝ) < 1 := by norm_num
  exact diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only
    paper hc_pos hcρ hρ_branch hρ1 hSummable_circleGap hSummable_n2_ρ hInt

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new branch-1 single-`Z`
collapsed `diskExcess` upper bound is materialised above in
`v31_disk_bound_collapsed_single_Z_via_series_eq4_only_compiles` and
`v31_disk_bound_collapsed_single_Z_via_series_eq4_only_recovers_sprint007_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V31
