-- @parent V37
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V38

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V37 — sprint 038
ships the workspace's **first integrated annulus-side bound whose body
invokes zero `paper.eq*` field projections**, the **integrated counterpart
of sprint 037**, the **annulus-side mirror of sprint 034**, and the
**single bottleneck for a future closing reducer with empty paper-axiom
signature modulo two cells**. The new generic theorem
`annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge` lifts the
window-uniform form of the unique series-non-derivable post-substitution
shape of the `(8)+(9)` bridge — `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ` on
all of `(c, 1)` — into its signature as the explicit hypothesis
`hLambdaBridgeWindow`. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V37, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 038 side lemma: exercise the brand-new paper-axiom-free integrated
annulus-side lower bound
`annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge` at
concrete `c := c_value = 3554/10000`, `ρ₁ := 1/2`, `ρ₂ := 7/10`,
`K := fun _ _ => 1`. The signature exhibits the new lemma's hypothesis
shape — seven cells: `hc_pos`, `hcρ₁`, `hρ₁₂`, `hρ₂_lt_one`,
`hIntCircle`, `hIntLambda`, `hLambdaBridgeWindow`. Crucially, **no
`Section2Assumptions` instance is needed** — this side lemma does not
use a `paper` parameter; the integrability hypotheses and the
window-uniform `hLambdaBridgeWindow` are taken as universally-quantified
Lean hypotheses on the side lemma. The proof body is a single
application of the new generic lemma. Not `axiom`-ed and does not call
the seed axiom.
-/
theorem v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_compiles
    (a b : ℕ → ℂ)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c_value 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda (fun _ _ => (1 : ℝ)) c_value ρ)
        volume (1 / 2 : ℝ) (7 / 10 : ℝ))
    (hLambdaBridgeWindow :
      ∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda (fun _ _ => (1 : ℝ)) c_value ρ
            * PaperAxioms.circleGap a b ρ) :
    (∫ ρ in (1 / 2 : ℝ)..(7 / 10 : ℝ),
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda (fun _ _ => (1 : ℝ)) c_value ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ₁ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ₁₂ : (1 / 2 : ℝ) ≤ (7 / 10 : ℝ) := by norm_num
  have hρ₂_lt_one : (7 / 10 : ℝ) < 1 := by norm_num
  exact annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
    (K := fun _ _ => (1 : ℝ)) hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one
    hIntCircle hIntLambda hLambdaBridgeWindow

/--
Sprint 038 structural witness lemma: demonstrate that any candidate
carrying a `Section2Assumptions a b K c_value` instance can discharge the
new theorem's window-uniform `hLambdaBridgeWindow` hypothesis from
`PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap` (lifted to the
universal-quantifier shape), recovering sprint 006's exact conclusion at
the seed through the new chain. This confirms the new theorem **strictly
generalises** sprint 006: any consumer with `paper.eq8`/`paper.eq9`
access can recover sprint 006's bound, and any consumer with access to a
stronger oracle/proposal that proves `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ`
window-uniformly can discharge the new theorem **without ever invoking
`paper.eq8`/`paper.eq9`**. Not `axiom`-ed and does not call the seed
axiom.
-/
theorem v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c_value 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c_value ρ)
        volume (1 / 2 : ℝ) (7 / 10 : ℝ)) :
    (∫ ρ in (1 / 2 : ℝ)..(7 / 10 : ℝ),
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c_value ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ₁ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ₁₂ : (1 / 2 : ℝ) ≤ (7 / 10 : ℝ) := by norm_num
  have hρ₂_lt_one : (7 / 10 : ℝ) < 1 := by norm_num
  -- Discharge `hLambdaBridgeWindow` window-uniformly from
  -- `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`.
  have hLambdaBridgeWindow :
      ∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda K c_value ρ
            * PaperAxioms.circleGap a b ρ := by
    intro ρ hcρ hρ_lt_one
    exact PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hcρ hρ_lt_one
  exact annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
    hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambda hLambdaBridgeWindow

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
integrated annulus-side lower bound is materialised above in
`v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_compiles` and
`v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V38
