-- @parent V36
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V37

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V36 — sprint 037 ships
the workspace's **first paper-axiom-free annulus-side bound of any kind**, the
**annulus-side mirror of sprint 036**, and the **first lemma to fuse sprint
005 with an explicit `hLambdaBridge` cell into a single pointwise outer
chain**. The new generic theorem
`circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge` lifts the
unique series-non-derivable post-substitution form of the `(8)+(9)` bridge —
`Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ` — into its signature as the explicit
hypothesis `hLambdaBridge`. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V36, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 037 side lemma: exercise the brand-new paper-axiom-free pointwise
outer-annulus single-`Z` lower bound
`circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge` at
concrete `c := c_value = 3554/10000`, `ρ := 1/2`, `K := fun _ _ => 1`. The
signature exhibits the new lemma's hypothesis shape — four cells:
`hc_pos`, `hcρ`, `hρ1`, `hLambdaBridge`. Crucially, **no
`Section2Assumptions` instance is needed** — this side lemma does not use a
`paper` parameter; the `hLambdaBridge` hypothesis is taken as a
universally-quantified Lean hypothesis on the side lemma. The proof body
is a single application of the new generic lemma. Not `axiom`-ed and does
not call the seed axiom.
-/
theorem v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_compiles
    (a b : ℕ → ℂ)
    (hLambdaBridge :
      PaperAxioms.sigmaMinus a b (1 / 2 : ℝ) ≤
        WangOuter.paperLambda (fun _ _ => (1 : ℝ)) c_value (1 / 2 : ℝ)
          * PaperAxioms.circleGap a b (1 / 2 : ℝ)) :
    2 * (1 / 2 : ℝ) ^ 3 * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ)
        / WangOuter.paperLambda (fun _ _ => (1 : ℝ)) c_value (1 / 2 : ℝ)
      ≤ 2 * (1 / 2 : ℝ) * PaperAxioms.circleGap a b (1 / 2 : ℝ) := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
    (K := fun _ _ => (1 : ℝ)) hc_pos hcρ hρ1 hLambdaBridge

/--
Sprint 037 structural witness lemma: demonstrate that any candidate carrying a
`Section2Assumptions a b K c_value` instance can discharge the new theorem's
`hLambdaBridge` hypothesis from
`PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9 paper.eq8_sigma_to_liftGap
paper.eq9_liftGap_to_circleGap hcρ hρ1`, recovering sprint 005's exact
conclusion at the seed through the new chain. This confirms the new theorem
**strictly generalises** sprint 005: any consumer with `paper.eq8`/`paper.eq9`
access can recover sprint 005's bound, and any consumer with access to a
stronger oracle/proposal that proves `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ`
independently can discharge the new theorem **without ever invoking
`paper.eq8`/`paper.eq9`**. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value) :
    2 * (1 / 2 : ℝ) ^ 3 * PaperAxioms.sigmaZeroMinus a b (1 / 2 : ℝ)
        / WangOuter.paperLambda K c_value (1 / 2 : ℝ)
      ≤ 2 * (1 / 2 : ℝ) * PaperAxioms.circleGap a b (1 / 2 : ℝ) := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hcρ : c_value < (1 / 2 : ℝ) := by norm_num [c_value]
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  -- Discharge `hLambdaBridge` from the (8)+(9) bridge constructor at the
  -- seed; this is precisely the substitution sprint 037 lifts to a
  -- hypothesis cell.
  have hLambdaBridge :
      PaperAxioms.sigmaMinus a b (1 / 2 : ℝ) ≤
        WangOuter.paperLambda K c_value (1 / 2 : ℝ)
          * PaperAxioms.circleGap a b (1 / 2 : ℝ) :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ1
  exact circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
    hc_pos hcρ hρ1 hLambdaBridge

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free pointwise
outer-annulus single-`Z` lower bound is materialised above in
`v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_compiles` and
`v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V37
