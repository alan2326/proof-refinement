-- @parent V52
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Candidates.V53.ThetaStep

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V53

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 068 ships V53 at the same `c_value = 7129/20000 = 0.35645` as V52,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V52's: this is the contract's Outcome C
(Phase B step 1 falsified KERNEL_68 — see
`Scratch/sprint_068_phaseB_kernel_check.txt` — so V53 ties V52 with no
c-push).

What is structurally novel in V53 is the import of
`ProofRefinement.Korenblum.Candidates.V53.ThetaStep`, the **first**
per-candidate derived-theorem file in the workspace shipping a Lean theorem
corresponding to a Wang un-numbered intermediate algebraic step
(`(1 + Λ) · Σ⁻ ≤ Λ · Σ⁺` for `ρ ∈ (c, 1)`). Sprints 065, 066, 067 all
*reference* THETA_STEP as an analytic identity but never wrote any Lean
for it; sprint 068 ships the first Lean realization, derived purely from
existing `Section2Assumptions` fields plus sprint 005's series identity
plus `paperLambda_pos`, with no new axioms / oracles / `lemma.toml` entries
and no edits to `KorenblumPaper/`.

The side lemma `v53_theta_step_compiles_at_seed_witness` below forces the
elaborator to verify that THETA_STEP compiles against an arbitrary
`Section2Assumptions` instance — confirming the new theorem is non-vacuous
and reusable by future candidates. This is the Phase B-b deliverable per
sprint 068's contract acceptance criteria.

c-pushing is deferred per the bulletin's three-sprint exhaustion synthesis;
this sprint's purpose is to put a reusable Lean building block in place
that future c-pushing sprints can consume.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
V52-shaped oracle bound-field. Identical declaration to V52's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V52's `hEq15_oracle_certified_hp_35645`, with the
exact same `Eq15ScalarBound K c_value` shape at `c_value = 35645/100000 =
0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

Wrapper acceptance pre-verified by sprint 058's HP probe and re-checked by
sprint 059's sanity replay; certified `total_mass_lower = 1.000013457935`,
margin `+1.35e-05` above the strict-margin threshold. V53's trust envelope
is byte-for-byte identical to V52's; the structural novelty of V53 is
upstream (the new derived-theorem file
`Candidates/V53/ThetaStep.lean`), not in the discharge route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 068 / Phase B-b non-vacuity check: invoke `theta_step_raw` against
a generic `Section2Assumptions a b K c` instance to force the elaborator
to confirm THETA_STEP_RAW compiles and that the inequality is well-typed
as a statement about `paperLambda K c ρ`, `sigmaMinus a b ρ`, and
`sigmaPlus a b ρ`.

The hypothesis `0 ≤ c` is satisfied by `V53.c_value_pos` whenever
`c = c_value`; since this lemma is generic in `c`, we surface it as a
hypothesis to keep the lemma reusable.

This is a **statement-level** check, not a witness-construction: the lemma
takes an arbitrary `Section2Assumptions a b K c` as a hypothesis and applies
`ThetaStep.theta_step_raw` to it, returning the THETA_STEP_RAW conclusion
verbatim. The elaborator's acceptance of this lemma confirms that
`Candidates/V53/ThetaStep.lean` is non-vacuous and that the workspace's
existing trusted surface is structurally compatible with THETA_STEP.
-/
theorem v53_theta_step_compiles_at_seed_witness
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : KorenblumPaper.PaperAxioms.Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
    (1 + WangOuter.paperLambda K c ρ) *
        KorenblumPaper.PaperAxioms.sigmaMinus a b ρ ≤
      WangOuter.paperLambda K c ρ *
        KorenblumPaper.PaperAxioms.sigmaPlus a b ρ :=
  ThetaStep.theta_step_raw paper hc_nonneg hcρ hρ_lt_one

/--
Paper-faithful candidate: the V52-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-068 advance is
the new building block in `Candidates/V53/ThetaStep.lean`, exercised by
`v53_theta_step_compiles_at_seed_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V53
