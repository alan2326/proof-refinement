-- @parent V54
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V55

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 070 ships V55 at the same `c_value = 7129/20000 = 0.35645` as V54,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V54's: this is the contract's Outcome A
(c-tying sprint by design — the bulletin's three-sprint exhaustion
synthesis and sprint 068's Phase B falsification settle that closed-form
`(a, b)`-independent kernels are exhausted; advancing `c` further requires
per-`k` content that this sprint contributes a building block toward).

What is structurally novel in V55 is the import of
`ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`, the **third**
per-candidate derived-theorem file in the workspace shipping a Lean theorem
corresponding to a Wang un-numbered intermediate algebraic step:

  `liftGapSeries b a (fun _ => α) ρ − liftGapSeries a b (fun _ => α) ρ
     = circleGapSeries a b ρ`

valid for every `(a, b : ℕ → ℂ)`, every real `α` with `α² < 1`, every
`ρ ≥ 0`, and per-mode summability hypotheses surfaced as theorem
arguments. Sprint 068 shipped THETA_STEP (the first such file); sprint
069 shipped LIFT_IDENTITY (the second); sprint 070 ships
LIFT_SERIES_BRIDGE (the third), in a structurally distinct register
(`tsum`-level rearrangement that bridges the per-`k` algebraic content
of sprint 069 to the workspace's series-level circle-gap object).

The identity is paper-axiom-free: its closure draws only on
`Candidates.V54.LiftIdentity.lift_identity_per_k` (sprint 069's
Mathlib-only identity), `Mathlib.Topology.Algebra.InfiniteSum.*`, and
the `def`-level unfolding of `liftGapSeries` / `circleGapSeries` from
`KorenblumPaper.PaperAxioms`. No `Section2Assumptions` field, no oracle,
no new axioms.

### Sign / orientation note

The sprint contract proposed
`liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ`,
but the per-`k` calculation gives the opposite sign: by V54's lift
identity, `‖b k − α·a k‖² − ‖a k − α·b k‖² = (1 − α²) · (‖b k‖² −
‖a k‖²)`, so the `(a, b)`-orientation difference equals
`−circleGapSeries a b ρ`. We therefore ship the sign-correct swap
`liftGapSeries b a … − liftGapSeries a b …`. The compositional /
structural value for downstream consumers is identical; the next planner
can re-orient any consumer that prefers the contract's original swap.

The side lemma `v55_lift_series_bridge_compiles_at_seed_witness` below
forces the elaborator to verify that LIFT_SERIES_BRIDGE compiles
against arbitrary `(a, b, α, ρ)` and the four summability hypotheses —
confirming the new theorem is non-vacuous and reusable by future
candidates that need series-level circle-gap content.

c-pushing is deferred per the bulletin's three-sprint exhaustion
synthesis; this sprint's purpose is to put a third reusable Lean
building block in place that future c-pushing sprints can compose with
the brief's two remaining named candidates (per-`k` cross-coupling
positivity, Wang Lemma 2's boundary `L²` expansion) to derive a per-`k`
strict drop bound the way Wang's published proof does.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
V54-shaped oracle bound-field. Identical declaration to V54's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V54's `hEq15_oracle_certified_hp_35645`, with the
exact same `Eq15ScalarBound K c_value` shape at `c_value = 35645/100000 =
0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

Wrapper acceptance pre-verified by sprint 058's HP probe and re-checked by
sprint 059's sanity replay; certified `total_mass_lower = 1.000013457935`,
margin `+1.35e-05` above the strict-margin threshold. V55's trust envelope
is byte-for-byte identical to V54's; the structural novelty of V55 is
upstream (the new derived-theorem file
`Candidates/V55/LiftSeriesBridge.lean`), not in the discharge route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 070 / Phase A non-vacuity check: invoke `liftSeriesBridge_main`
against arbitrary `(a, b : ℕ → ℂ)`, `α ρ : ℝ`, the four summability
hypotheses, and `α² < 1`, `ρ ≥ 0`, to force the elaborator to confirm
LIFT_SERIES_BRIDGE compiles and that the identity is well-typed as a
statement about `liftGapSeries` and `circleGapSeries`.

This is a **statement-level** check, not a witness-construction: the lemma
re-states the LiftSeriesBridge headline theorem in the V55 namespace and
discharges it by directly invoking
`LiftSeriesBridge.liftSeriesBridge_main`. The elaborator's acceptance of
this lemma confirms that `Candidates/V55/LiftSeriesBridge.lean` is
non-vacuous and that the workspace's existing trusted surface is
structurally compatible with LIFT_SERIES_BRIDGE.

Note the orientation: per the sign-correct calculation (see the
LiftSeriesBridge docstring for full discussion), the headline identity
is `liftGapSeries b a … − liftGapSeries a b … = circleGapSeries a b ρ`,
not the contract's original orientation `a b … − b a …` (which would
equal `−circleGapSeries a b ρ`).
-/
theorem v55_lift_series_bridge_compiles_at_seed_witness
    (a b : ℕ → ℂ) (α ρ : ℝ)
    (hα_sq_lt_one : α ^ 2 < 1)
    (hρ_nonneg : 0 ≤ ρ)
    (hS1 : Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)))
    (hS2 : Summable (fun k : ℕ => ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)))
    (hS3 : Summable (fun k : ℕ => ‖a k‖ ^ 2 * ρ ^ (2 * k)))
    (hS4 : Summable (fun k : ℕ => ‖b k‖ ^ 2 * ρ ^ (2 * k))) :
    PaperAxioms.liftGapSeries b a (fun _ => α) ρ
      - PaperAxioms.liftGapSeries a b (fun _ => α) ρ
        = PaperAxioms.circleGapSeries a b ρ :=
  LiftSeriesBridge.liftSeriesBridge_main
    a b α ρ hα_sq_lt_one hρ_nonneg hS1 hS2 hS3 hS4

/--
Paper-faithful candidate: the V54-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-070 advance is
the new building block in `Candidates/V55/LiftSeriesBridge.lean`,
exercised by `v55_lift_series_bridge_compiles_at_seed_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V55
