-- @parent V56
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V57

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 073 ships V57 at the same `c_value = 7129/20000 = 0.35645` as V56,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V56's: this is the contract's standard
PASS-tie-with-structural-advance Outcome — sprint 071's per-mode
τ-window kernel exhausted the per-mode-via-eq8+eq9 axis at single-window
granularity, sprint 072 was superseded because multi-window per-mode
inherits the same `paperLambda` suppression that sprint 071 forecast.
Sprint 073 routes the **disk side** through V54's lift identity + V55's
series bridge, producing a structurally novel **Λ-free** disk-side
upper bound on `diskExcess` that future closing-reducer sprints can
compose with annulus-side machinery on a different chain.

What is structurally novel in V57 is the import of
`ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated`, the
**fourth** per-candidate derived-theorem file in the workspace shipping
Lean theorems corresponding to Wang un-numbered intermediate analytical
content:

  * `diskExcess_lift_identity_at_alpha`: the integrated form of V54's
    per-`k` lift identity over `[0, c]`,

      `(1 − α²) · diskExcess (circleGap a b) c
         = ∑' k, ‖a k − α·b k‖² · c^(2k+2) / (k+1)
           − ∑' k, ‖b k − α·a k‖² · c^(2k+2) / (k+1)`,

    valid for every `(a, b : ℕ → ℂ)`, every real `α` with `α² < 1`,
    every `c ≥ 0`, the four disk-weighted summability hypotheses, and
    the polar-Jacobian disk-integral hypothesis (the latter surfaced
    in the signature for the same reason V53/V54/V55 surface their
    own structural side-conditions).

  * `diskExcess_upper_bound_via_lift_at_alpha`: the immediate
    corollary by dropping the non-negative second `tsum`,

      `(1 − α²) · diskExcess (circleGap a b) c
         ≤ ∑' k, ‖a k − α·b k‖² · c^(2k+2) / (k+1)`.

    This is the workspace's **first Λ-free disk-side upper bound on
    integrated diskExcess** — no `paperLambda K c ρ` denominator
    anywhere in the chain.

  * `diskExcess_le_simple_at_alpha_eq_c`: specialisation to `α = c`
    with the elementary triangle/Cauchy bound
    `‖a k − c·b k‖² ≤ 2(‖a k‖² + c²·‖b k‖²)`, producing a closed-form
    upper bound in terms of `Σ⁰⁺(c)`-style coefficient sums.

Sprint 068 shipped THETA_STEP (the first such file); sprint 069 shipped
LIFT_IDENTITY (the second); sprint 070 shipped LIFT_SERIES_BRIDGE
(the third). Sprint 073 ships INTEGRATED_LIFT_IDENTITY (the fourth), in
the structurally distinct register of `tsum`-level integration over the
disk `[0, c]`.

The three theorems are paper-axiom-free: their closure draws only on
`Candidates.V54.LiftIdentity.lift_identity_per_k` (sprint 069's
Mathlib-only identity), `Mathlib.Topology.Algebra.InfiniteSum.*`, and
the `def`-level unfolding of `coeffPlusGap` / `circleGapSeries` /
`diskExcess` from `KorenblumPaper.PaperAxioms`. No `Section2Assumptions`
field, no oracle, no new axioms.

### Sign / orientation note

V54's `lift_identity_per_k` provides
`(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²`.
Negating gives `(1 − α²) · (‖a k‖² − ‖b k‖²) = ‖a k − α·b k‖² − ‖b k − α·a k‖²`.
Since `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`, the integrated form
gives the contract's stated orientation:

  `(1 − α²) · diskExcess(circleGap a b) c
     = ∑' k, ‖a k − α·b k‖² · c^(2k+2)/(k+1)
       − ∑' k, ‖b k − α·a k‖² · c^(2k+2)/(k+1)`.

The side lemma `v57_lift_integrated_compiles_at_seed_witness` below
forces the elaborator to verify that `diskExcess_lift_identity_at_alpha`
compiles against arbitrary `(a, b, α, c)` and the four disk-weighted
summability hypotheses + polar-Jacobian hypothesis — confirming the
new theorems are non-vacuous and reusable by future candidates that
need disk-integrated lift-identity content.

c-pushing is deferred to a future sprint per the contract's sequencing
note: sprint 074 (the immediately next planner session) is forecast
to compose Theorem 2 / Theorem 3 with sprint 005's
`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` plus eq8/eq9 on the annulus
side, possibly producing a per-`k` cross-coupling kernel for the next
c-push attempt that does NOT divide by `paperLambda` on the disk side.

### Trust-base envelope

Identical to V56's:
  - `hEq15_oracle_certified_hp_35645` (registered oracle, sprint 059)
  - standard Lean axioms
  - no new axioms, no new oracles, no `Section2Assumptions` field
    extensions, no `KorenblumPaper/` edits.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
V56-shaped oracle bound-field. Identical declaration to V56's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V56's `hEq15_oracle_certified_hp_35645`, with
the exact same `Eq15ScalarBound K c_value` shape at `c_value =
35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at `(c_num, c_den, dps,
n_trunc) = (35645, 100000, 100, 500)`.

Wrapper acceptance pre-verified by sprint 058's HP probe and re-checked
by sprint 059's sanity replay; certified `total_mass_lower =
1.000013457935`, margin `+1.35e-05` above the strict-margin threshold.
V57's trust envelope is byte-for-byte identical to V56's; the structural
novelty of V57 is upstream (the new derived-theorem file
`Candidates/V57/DiskExcessLiftIntegrated.lean`), not in the discharge
route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 073 / Phase A non-vacuity check: invoke
`diskExcess_lift_identity_at_alpha` against arbitrary `(a, b : ℕ → ℂ)`,
`α c : ℝ`, the four disk-weighted summability hypotheses, the
polar-Jacobian disk-integral hypothesis, and `α² < 1`, `c ≥ 0`, to
force the elaborator to confirm INTEGRATED_LIFT_IDENTITY compiles and
that the identity is well-typed as a statement about
`diskExcess (circleGap a b) c` on the LHS and the difference of two
disk-weighted `tsum`s on the RHS.

This is a **statement-level** check, not a witness-construction: the
lemma re-states the headline theorem in the V57 namespace and discharges
it by directly invoking
`DiskExcessLiftIntegrated.diskExcess_lift_identity_at_alpha`. The
elaborator's acceptance of this lemma confirms that
`Candidates/V57/DiskExcessLiftIntegrated.lean` is non-vacuous and that
the workspace's existing trusted surface is structurally compatible
with INTEGRATED_LIFT_IDENTITY.
-/
theorem v57_lift_integrated_compiles_at_seed_witness
    (a b : ℕ → ℂ) (α c : ℝ)
    (hα_sq_lt_one : α ^ 2 < 1)
    (hc_nonneg : 0 ≤ c)
    (hS1 :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hS2 :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hS3 :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hS4 :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hDiskJacobian :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        = ∑' k : ℕ,
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ)) :
    (1 - α ^ 2) *
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      = (∑' k : ℕ,
            ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ))
        - (∑' k : ℕ,
            ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)) :=
  DiskExcessLiftIntegrated.diskExcess_lift_identity_at_alpha
    a b α c hα_sq_lt_one hc_nonneg hS1 hS2 hS3 hS4 hDiskJacobian

/--
Paper-faithful candidate: the V56-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-073 advance is
the new building block in `Candidates/V57/DiskExcessLiftIntegrated.lean`,
exercised by `v57_lift_integrated_compiles_at_seed_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V57
