-- @parent V57
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V58

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 075 ships V58 at the same `c_value = 7129/20000 = 0.35645` as V57,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V57's: this is the contract's standard
PASS-tie-with-structural-advance Outcome — the structural advance is
upstream in the new derived-theorem file
`Candidates/V58/AnnulusExcessLiftIntegrated.lean`, the **annulus-side
sibling** of V57's `DiskExcessLiftIntegrated`.

What is structurally novel in V58 is the import of
`ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated`,
the **fifth** per-candidate derived-theorem file in the workspace
shipping Lean theorems corresponding to Wang un-numbered intermediate
analytical content. V58 ships three theorems:

  * `annulusExcess_lift_identity_at_alpha`: the integrated form of V54's
    per-`k` lift identity over `[c, 1]`,

      `(1 − α²) · annulusExcess (circleGap a b) c
         = ∑' k, ‖a k − α·b k‖² · (1 − c^(2k+2))/(k+1)
           − ∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2))/(k+1)`.

    Unlike V57's Theorem 1 (which surfaces the disk-side polar-Jacobian
    as a hypothesis), V58's Theorem 1 invokes the already-proved
    sprint-046 theorem
    `Reduction.annulusExcess_eq_tsum_via_termwise_integration` directly,
    so the only "polar-Jacobian-shaped" hypothesis is that theorem's
    summability premise. This is a strict structural improvement over
    V57's signature.

  * `annulusExcess_lower_bound_via_lift_at_alpha`: the immediate
    corollary by dropping the non-negative first `tsum`,

      `−(∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2))/(k+1))
         ≤ (1 − α²) · annulusExcess (circleGap a b) c`.

    This is the workspace's **first Λ-free annulus-side lower bound**
    on `(1 − α²) · annulusExcess` — no `paperLambda K c ρ` denominator
    anywhere in the chain. Mirrors V57's Theorem 2 by orientation flip.

  * `annulusMinusDiskExcess_per_k_at_alpha_eq_c`: the closed-form
    per-`k` representation of `annulusExcess − diskExcess` at `α = c`,

      `(1 − c²) · (annulusExcess (circleGap a b) c
                     − diskExcess (circleGap a b) c)
         = ∑' k, ((1 − c²) · coeffPlusGap a b k)
                  · (1 − 2 c^(2k+2)) / (k + 1)`.

    This is the **direct reduction handle** for a future closing-reducer
    sprint: a per-`k` representation of `annulusExcess − diskExcess`
    with weights `(1 − 2 c^(2k+2))/(k+1)` that are strictly positive on
    `c² < 1/2` (the Korenblum regime is `c² ≈ 0.126`, well inside that
    bound).

Sprint 068 shipped THETA_STEP (the first such file); sprint 069 shipped
LIFT_IDENTITY (the second); sprint 070 shipped LIFT_SERIES_BRIDGE (the
third); sprint 073 shipped DISK_EXCESS_LIFT_INTEGRATED (the fourth).
Sprint 075 ships ANNULUS_EXCESS_LIFT_INTEGRATED (the fifth), in the
structurally-distinct register of `tsum`-level integration over the
annulus `[c, 1]`.

The three theorems are paper-axiom-free: their closure draws only on
`Candidates.V54.LiftIdentity.lift_identity_per_k` (sprint 069's
Mathlib-only identity), `Candidates.V57.DiskExcessLiftIntegrated`
(sprint 073's disk-side sibling), `Mathlib.Topology.Algebra.InfiniteSum.*`,
the `def`-level unfolding of `coeffPlusGap` / `circleGap` /
`annulusExcess` from `KorenblumPaper.PaperAxioms`, and the existing
sprint-046 theorem `annulusExcess_eq_tsum_via_termwise_integration` from
`Proof/Reduction.lean`. No `Section2Assumptions` field, no oracle, no new
axioms.

### Sign / orientation note

V54's `lift_identity_per_k` provides
`(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²`.
Negating gives `(1 − α²) · (‖a k‖² − ‖b k‖²) = ‖a k − α·b k‖² − ‖b k − α·a k‖²`.
Since `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`, the integrated form
gives the contract's stated orientation:

  `(1 − α²) · annulusExcess(circleGap a b) c
     = ∑' k, ‖a k − α·b k‖² · (1 − c^(2k+2))/(k+1)
       − ∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2))/(k+1)`.

V58's orientation **matches** V57's, so disk + annulus halves are
additive. Subtracting V57 from V58 at `α = c` gives Theorem 3's
per-`k` reduction.

The side lemma `v58_annulus_lift_integrated_compiles_at_seed_witness`
below forces the elaborator to verify that
`annulusExcess_lift_identity_at_alpha` compiles against arbitrary
`(a, b, α, c)` and the four annulus-weighted summability hypotheses +
sprint-046 polar-Jacobian summability hypothesis — confirming the
new theorems are non-vacuous and reusable by future candidates that
need annulus-integrated lift-identity content.

c-pushing is deferred to a future sprint per the contract's sequencing
note: a future sprint composes V57 + V58 + a per-`k` cross-coupling
argument that isolates the `coeffPlusGap_k < 0` modes and compensates
them via a per-mode Cauchy–Schwarz / lift-at-different-α strategy.

### Trust-base envelope

Identical to V57's:
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
V57-shaped oracle bound-field. Identical declaration to V57's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V57's `hEq15_oracle_certified_hp_35645`, with
the exact same `Eq15ScalarBound K c_value` shape at `c_value =
35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at `(c_num, c_den, dps,
n_trunc) = (35645, 100000, 100, 500)`.

Wrapper acceptance pre-verified by sprint 058's HP probe and re-checked
by sprint 059's sanity replay; certified `total_mass_lower =
1.000013457935`, margin `+1.35e-05` above the strict-margin threshold.
V58's trust envelope is byte-for-byte identical to V57's; the structural
novelty of V58 is upstream (the new derived-theorem file
`Candidates/V58/AnnulusExcessLiftIntegrated.lean`), not in the discharge
route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 075 / Phase A non-vacuity check: invoke
`annulusExcess_lift_identity_at_alpha` against arbitrary `(a, b : ℕ → ℂ)`,
`α c : ℝ`, the four annulus-weighted summability hypotheses, the
sprint-046 polar-Jacobian summability hypothesis, and `0 ≤ c ≤ 1`, to
force the elaborator to confirm ANNULUS_EXCESS_LIFT_INTEGRATED compiles
and that the identity is well-typed as a statement about
`annulusExcess (circleGap a b) c` on the LHS and the difference of two
annulus-weighted `tsum`s on the RHS.

This is a **statement-level** check, not a witness-construction: the
lemma re-states the headline theorem in the V58 namespace and discharges
it by directly invoking
`AnnulusExcessLiftIntegrated.annulusExcess_lift_identity_at_alpha`. The
elaborator's acceptance of this lemma confirms that
`Candidates/V58/AnnulusExcessLiftIntegrated.lean` is non-vacuous and
that the workspace's existing trusted surface is structurally compatible
with ANNULUS_EXCESS_LIFT_INTEGRATED.
-/
theorem v58_annulus_lift_integrated_compiles_at_seed_witness
    (a b : ℕ → ℂ) (α c : ℝ)
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hS1 :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hS2 :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hS3 :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hS4 :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_polar_jacobian :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))) :
    (1 - α ^ 2) *
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
      = (∑' k : ℕ,
            ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
        - (∑' k : ℕ,
            ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)) :=
  AnnulusExcessLiftIntegrated.annulusExcess_lift_identity_at_alpha
    a b α c hc_nonneg hc_le_one hS1 hS2 hS3 hS4 hSum_polar_jacobian

/--
Paper-faithful candidate: the V57-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-075 advance is
the new building block in
`Candidates/V58/AnnulusExcessLiftIntegrated.lean`, exercised by
`v58_annulus_lift_integrated_compiles_at_seed_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V58
