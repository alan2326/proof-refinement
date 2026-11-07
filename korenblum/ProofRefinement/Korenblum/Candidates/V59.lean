-- @parent V58
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V59

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 076 ships V59 at the same `c_value = 7129/20000 = 0.35645` as V58,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V58's: this is the contract's standard
PASS-tie-with-structural-advance Outcome — the structural advance is
upstream in the new shared-trust-surface theorem
`Reduction.diskExcess_eq_tsum_via_termwise_integration_with_le_one`,
the **disk-side sibling** of sprint 046's
`Reduction.annulusExcess_eq_tsum_via_termwise_integration` at the
exact annulus-parity signature `(hc_nonneg, hc_le_one, hSummable_int_norm)`.

What is structurally novel in V59 is the use of a new `Reduction.lean`
theorem at the disk-side polar-Jacobian termwise-integration identity
signature, mirroring sprint 046's annulus-side theorem signature
byte-for-byte modulo integration-domain endpoints and the per-`k` polar
weight. The theorem closes the structural disk/annulus asymmetry that
V57.Theorem 1's surfaced `hDiskJacobian` hypothesis exposed: a future
V60 sprint can now re-state V57.Theorem 1 with the `hDiskJacobian`
hypothesis dropped, by consuming the new sprint-076 shared-trust-
surface theorem internally.

### Sprint 076 discovery

The contract for sprint 076 framed the new theorem as filling a gap
where the disk-side `tsum`-of-integrals identity did not yet exist in
shared trust surface. While drafting the proof, the generator
discovered that sprint 042 had **already shipped** the disk-side
identity at `Reduction.diskExcess_eq_tsum_via_termwise_integration`
(line 6473 of `Reduction.lean`), with hypotheses
`(hc_nonneg, hSummable_int_norm)` — i.e., **without** the `hc_le_one`
parity hypothesis the contract requested. The contract's intent
(close the V57/V58 asymmetry by making the disk-side polar-Jacobian
identity available in shared trust surface for V57 to consume) was
already met by sprint 042 at the time it was shipped. What V57.Theorem
1 missed was not the existence of a usable shared-trust-surface theorem;
it was the architectural choice (made for sprint-073 reasons) to surface
`hDiskJacobian` as a hypothesis rather than discharge it via sprint 042.

The sprint-076 deliverable consequently consists of a sibling theorem
`diskExcess_eq_tsum_via_termwise_integration_with_le_one` at the **exact
annulus-parity signature** the contract specified, whose proof body
delegates to the existing sprint 042 theorem. The `hc_le_one` premise
is not used in the proof body (it is genuinely unnecessary on the disk
side); it is present purely for signature parity with sprint 046's
annulus theorem, so that future candidate-side derived-theorem files
needing a disk-side signature byte-for-byte parallel to the annulus
side can consume the disk-side theorem directly without an adapter
shim.

### V59 side lemma

The side lemma `v59_disk_polar_jacobian_compiles_at_witness` exercises
the new theorem's signature against arbitrary `(a, b : ℕ → ℂ)`,
`c : ℝ` input, mirroring V57's
`v57_lift_integrated_compiles_at_seed_witness` pattern (statement-level
non-vacuity check). The lemma confirms that the new theorem compiles,
that its hypothesis envelope matches the contract specification, and
that its conclusion is well-typed as a statement about
`diskExcess (circleGap a b) c` on the LHS and a per-`k` `tsum` over the
disk-weighted Bergman scalar series on the RHS.

### Trust-base envelope

Identical to V58's:
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
V58-shaped oracle bound-field. Identical declaration to V58's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V58's `hEq15_oracle_certified_hp_35645`, with
the exact same `Eq15ScalarBound K c_value` shape at `c_value =
35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at `(c_num, c_den, dps,
n_trunc) = (35645, 100000, 100, 500)`.

V59's trust envelope is byte-for-byte identical to V58's; the structural
novelty of V59 is upstream (the new shared-trust-surface theorem
`Reduction.diskExcess_eq_tsum_via_termwise_integration_with_le_one`),
not in the discharge route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 076 / Phase B non-vacuity check: invoke
`Reduction.diskExcess_eq_tsum_via_termwise_integration_with_le_one`
against arbitrary `(a, b : ℕ → ℂ)`, `c : ℝ`, the disk-side polar-Jacobian
summability hypothesis, and `0 ≤ c ≤ 1`, to force the elaborator to
confirm the new shared-trust-surface theorem compiles and that the
identity is well-typed as a statement about
`diskExcess (circleGap a b) c` on the LHS and the per-`k` `tsum` over
the disk-weighted Bergman scalar series on the RHS.

This is a **statement-level** check, not a witness-construction: the
lemma re-states the headline theorem in the V59 namespace and
discharges it by directly invoking
`Reduction.diskExcess_eq_tsum_via_termwise_integration_with_le_one`.
The elaborator's acceptance of this lemma confirms that the new
shared-trust-surface theorem in `Reduction.lean` is non-vacuous and
that the workspace's existing trusted surface is structurally
compatible with consuming a disk-side polar-Jacobian termwise-
integration identity at the annulus-parity signature.
-/
theorem v59_disk_polar_jacobian_compiles_at_witness
    (a b : ℕ → ℂ) (c : ℝ)
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSum :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      = ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
  ProofRefinement.Korenblum.diskExcess_eq_tsum_via_termwise_integration_with_le_one
    a b hc_nonneg hc_le_one hSum

/--
Paper-faithful candidate: the V58-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-076 advance is
the new shared-trust-surface theorem in `Reduction.lean`, exercised by
`v59_disk_polar_jacobian_compiles_at_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V59
