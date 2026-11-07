-- @parent V59
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V60

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 077 ships V60 at the same `c_value = 7129/20000 = 0.35645` as V59,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V59's: this is the contract's standard
PASS-tie-with-Phase-0-witness Outcome — the structural advance is
upstream in the new per-candidate derived-theorem file
`Candidates.V60.PerKAlphaVaryingLiftIdentity`, which freezes the
per-`k` α-varying signature into the workspace's import graph.

What is structurally novel in V60 is the introduction of the workspace's
**first** per-candidate derived-theorem file whose signature ranges over
`α : ℕ → ℝ` (per-mode α(·)) rather than `α : ℝ` (uniform α). The new
theorem `lift_identity_per_k_alpha_varying` is a one-line wrapper of
V54's `lift_identity_per_k`, applied at α := α(k) for each `k`
independently. The algebraic content is V54's; sprint 077's contribution
is the signature-level handle for sprint 078.

### Sprint 077 Phase 0 outcome

The numerical sweep
(`Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.py`) returned GO:
the per-`k` α-varying kernel
  `∑'_k (1 − α(k)²) · coeffPlusGap_k · (1 − 2c^(2k+2)) / (k+1)`
is non-negative on every canonical extremal `E_j` (`j = 1..5`) and on
every linear combination probed at
  `c = 0.3565`, `α(0) = 0.1`, `α(k) = 1.01` for `k ∈ {1..19}`,
with worst margin `+2.0e-2` (≥ 1e-4) on E5.

**Structural caveat (faithfully recorded in `_witness.txt`)**: the
witness's α-vector exits V54's `lift_identity_per_k_rearranged`
contraction regime (`max_k |α(k)| = 1.01 > 1`). The Phase 0 sweep
detected NO contraction-regime witness (`|α(k)| < 1` for all k)
above c = 0.35645 in the structured-α-family grid. The sign-positivity
at `α(k)² > 1` is a *trivially scalable* sign flip: `(1 − α(k)²) < 0`
multiplied by the negative `coeffPlusGap_k` on E_k yields a positive
per-mode contribution that scales with α(k)². Whether this lifts to a
genuine `annulusExcess(c) ≥ diskExcess(c)` inequality is sprint 078's
problem, and the answer is NOT automatic.

### V60 side lemma

The side lemma `v60_per_k_alpha_varying_compiles_at_witness` exercises
`lift_identity_per_k_alpha_varying`'s signature against arbitrary
`(a, b : ℕ → ℂ)`, `α : ℕ → ℝ`, `k : ℕ` input (statement-level
non-vacuity check). The lemma confirms that the new theorem compiles,
that its hypothesis envelope matches the contract specification, and
that its conclusion is well-typed as a per-`k` α-varying instantiation
of V54's lift identity.

### Trust-base envelope

Identical to V59's:
  - `hEq15_oracle_certified_hp_35645` (registered oracle, sprint 059)
  - standard Lean axioms
  - no new axioms, no new oracles, no `Section2Assumptions` field
    extensions, no `KorenblumPaper/` edits, no `Reduction.lean` edits.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
V58/V59-shaped oracle bound-field. Identical declaration to V59's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V59's `hEq15_oracle_certified_hp_35645`, with
the exact same `Eq15ScalarBound K c_value` shape at `c_value =
35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at `(c_num, c_den, dps,
n_trunc) = (35645, 100000, 100, 500)`.

V60's trust envelope is byte-for-byte identical to V59's; the structural
novelty of V60 is upstream (the new per-candidate derived-theorem file
`Candidates.V60.PerKAlphaVaryingLiftIdentity`), not in the discharge
route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 077 / Phase B non-vacuity check: invoke
`Candidates.V60.PerKAlphaVaryingLiftIdentity.lift_identity_per_k_alpha_varying`
against arbitrary `(a, b : ℕ → ℂ)`, `α : ℕ → ℝ`, `k : ℕ` input, to force
the elaborator to confirm the new α-varying signature compiles and that
the identity is well-typed as a per-`k` instantiation of V54's lift
identity at α := α(k).

This is a **statement-level** check, not a witness-construction: the
lemma re-states the theorem in the V60 namespace and discharges it by
directly invoking the per-candidate derived-theorem file. The
elaborator's acceptance of this lemma confirms that the new α-varying
signature is non-vacuous and that the workspace's existing trusted
surface is structurally compatible with consuming a per-`k` α-varying
lift identity at the per-mode-α(·) signature.
-/
theorem v60_per_k_alpha_varying_compiles_at_witness
    (a b : ℕ → ℂ) (α : ℕ → ℝ) (k : ℕ) :
    (1 - (α k) ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
      = ‖b k - ((α k) : ℂ) * a k‖ ^ 2
          - ‖a k - ((α k) : ℂ) * b k‖ ^ 2 := by
  open ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity in
  exact lift_identity_per_k_alpha_varying a b α k

/--
Paper-faithful candidate: the V59-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-077 advance is
the new per-candidate derived-theorem file
`Candidates.V60.PerKAlphaVaryingLiftIdentity`, exercised by
`v60_per_k_alpha_varying_compiles_at_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V60
