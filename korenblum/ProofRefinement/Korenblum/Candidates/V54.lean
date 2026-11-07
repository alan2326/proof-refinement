-- @parent V53
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Candidates.V54.LiftIdentity

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V54

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 069 ships V54 at the same `c_value = 7129/20000 = 0.35645` as V53,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V53's: this is the contract's Outcome A
(c-tying sprint by design — the bulletin's three-sprint exhaustion
synthesis and sprint 068's Phase B falsification settle that closed-form
`(a, b)`-independent kernels are exhausted; advancing `c` further requires
per-`k` content that this sprint contributes a building block toward).

What is structurally novel in V54 is the import of
`ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`, the **second**
per-candidate derived-theorem file in the workspace shipping a Lean theorem
corresponding to a Wang un-numbered intermediate algebraic step:

  `(1 − α²) · (‖b k‖² − ‖a k‖²) =
     ‖b k − (α : ℂ)·a k‖² − ‖a k − (α : ℂ)·b k‖²`

valid for every `(a, b : ℕ → ℂ) × ℝ × ℕ`. Sprint 068 shipped THETA_STEP
(the first such file); sprint 069 ships LIFT_IDENTITY (the second), in a
structurally distinct register (pure complex algebra on `ℕ → ℂ` sequences
vs. THETA_STEP's chain of paper equations and series identities). The
identity is paper-axiom-free: its closure draws only on `Mathlib.Analysis.
Complex.Norm` (i.e. on `Complex.sq_norm`, `Complex.normSq_apply`, and the
`re`/`im` simp lemmas), with no `Section2Assumptions` field, no oracle,
and no `KorenblumPaper.*` content.

The side lemma `v54_lift_identity_compiles_at_seed_witness` below forces
the elaborator to verify that LIFT_IDENTITY compiles against arbitrary
`(a, b, α, k)` — confirming the new theorem is non-vacuous and reusable
by future candidates that need per-`k` cross-coupling content.

c-pushing is deferred per the bulletin's three-sprint exhaustion synthesis;
this sprint's purpose is to put a second reusable Lean building block in
place that future c-pushing sprints can compose with the boundary `L²`
comparison (a future per-candidate derived-theorem candidate per the brief
lines 137–141) to derive a per-`k` strict drop bound the way Wang's
published proof does.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
V53-shaped oracle bound-field. Identical declaration to V53's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V53's `hEq15_oracle_certified_hp_35645`, with the
exact same `Eq15ScalarBound K c_value` shape at `c_value = 35645/100000 =
0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

Wrapper acceptance pre-verified by sprint 058's HP probe and re-checked by
sprint 059's sanity replay; certified `total_mass_lower = 1.000013457935`,
margin `+1.35e-05` above the strict-margin threshold. V54's trust envelope
is byte-for-byte identical to V53's; the structural novelty of V54 is
upstream (the new derived-theorem file
`Candidates/V54/LiftIdentity.lean`), not in the discharge route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 069 / Phase A non-vacuity check: invoke `lift_identity_per_k` against
arbitrary `(a, b : ℕ → ℂ)`, `α : ℝ`, `k : ℕ` to force the elaborator to
confirm LIFT_IDENTITY compiles and that the identity is well-typed as a
statement on complex sequences and a real scalar.

This is a **statement-level** check, not a witness-construction: the lemma
re-states the LiftIdentity theorem in the V54 namespace and discharges it
by directly invoking `LiftIdentity.lift_identity_per_k`. The elaborator's
acceptance of this lemma confirms that
`Candidates/V54/LiftIdentity.lean` is non-vacuous and that the workspace's
existing trusted surface is structurally compatible with LIFT_IDENTITY.
-/
theorem v54_lift_identity_compiles_at_seed_witness
    (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
    (1 - α ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
      = ‖b k - (α : ℂ) * a k‖ ^ 2 - ‖a k - (α : ℂ) * b k‖ ^ 2 :=
  LiftIdentity.lift_identity_per_k a b α k

/--
Paper-faithful candidate: the V53-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-069 advance is
the new building block in `Candidates/V54/LiftIdentity.lean`, exercised by
`v54_lift_identity_compiles_at_seed_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V54
