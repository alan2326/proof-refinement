-- @parent V49
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V50

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
Second c-push above the seed in 56 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48 / V49, but with the literal
`(15)` premise pinned at `c = 1781/5000 = 0.3562` (= one
integer-10000ths past sprint 055's c = 0.3560, the next safe step in
the bulletin's directive lines 271–280) instead of sprint 055's
`c = 1780/5000`. The `(15)` premise is discharged by the registered
oracle `eq15_certified_at_3562` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1781, 5000, 50, 200)`; the wrapper's
positive return at this c was pre-verified by
`Scratch/sprint_056_eq15_wrapper_pre_verification.{py,txt}` (certified
total_mass_lower 1.003960506, margin +3.96e-03; a step sprint 055 did
not need because sprint 050's mpmath table already covered c = 0.3560
directly; sprint 056 needs it because c = 0.3562 is not in sprint
050's enumeration).
-/
def c_value : ℝ := 1781 / 5000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 056 oracle bound-field. Identical declaration to V48 / V49; the
Evaluator compares the per-candidate `oracle_fn`'s returned Fraction
against this `def` via `oracle_bound <= declared`. Sharing the same
`bound_field` name across V48 / V49 / V50 is permitted because each
`[[oracles]]` row carries its own `oracle_fn` (the per-`c` shim).
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 1781/5000 = 0.3562`. Discharged by the registered oracle
`eq15_certified_at_3562` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1781, 5000, 50, 200)`.

Lean axiom shape is byte-for-byte identical to V49's
`hEq15_oracle_certified_3560` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper, plus
the Scratch pre-verification recorded at
`Scratch/sprint_056_eq15_wrapper_pre_verification.txt`.
-/
axiom hEq15_oracle_certified_3562 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3562 K)

end ProofRefinement.Korenblum.Candidates.V50
