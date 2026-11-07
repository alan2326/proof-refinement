-- @parent V48
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V49

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
First c-push above the seed in 55 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48, but with the literal
`(15)` premise pinned at `c = 1780/5000 = 0.3560` (= the largest
integer-10000ths `c` with sprint-050-verified positive margin in
the mpmath `dps=50, N_TRUNC=200` envelope) instead of the seed
`c = 3554/10000`. The `(15)` premise is discharged by the registered
oracle `eq15_certified_at_3560` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)`; per sprint
050's pinpoint, the wrapper certifies `total ≥ 1 + 10^(-30)` at this
`c` (mpmath gap +1.131e-02, conservatism ~0.003).
-/
def c_value : ℝ := 1780 / 5000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 055 oracle bound-field. Identical declaration to V48; the
Evaluator compares the per-candidate `oracle_fn`'s returned Fraction
against this `def` via `oracle_bound <= declared`. Sharing the same
`bound_field` name across V48 / V49 / future V50+ is permitted because
each `[[oracles]]` row carries its own `oracle_fn` (the per-`c` shim);
the `bound_field` is just the candidate-side declaration of the RHS
threshold of Wang's `1 ≤ scalarCriterion c (paperLambda K c)`.
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 1780/5000 = 0.3560`. Discharged by the registered oracle
`eq15_certified_at_3560` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)`.

Lean axiom shape is byte-for-byte identical to V48's
`hEq15_oracle_certified_3554` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper invoked
by the Evaluator on every candidate run; the wrapper is parametric in
`(c_num, c_den)` so the c-push cascade reuses the existing oracle
infrastructure with one shim-add per sprint.
-/
axiom hEq15_oracle_certified_3560 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3560 K)

end ProofRefinement.Korenblum.Candidates.V49
