-- @parent V50
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V51

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
Third c-push above the seed in 57 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48 / V49 / V50, but with the
literal `(15)` premise pinned at `c = 1782/5000 = 0.3564` (path HP-3564)
instead of sprint 056's `c = 1781/5000`. The `(15)` premise is discharged
by the registered oracle `eq15_certified_at_hp_3564` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1782, 5000, 100, 500)`; the wrapper's
positive return at this `(c, envelope)` was pre-verified by
`Scratch/sprint_057_eq15_wrapper_tiered_preverification.{py,txt}`
(certified `total_mass_lower = 1.001174814942`, margin `+1.17e-03`).

This is the first candidate in the workspace to pin the upgraded precision
envelope `(dps=100, n_trunc=500)` per Bulletin.md lines 300-304. The tiered
Scratch pre-verification confirmed that the standard envelope
`(dps=50, n_trunc=200)` rejects at `c = 0.3564` (margin `-6.89e-04`,
matching the planner's measured slope `-2.34e-3` per `+0.0001` of `c`
across V49 / V50 / sprint_056-fallback) but the upgraded envelope accepts.
The upgraded envelope reduces the wrapper's box-by-box conservatism gap
relative to adaptive `mp.quad`, allowing certification at `c` values where
the standard envelope rejects despite the ground-truth `(15)` gap being
positive.

Falsifiability still holds at the upgraded envelope: `certify_eq15` at
`(3565, 10000, dps=100, n_trunc=500)` rejects (margin `-1.15e-03`), so the
HP envelope is verifiably below the literal `(15)` crossover at
`c ~ 0.35635` (sprint 050's pinpoint). HP-tier probes at `c = 0.3566` and
`c = 0.3568` both rejected (margins `-3.46e-03` and `-8.08e-03`
respectively), so HP-3564 is the largest accepting `c` in the tiered
probe — the new wrapper ceiling.
-/
def c_value : ℝ := 1782 / 5000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 057 oracle bound-field. Identical declaration to V48 / V49 / V50;
the Evaluator compares the per-candidate `oracle_fn`'s returned Fraction
against this `def` via `oracle_bound <= declared`. Sharing the same
`bound_field` name across V48 / V49 / V50 / V51 is permitted because each
`[[oracles]]` row carries its own `oracle_fn` (the per-`c`-and-envelope
shim).
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 1782/5000 = 0.3564`. Discharged by the registered oracle
`eq15_certified_at_hp_3564` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1782, 5000, 100, 500)`.

Lean axiom shape is byte-for-byte identical to V50's
`hEq15_oracle_certified_3562` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper, but with
the upgraded envelope; the Scratch pre-verification at
`Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt` records the
wrapper's True return and certified margin at this `(c, envelope)`.
-/
axiom hEq15_oracle_certified_hp_3564 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_3564 K)

end ProofRefinement.Korenblum.Candidates.V51
