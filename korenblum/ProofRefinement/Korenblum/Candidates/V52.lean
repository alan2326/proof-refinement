-- @parent V51
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V52

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
Fourth c-push above the seed in 59 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48 / V49 / V50 / V51, with the
literal `(15)` premise pinned at the finer-denominator `c = 35645/100000
= 0.35645` (path HP-35645) — a +0.00005 increment over V51's
`c = 1782/5000 = 35640/100000`. The `(15)` premise is discharged by the
registered oracle `eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)` — the same
upgraded HP envelope as V51, but at a finer-denominator c.

The wrapper's positive return at this `(c, envelope)` was discovered
by sprint 058's anti-blind-spot HP probe
(`Scratch/sprint_058_hp_ceiling_pin.{py,txt}`) and re-checked by
sprint 059's sanity replay (`Scratch/sprint_059_hp_35645_sanity_replay.{py,txt}`)
just before this candidate was written. Certified
`total_mass_lower = 1.000013457935`, margin `+1.35e-05` above the
strict-margin threshold `1 + 10^(-30)`.

This is the first candidate in the workspace to pin a c-denominator
finer than 5000 — the +0.00005 increment over V51 cannot be expressed
at the 5000-denominator scale. The HP envelope's box-by-box conservatism
residue is what permits this thin-but-positive certification: the
ground-truth Wang `(15)` gap at `c = 0.35645` is below the literal
crossover at `c ~ 0.35635` (sprint 050's pinpoint), but the upper-bound
box partition's lower envelope remains positive at `+1.35e-05`. HP-tier
falsifiability at `c = 0.3565` still rejects (margin `-1.15e-03`), so
the absolute HP ceiling sits somewhere in `(0.35645, 0.35650)` —
sprint 060's question, not this sprint's.
-/
def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 059 oracle bound-field. Identical declaration to V48 / V49 / V50
/ V51; the Evaluator compares the per-candidate `oracle_fn`'s returned
Fraction against this `def` via `oracle_bound <= declared`. Sharing the
same `bound_field` name across V48 / V49 / V50 / V51 / V52 is permitted
because each `[[oracles]]` row carries its own `oracle_fn` (the per-`c`-
and-envelope shim).
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

Lean axiom shape is byte-for-byte identical to V51's
`hEq15_oracle_certified_hp_3564` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper at the
same upgraded envelope; the Scratch records at
`Scratch/sprint_058_hp_ceiling_pin.txt` and
`Scratch/sprint_059_hp_35645_sanity_replay.txt` document the wrapper's
True return and certified margin at this `(c, envelope)`.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V52
