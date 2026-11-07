-- @parent V47
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V48

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/-- Wang 2025's published lower-bound radius. Unchanged from V0 / V47. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 053 oracle bound-field. The `bound_field` for the registered oracle
`eq15_certified_at_seed`; the Evaluator reads
`Numerical_Library.rigorous_scalar.certify_eq15_at_seed()` (which returns
`Fraction(1)` iff the verified-interval wrapper certifies Wang's `(15)` at
`c = 3554/10000` under the registered envelope `(dps, n_trunc) = (50, 200)`)
and compares it to this declaration via `oracle_bound <= declared`. The
choice `1` is exactly the RHS threshold of Wang's `1 ≤ scalarCriterion c
(paperLambda K c)`: the wrapper certifies the strict bound
`scalarCriterion >= 1 + 10^(-30)` so reporting `1` here is a faithful
under-bound.
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at `c = 0.3554`,
discharged by the registered oracle `eq15_certified_at_seed` whose wrapper
is `Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (3554, 10000, 50, 200)`.

The Lean axiom shape is byte-for-byte identical to V0 / V47's
`hEq15_seed_3554` modulo the name swap; only the trust grounding differs:
V0–V47's `hEq15_seed_3554` is a free-floating per-`c` axiom listed in
`lemma.toml:[seed_axioms].allowed`, whereas
`hEq15_oracle_certified_3554` is registered under
`lemma.toml:[[oracles]]` and the matching Python verifier is invoked by
the Evaluator on every candidate run (see the schema-deviation note in
`Experience.md`).
-/
axiom hEq15_oracle_certified_3554 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
First workspace candidate whose `(15)` premise is routed through the
`[[oracles]]`-registered wrapper instead of the literal seed axiom.
`c_value` ties V0 / V47 at `3554/10000`; this sprint deliberately does
not push `c` (per the bulletin's 2026-05-02 second directive). The
deliverable is the trust-surface change: `axioms_used` switches from
`{seed} ∪ {hEq15_seed_3554}` to `{seed} ∪ {hEq15_oracle_certified_3554}`,
unblocking the per-sprint c-push cascade prescribed by sprints 054+.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3554 K)

end ProofRefinement.Korenblum.Candidates.V48
