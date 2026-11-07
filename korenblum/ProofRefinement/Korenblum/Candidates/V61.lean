-- @parent V60
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V61

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-!
# Sprint 078 / V61 — two-window τ-partition closing reducer + V60-tie candidate

## Structural advance

V61's structural advance is upstream of the candidate: a new closing
reducer `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` in
`Proof/Reduction.lean`, the workspace's **first multi-window per-mode
τ-partition closing reducer**. Sprint 071 shipped the single-window
version `valid_of_perMode_tau_window_eq8_eq9` (m=1); sprint 072 attempted
a general-`m` `Fin m`-indexed version, hit a `hcEqStart0 : c = start 0`
rewrite-motive obstruction, and was rolled back by sprint 074. The new
reducer uses **m=2 with concrete-endpoint plain real parameters**
`(ρStart₁, ρStop₁, ρStart₂, ρStop₂)` plus a single adjacency equality
`hAdj : ρStop₁ = ρStart₂`, sidestepping the `Fin m` motive issue
entirely.

## Phase 0 outcome

The numerical Phase 0 sweep
(`Scratch/sprint_078_two_window_tau_mass_sweep.{py,txt}`) returned **GO**:
the joint two-window mass `mass_2(c) + mass_1(c)` (with windows
`[ρ_2(c), ρ_1(c)]` for j=2 and `[ρ_1(c), 1]` for j=1, where
`ρ_j(c) = c / sqrt(tau(j))` and `tau(j) = j(j+2)/(j+1)²`) crosses 1 at

  - `c = 7129/20000 = 0.35645` (V60 boundary): mass_total = 1.00213, margin = +2.13e-3
  - `c = 0.35646`: mass_total = 1.00190, margin = +1.90e-3   ← strict witness above V60
  - `c = 0.35648`: mass_total = 1.00144, margin = +1.44e-3   (last point above 1e-3 threshold)
  - `c = 0.35654`: mass_total = 1.00004, margin = +4.2e-5    (mass crosses 1 around here)
  - `c = 0.35655`: mass_total = 0.99981, margin = -1.9e-4    (mass falls below 1)

So a strict c-push above V60 is **numerically supported** at any
`c ∈ [0.35646, 0.35648]` with mass margin ≥ 1e-3.

## Phase B GO branch — what would be required, and why this candidate
ties V60 instead

To ship V61 at the witness c (e.g. c=0.35646), the candidate would have
to discharge the reducer's load-bearing premise

  hMassTotal :  1 ≤ ∫_{ρ_2..ρ_1} 2ρ/(H_2·Λ) dρ
                  + ∫_{ρ_1..1} 2ρ/(H_1·Λ) dρ

inside Lean. The integrand involves `WangOuter.paperLambda K c ρ`, the
Wang infinite-product Λ-function — **not a closed-form rational**.
Discharging this premise would require either:

  (a) An interval-arithmetic Lean derivation: bound `Λ(c, ρ)` from above
      by a closed-form rational on each Riemann subinterval, then bound
      `∫ 2ρ/(H·Λ_upper)` from below by closed-form Riemann lower bounds
      that `norm_num` can clear. The Λ-bound itself is an infinite-
      product termwise estimate (Wang's `paper_factor`); each factor
      `> 1`, but the infinite-product bound has no closed-form upper
      witness in Mathlib that the workspace has trusted-surface access
      to.

  (b) A registered `Numerical_Library` oracle: a numerically-certified
      `joint_two_window_mass_lower_bound : ℚ` returned by an mpmath
      wrapper, with a `[[oracles]]` entry in `lemma.toml`.

Route (a) is a substantial Lean undertaking (the Wang Λ-bound is the
load-bearing analytical content of Wang's Section 2 itself); route (b)
is feasible but requires a new oracle row beyond the contract's
preferred `norm_num` route. Per the contract's "Stop conditions"
fallback (line 626-633): if Phase B-GO doesn't fit in the remaining
budget, ship the V60-tie with the structural advance (the new reducer
plus the Phase 0 witness file) preserved.

V61 takes that fallback. The Phase 0 witness at
`Scratch/sprint_078_witness.txt` is a load-bearing input for the next
planner; sprint 079 should pursue either:
  - the oracle route to ship the c-push at the witness c (smallest
    structural step from here), or
  - Sprint C's seven-window envelope at V38's c=356401/1000000, which
    is a structurally tighter envelope where the joint mass is closer
    to 1 with margin ≥ 1e-2 (Bulletin V38 directive).

## V61 trust envelope

Identical to V60's, byte-for-byte:
  - `hEq15_oracle_certified_hp_35645` (registered oracle, sprint 059)
  - standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`,
    `Lean.ofReduceBool`, `Lean.trustCompiler`)
  - no new axioms, no new oracles, no `Section2Assumptions` field
    extensions, no `KorenblumPaper/` edits.

The only non-trust-envelope edit is in `Proof/Reduction.lean`, which
adds the new theorem `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`.
That theorem has no `axiom`s, no `sorry`s, no `admit`s, and no
`Section2Assumptions` field extensions; it is a Lean theorem composing
sprint 071's reducer machinery with `AnnulusIntegralReduction.
annulusSlice_add_adjacent`.

## V61 side lemma

The side lemma `v61_two_window_reducer_compiles_at_witness` exercises
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s signature against
an abstract `h_witness` predicate (statement-level non-vacuity check).
The lemma confirms:
  - the new theorem compiles in V61's import context,
  - its hypothesis envelope matches the contract's m=2 specification
    (four plain real endpoints, adjacency, two j-modes, joint mass),
  - the discharge by direct invocation produces a `ValidKorenblumBound c`
    for any abstract witness predicate satisfying the reducer's
    hypotheses.

The lemma is statement-level: it does not construct a witness for
`hMassTotal` (that is the obstruction described above). It only checks
that the reducer's signature is consumable.
-/

def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/-- V60-shaped oracle bound-field; the Evaluator compares the
per-candidate `oracle_fn`'s returned Fraction against this `def` via
`oracle_bound ≤ declared`. -/
def eq15_lower_bound : ℝ := 1

/-- Same Lean-facing axiom as V60's `hEq15_oracle_certified_hp_35645`,
with the exact same `Eq15ScalarBound K c_value` shape at
`c_value = 35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

V61's trust envelope is byte-for-byte identical to V60's; the
structural novelty of V61 is **upstream** (the new closing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` in
`Proof/Reduction.lean`), not in the candidate's discharge route.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 078 / Phase B non-vacuity check: invoke the new closing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` against an abstract
`h_witness` predicate, to force the elaborator to confirm:
  - the reducer's signature compiles in V61's import context;
  - the m=2 four-endpoint shape is consumable as
    `ValidKorenblumBound c_value` given the `h_witness` predicate;
  - the discharge path is a direct invocation (no `axiom`s, no
    `sorry`s, no `admit`s introduced at the candidate level).

This is a **statement-level** check, not a witness-construction. The
load-bearing `hMassTotal` premise inside `h_witness` is an mpmath-
numerical fact (Phase 0 GO at `c=0.35646` per
`Scratch/sprint_078_witness.txt` shows margin = +1.9e-3 above 1); a
genuine candidate-side discharge of `hMassTotal` requires either an
interval-arithmetic `norm_num` Riemann lower-bound on
`2ρ / (H_j·Λ)` (whose Λ-bound is a substantial Lean derivation) or a
new `Numerical_Library` oracle row. Neither fits in this sprint's
budget; the next planner picks up the c-push at the V61 witness in
sprint 079+ per the V61 docstring's "Phase B GO branch" subsection.

The lemma below confirms that the reducer's signature is consumable.
The non-vacuity check then carries through any Phase 0-GO numerical
witness as a hypothetical: given the witness predicate, the c-push
`ValidKorenblumBound c` is a direct invocation of the reducer.
-/
theorem v61_two_window_reducer_compiles_at_witness
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ) (j₁ j₂ : ℕ),
          c < ρStart₁ ∧ ρStart₁ ≤ ρStop₁ ∧
            ρStop₁ = ρStart₂ ∧
            ρStart₂ ≤ ρStop₂ ∧ ρStop₂ < 1 ∧
            1 ≤ j₁ ∧ 1 ≤ j₂ ∧
            OneModeTail.tau (j₁ - 1) ≤ c ^ 2 / ρStop₁ ^ 2 ∧
            c ^ 2 / ρStart₁ ^ 2 ≤ OneModeTail.tau j₁ ∧
            OneModeTail.tau (j₂ - 1) ≤ c ^ 2 / ρStop₂ ^ 2 ∧
            c ^ 2 / ρStart₂ ^ 2 ≤ OneModeTail.tau j₂ ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                OneModeKernel.weight c n) ∧
            (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
              Summable (fun n : ℕ =>
                OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
            IntervalIntegrable
              (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
              MeasureTheory.volume c 1 ∧
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c j₁
                  (WangOuter.paperLambda K c) ρ)
              MeasureTheory.volume ρStart₁ ρStop₁ ∧
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c j₂
                  (WangOuter.paperLambda K c) ρ)
              MeasureTheory.volume ρStart₂ ρStop₂ ∧
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              OneModePaperBridge.innerSeriesExcess a b c ∧
            (1 : ℝ) ≤
              (∫ ρ in ρStart₁..ρStop₁,
                  ModeBridge.scalarIntegrand c j₁
                    (WangOuter.paperLambda K c) ρ) +
                (∫ ρ in ρStart₂..ρStop₂,
                  ModeBridge.scalarIntegrand c j₂
                    (WangOuter.paperLambda K c) ρ)) :
    ValidKorenblumBound c :=
  valid_of_perMode_twoWindow_tau_partition_eq8_eq9 hc_pos hc_lt_one h_witness

/--
Paper-faithful candidate: the V60-tied `c = 0.35645` is a valid
Korenblum lower bound, routed through `valid_of_eq15` and discharged
by `hEq15_oracle_certified_hp_35645`.

The structural sprint-078 advance is **upstream** of this candidate's
discharge route: the new closing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` in
`Proof/Reduction.lean`, exercised by
`v61_two_window_reducer_compiles_at_witness` above.

V61 ties V60's c (rather than pushing to the Phase 0 witness c=0.35646)
because the load-bearing `hMassTotal` premise of the new reducer
requires a substantial numerical-discharge layer (interval-arithmetic
`norm_num` Riemann lower-bound on the Wang-Λ kernel, or a new
`Numerical_Library` oracle row). Per the contract's fallback, this
candidate ships the structural advance (new reducer + Phase 0 witness)
without consuming the witness for a c-push; the next planner picks
that up in sprint 079.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V61
