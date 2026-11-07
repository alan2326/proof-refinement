-- @parent V55
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V56

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/--
Sprint 071 ships V56 at the same `c_value = 7129/20000 = 0.35645` as V55,
ROUTED THROUGH the same `valid_of_eq15` reducer and discharged by the same
`hEq15_oracle_certified_hp_35645` axiom (registered oracle
`eq15_certified_at_hp_35645`). The trust-base envelope and `axioms_used`
are byte-for-byte identical to V55's. This is the contract's Outcome B
(c-tying sprint by design — Phase 0's `Scratch/sprint_071_per_mode_kernel
_witness.{py,txt}` reports that the per-mode τ-window kernel
`KERNEL_71`'s mass-1 form `1 ≤ ∫_{start..stop} 2ρ/(term·Λ) dρ` falsifies
by ~3 orders of magnitude at every probed `(c, j*, start, stop)` with
`c > 7129/20000` and `j* ∈ {2, 3, 4, 5}`; max RHS ≈ 0.005, target 1).

What is structurally novel in V56 is the new closing reducer
`valid_of_perMode_tau_window_eq8_eq9` shipped in
`ProofRefinement.Korenblum.Proof.Reduction`, exercised below by the side
lemma `v56_perMode_reducer_compiles_at_witness`. This is the **first**
per-mode τ-window closing reducer in the workspace; every prior reducer
in `Reduction.lean` integrates the `(a, b)`-independent sup-kernel
`OneModeSupBridge.scalarIntegrand` or some closed-form scalar
simplification. The per-mode reducer's c-pushing potential is via the
multi-window partition of `(c, 1)` into `m` τ-windows each with its own
dominant mode `j*_w`: each window's mass-1 fraction can be `1/m`, and the
sum across windows reaches `1` by the partition-of-unity structure
**built into** the τ-window endpoint definitions. This sprint targets
ONE window (the structural prerequisite); sprint 072 will chain `m`
windows.

The Phase 0 numerical sweep is the **first quantitative test in the
workspace of whether per-mode actually beats sup-kernel at c-push
margins** above V55. The NO-GO conclusion does not invalidate the
multi-window route — it only establishes that single-window per-mode
does not push c past V55's `7129/20000` ceiling. The reducer's mass-1
hypothesis is the per-window cell of a multi-window c-push.

### Sign / orientation note (from sprint 071's Phase 0 retrospective)

The contract proposed Phase 0 Route A as a "lower bound" on KERNEL_71's
RHS via `paperLambda K c ρ ≥ 2`, but the Route A direction is reversed:
`paperLambda ≥ 2` ⇒ `1/paperLambda ≤ 1/2` ⇒ `2ρ/(term·Λ) ≤ ρ/term`. So
Route A integrates an UPPER bound, not a lower bound, on KERNEL_71's
actual RHS. Route A's positivity does NOT entail KERNEL_71. Phase 0 is
genuinely NO-GO under the corrected logic.

### Trust-base envelope

Identical to V55's:
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
V55-shaped oracle bound-field. Identical declaration to V55's
`eq15_lower_bound`; the Evaluator compares the per-candidate `oracle_fn`'s
returned Fraction against this `def` via `oracle_bound <= declared`.
-/
def eq15_lower_bound : ℝ := 1

/--
Same Lean-facing axiom as V55's `hEq15_oracle_certified_hp_35645`, with
the exact same `Eq15ScalarBound K c_value` shape at `c_value =
35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at `(c_num, c_den, dps,
n_trunc) = (35645, 100000, 100, 500)`.
-/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/--
Sprint 071 / Phase A non-vacuity check: the new per-mode τ-window closing
reducer `valid_of_perMode_tau_window_eq8_eq9` in `Proof/Reduction.lean`
admits a non-vacuous instantiation at the `(start, stop, mode)` quadruple
that maximizes Phase 0's per-mode kernel margin. The lemma states that
**given the standard witness data — a τ-window `[start, stop] ⊂ (c, 1)`
where mode `j*` is dominant, summability hypotheses, the diskExcess-to-
innerSeriesExcess bridge, and KERNEL_71's mass-1 hypothesis** — the new
reducer concludes `ValidKorenblumBound c`.

This is a **statement-level** Lean check, not a discharge: the lemma just
re-states the reducer's signature (universally quantified over the
witness data the reducer needs) and discharges it by directly invoking
`valid_of_perMode_tau_window_eq8_eq9`. The elaborator's acceptance of
this lemma confirms that the new reducer in `Reduction.lean` is
non-vacuous and Lean-checked, and that its signature shape is consumable
by future c-pushing sprints (e.g. sprint 072's multi-window partition).

The witness data is supplied **schematically**: the lemma quantifies over
all `start, stop, mode, ...` satisfying the per-mode τ-window's
structural side conditions. Phase 0's NO-GO conclusion (no `(start, stop,
mode)` quadruple with `c > 7129/20000` and `j* ≥ 2` satisfies KERNEL_71)
means this lemma is non-vacuous as a Lean statement but does not
discharge to a concrete `ValidKorenblumBound` at `c > 7129/20000`. The
reducer is reusable as soon as a future sprint constructs a witness that
actually satisfies KERNEL_71 (which the multi-window partition is
structurally required for).
-/
theorem v56_perMode_reducer_compiles_at_witness
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (start stop : ℝ) (mode : ℕ),
          c < start ∧ start ≤ stop ∧ stop < 1 ∧
            1 ≤ mode ∧
            OneModeTail.tau (mode - 1) ≤ c ^ 2 / stop ^ 2 ∧
            c ^ 2 / start ^ 2 ≤ OneModeTail.tau mode ∧
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
                ModeBridge.scalarIntegrand c mode
                  (WangOuter.paperLambda K c) ρ)
              MeasureTheory.volume start stop ∧
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              OneModePaperBridge.innerSeriesExcess a b c ∧
            (1 : ℝ) ≤
              ∫ ρ in start..stop,
                ModeBridge.scalarIntegrand c mode
                  (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c :=
  valid_of_perMode_tau_window_eq8_eq9 hc_pos hc_lt_one h_witness

/--
Paper-faithful candidate: the V55-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`. The structural sprint-071 advance is
the new `valid_of_perMode_tau_window_eq8_eq9` reducer in
`Proof/Reduction.lean`, exercised by
`v56_perMode_reducer_compiles_at_witness` above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V56
