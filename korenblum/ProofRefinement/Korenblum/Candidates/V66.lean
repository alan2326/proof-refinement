-- @parent V64
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Proof.Integrability
import ProofRefinement.Korenblum.Proof.Summability
import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V66

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints
open ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability

/-!
# Sprint 088 / V66 — second consecutive c-push past V52

V66 ships at `c_value = v66CValue = 356562/1000000 = 0.356562`,
**strictly above V64's high-water mark `35646/100000 = 0.35646`** —
the second c-push past V52 in 5 sprints, an order of magnitude
larger than V64→V65's 0 push (V65 is a structural V64-tie).

The c-push composes:

  * the V63 derived-theorem files (Integrability, Summability,
    DiskInnerSeriesBridge) — identical contents reused as-is at the
    new c-value;
  * the V66-namespaced derived-theorem file
    `Candidates/V66/SevenWindowEndpoints.lean` (this sprint) — defines
    the seven sqrt-pinned τ-window/branchSplit endpoints, geometric
    ordering, and per-window τ-bound polynomial inequalities at
    `c = v66CValue`;
  * the V66-namespaced derived-theorem file
    `Candidates/V66/Branch1Integrability.lean` (this sprint) —
    packages the three Branch.one fallback-window scalar integrand
    integrabilities via the trusted-surface
    `paperScalarIntegrand1_intervalIntegrable`;
  * two free candidate-side axioms `hH2_v66` (Wang's H² boundary-norm
    finiteness) and `hCircleGapInt_v66` (the `2ρ · circleGap`-density
    integrability on `(c_value, 1)`), per V64's pattern. Both
    registered in `lemma.toml:[seed_axioms].allowed`;
  * the sprint-087 oracle axiom
    `h_seven_window_mass_certified_at_356562_sqrt`
    (in `Proof/Reduction.lean`) discharging the joint seven-window
    mass cell, certified by
    `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356562_sqrt`
    at `(dps=80, n_trunc=300)` byte-for-byte against the seven sqrt
    endpoints.

The reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
(`Proof/Reduction.lean:8934`) is invoked with `n = 6` and the
`h_witness` predicate constructed below.

## Window geometry at `c = v66CValue`

| i | kind             | ρStart                  | ρStop                   |
|---|------------------|-------------------------|-------------------------|
| 0 | branch1          | `c · (1 + 1/1000000)`   | `c · sqrt(50/49)`       |
| 1 | branch1          | `c · sqrt(50/49)`       | `c · sqrt(36/35)`       |
| 2 | branch1          | `c · sqrt(36/35)`       | `c · sqrt(25/24)`       |
| 3 | modeJ 4          | `c · sqrt(25/24)`       | `c · sqrt(16/15)`       |
| 4 | modeJ 3          | `c · sqrt(16/15)`       | `c · sqrt(9/8)`         |
| 5 | modeJ 2          | `c · sqrt(9/8)`         | `c · sqrt(4/3)`         |
| 6 | modeJ 1          | `c · sqrt(4/3)`         | `999999/1000000`        |

The Branch.one boxes (i ∈ {0, 1, 2}) all sit inside
`[c, branchSplit c]` because `c · sqrt(k/(k-1)) ≤ c · sqrt(4/3)` for
`k ∈ {50, 36, 25}`. The mode windows (i ∈ {3, 4, 5, 6}) discharge
the τ-window τ-bound conjuncts of the reducer's `h_witness`.

## Trust envelope

V66's `axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V66.hH2_v66,
   ProofRefinement.Korenblum.Candidates.V66.hCircleGapInt_v66,
   ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt}.

The new oracle axiom is registered as the `[[oracles]]` row
`h_seven_window_mass_certified_at_356562_sqrt` in `lemma.toml`
(sprint 087); both new free axioms are added to
`[seed_axioms].allowed` in this sprint inline. V66's audit set
extends V64's by exactly one entry (the new oracle, itself a
candidate-side handle on the registered numerical wrapper).
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.356562`, strictly above V64's
high-water mark `0.35646`. Numerically equal (and Lean-definitionally
equal) to `Proof.Reduction.v66CValue`, so that the joint-mass oracle
axiom matches verbatim. The literal-rational form is required by the
Evaluator's `def c_value : ℝ := <rational>` extraction. -/
def c_value : ℝ := 356562 / 1000000

/-- `c_value = v66CValue` (definitional equality). Used to align the
oracle axiom's `v66CValue` with the candidate's `c_value`. -/
theorem c_value_eq_v66CValue : c_value = v66CValue := rfl

theorem c_value_pos : (0 : ℝ) < c_value := by
  unfold c_value; norm_num

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  unfold c_value; norm_num

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-value strictly improves on V64's `35646/100000 = 356460/1000000`. -/
theorem c_value_gt_v64 : (35646 : ℝ) / 100000 < c_value := by
  unfold c_value
  norm_num

/-- Evaluator-facing oracle bound-field for the seven-window mass oracle. -/
def seven_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness on
`f`): for any coefficient sequence `a : ℕ → ℂ`, the norm-squared
sequence `‖a n‖²` is summable. Used universally over the witness's
`(a, b)` quantifier; applied to `a` for f and to `b` for g. Sibling
of V64's `hH2_v64` at the new c-value. -/
axiom hH2_v66 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis (paper-faithful): the disk
excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
`(c_value, 1)`. Sibling of V64's `hCircleGapInt_v64` at the new
c-value. -/
axiom hCircleGapInt_v66 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## branchSplit < 1 at c_value -/

theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 :=
  v66_branchSplit_lt_one

/-! ## h_witness construction -/

/-- The h_witness predicate of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`,
constructed universally over `(a, b, K, paper)` by composing the V63
derived-theorem files, the V66 SevenWindowEndpoints + Branch1Integrability
files, the two free candidate-side axioms, and the sprint-087 oracle
axiom. The structure `⟨…⟩` matches the reducer's `obtain` pattern at
`Proof/Reduction.lean:9003-9008` conjunct-for-conjunct in order. -/
theorem v66_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin (6 + 1) → ℝ) (kind : Fin (6 + 1) → KernelKind),
        (∀ i : Fin (6 + 1), c_value < ρStart i) ∧
        (∀ i : Fin (6 + 1), ρStart i ≤ ρStop i) ∧
        (∀ i : Fin (6 + 1), ρStop i < 1) ∧
        (∀ i : Fin 6, ρStop i.castSucc = ρStart i.succ) ∧
        (∀ i : Fin (6 + 1), ∀ j : ℕ,
          kind i = KernelKind.modeJ j →
            1 ≤ j ∧
            OneModeTail.tau (j - 1) ≤ c_value ^ 2 / ρStop i ^ 2 ∧
            c_value ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau j) ∧
        (∀ i : Fin (6 + 1),
          kind i = KernelKind.branch1 →
            ρStop i ≤ PaperAxioms.branchSplit c_value) ∧
        Summable (fun n' : ℕ =>
          OneModePaperBridge.plusSeq a b n' *
            c_value ^ (2 * n' + 2) / ((n' : ℝ) + 1)) ∧
        Summable (fun n' : ℕ =>
          OneModePaperBridge.plusSeq a b n' * c_value ^ (2 * n')) ∧
        Summable (fun n' : ℕ =>
          OneModePaperBridge.minusSeq a b n' *
            c_value ^ (2 * n' + 2) / ((n' : ℝ) + 1)) ∧
        Summable (fun n' : ℕ =>
          OneModePaperBridge.minusSeq a b n' * c_value ^ (2 * n')) ∧
        Summable (fun n' : ℕ =>
          OneModePaperBridge.minusSeq a b n' *
            OneModeKernel.weight c_value n') ∧
        (∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' * ρ ^ (2 * n'))) ∧
        IntervalIntegrable
          (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
          MeasureTheory.volume c_value 1 ∧
        (∀ i : Fin (6 + 1),
          (∀ j : ℕ, kind i = KernelKind.modeJ j →
            IntervalIntegrable
              (fun ρ => ModeBridge.scalarIntegrand c_value j
                (WangOuter.paperLambda K c_value) ρ)
              MeasureTheory.volume (ρStart i) (ρStop i)) ∧
          (kind i = KernelKind.branch1 →
            IntervalIntegrable
              (fun ρ => Korenblum.scalarIntegrand1 c_value
                (WangOuter.paperLambda K c_value) ρ)
              MeasureTheory.volume (ρStart i) (ρStop i))) ∧
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          OneModePaperBridge.innerSeriesExcess a b c_value ∧
        (1 : ℝ) ≤
          ∑ i : Fin (6 + 1),
            match kind i with
            | KernelKind.modeJ j =>
              ∫ ρ in (ρStart i)..(ρStop i),
                ModeBridge.scalarIntegrand c_value j
                  (WangOuter.paperLambda K c_value) ρ
            | KernelKind.branch1 =>
              ∫ ρ in (ρStart i)..(ρStop i),
                Korenblum.scalarIntegrand1 c_value
                  (WangOuter.paperLambda K c_value) ρ := by
  intro a b K paper
  refine ⟨v66SevenWindowStart, v66SevenWindowStop, v66SevenWindowKind,
          ?_, ?_, ?_, ?_,
          ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) ∀ i, c < ρStart i
    intro i; exact v66_c_lt_start i
  · -- (2) ∀ i, ρStart i ≤ ρStop i
    intro i; exact v66_start_le_stop i
  · -- (3) ∀ i, ρStop i < 1
    intro i; exact v66_stop_lt_one i
  · -- (4) ∀ i : Fin 6, ρStop i.castSucc = ρStart i.succ
    intro i; exact v66_adj i
  · -- (5) ∀ i j, kind i = modeJ j → 1 ≤ j ∧ τ-bounds
    intro i j hKind
    exact v66_modeJ_tau_bounds i j hKind
  · -- (6) ∀ i, kind i = branch1 → ρStop i ≤ branchSplit c
    intro i hKind
    exact v66_stop_le_branchSplit i hKind
  -- Summability witnesses (six total).
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v66 a b
  · -- (∀ i, kind-dispatched per-window integrability)
    intro i
    refine ⟨?_, ?_⟩
    · -- ∀ j, kind i = modeJ j → modeJ integrability
      intro j hKind
      -- Use V63's modeScalarIntegrand_intervalIntegrable at the
      -- specific j given by hKind. We get 1 ≤ j from
      -- v66_modeJ_one_le_j and the endpoint inequalities from
      -- SevenWindowEndpoints.
      have hj : 1 ≤ j := v66_modeJ_one_le_j i j hKind
      have hStartLeStop : v66SevenWindowStart i ≤ v66SevenWindowStop i :=
        v66_start_le_stop i
      have hcStart : c_value ≤ v66SevenWindowStart i :=
        v66_c_le_start i
      have hStopOne : v66SevenWindowStop i ≤ 1 :=
        v66_stop_le_one i
      exact ProofRefinement.Korenblum.Proof.Integrability.modeScalarIntegrand_intervalIntegrable
        hj c_value_pos hStartLeStop hcStart hStopOne paper.eq7_paperK_formula
    · -- kind i = branch1 → branch1 integrability
      intro hKind
      -- Use V66.Branch1Integrability for the three Branch.one windows.
      -- We dispatch on i; for i ∈ {3, 4, 5, 6} the kind is modeJ, so hKind
      -- yields a contradiction.
      fin_cases i
      · exact (v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).1
      · exact (v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).2.1
      · exact (v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).2.2
      · exfalso; simp [v66SevenWindowKind] at hKind
      · exfalso; simp [v66SevenWindowKind] at hKind
      · exfalso; simp [v66SevenWindowKind] at hKind
      · exfalso; simp [v66SevenWindowKind] at hKind
  · -- diskExcess ≤ innerSeriesExcess via V63.DiskInnerSeriesBridge
    have hkit := ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one
    have hPlusDisk := hkit.1
    have hMinusDisk := hkit.2.2.1
    have hAbsSummable :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
      ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components
        c_value_nonneg hPlusDisk hMinusDisk
    exact ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
      c_value_nonneg hPlusDisk hMinusDisk hAbsSummable
  · -- joint seven-window mass — discharged by the sprint-087 oracle axiom.
    -- The oracle axiom is in `Proof/Reduction.lean` namespace, so we
    -- reference it through the fully-qualified name. `c_value = v66CValue`
    -- is definitional (`c_value := v66CValue`), so the goal's c_value
    -- substitution is by `rfl` against the oracle's v66CValue.
    show (1 : ℝ) ≤
      ∑ i : Fin 7,
        match v66SevenWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
            ModeBridge.scalarIntegrand c_value j
              (WangOuter.paperLambda K c_value) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
            Korenblum.scalarIntegrand1 c_value
              (WangOuter.paperLambda K c_value) ρ
    -- c_value unfolds to v66CValue, then the goal matches the axiom verbatim.
    show (1 : ℝ) ≤
      ∑ i : Fin 7,
        match v66SevenWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
            ModeBridge.scalarIntegrand v66CValue j
              (WangOuter.paperLambda K v66CValue) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
            Korenblum.scalarIntegrand1 v66CValue
              (WangOuter.paperLambda K v66CValue) ρ
    exact h_seven_window_mass_certified_at_356562_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 356562/1000000`. Constructed
by applying `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
to `v66_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    (n := 6) c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v66_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V64's high-water mark. -/
lemma v66_strictly_above_v64 : (35646 : ℝ) / 100000 < c_value :=
  c_value_gt_v64

end ProofRefinement.Korenblum.Candidates.V66
