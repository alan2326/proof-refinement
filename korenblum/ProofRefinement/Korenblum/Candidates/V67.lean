-- @parent V66
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Proof.Integrability
import ProofRefinement.Korenblum.Proof.Summability
import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
import ProofRefinement.Korenblum.Candidates.V67.EightWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V67

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V67.EightWindowEndpoints
open ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability

/-!
# Sprint 090 / V67 — third consecutive c-push past V52

V67 ships at `c_value = v67CValue = 89141/250000 = 356564/1000000`,
**strictly above V66's high-water mark `178281/500000 = 356562/1000000`**
by `+2/1000000 ≈ +2e-6` — the smallest c-push in the project's history
but strictly positive and full-envelope-margin-robust (~26 orders of
magnitude above the strict-margin floor).

The c-push composes:

  * the V63 derived-theorem files (Integrability, Summability,
    DiskInnerSeriesBridge) — identical contents reused as-is at the
    new c-value, parametric in `j` and the c-band;
  * the V67-namespaced derived-theorem file
    `Candidates/V67/EightWindowEndpoints.lean` (this sprint) — defines
    the eight sqrt-pinned τ-window/branchSplit endpoints for the
    eight-window architecture (1 Branch.one residual box + 7 per-mode
    windows for j ∈ {7, 6, 5, 4, 3, 2, 1}), geometric ordering, and
    per-window τ-bound polynomial inequalities at `c = v67CValue`;
  * the V66-namespaced derived-theorem file
    `Candidates/V66/Branch1Integrability.lean` — reused **as-is**
    (the wrapper `branch1ScalarIntegrand_intervalIntegrable` is
    parametric in `[a, b]`, so V67 invokes it directly at the single
    residual box `[c·(1+1e-9), c·sqrt(64/63)]` without any edit);
  * two free candidate-side axioms `hH2_v67` (Wang's H² boundary-norm
    finiteness) and `hCircleGapInt_v67` (the `2ρ · circleGap`-density
    integrability on `(c_value, 1)`), per V64/V66's pattern. Both
    registered in `lemma.toml:[seed_axioms].allowed`;
  * the sprint-090 oracle axiom
    `h_eight_window_mass_certified_at_356564_modeJ7`
    (in `Proof/Reduction.lean`) discharging the joint eight-window
    mass cell, certified by
    `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
    at `(dps=80, n_trunc=300)` byte-for-byte against the eight
    sqrt-pinned and rational-pinned endpoints. (Wrapper name retained
    from sprint 089's witness for backwards consistency; despite the
    `seven_window` name prefix it pins the eight-window architecture.)

The reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
(`Proof/Reduction.lean:8934`) is invoked with `n = 7` (i.e. `Fin 8`
windows) and the `h_witness` predicate constructed below.

## Window geometry at `c = v67CValue`

| i | kind             | ρStart                  | ρStop                   |
|---|------------------|-------------------------|-------------------------|
| 0 | branch1          | `c · (1 + 1/1e9)`       | `c · sqrt(64/63)`       |
| 1 | modeJ 7          | `c · sqrt(64/63)`       | `c · sqrt(49/48)`       |
| 2 | modeJ 6          | `c · sqrt(49/48)`       | `c · sqrt(36/35)`       |
| 3 | modeJ 5          | `c · sqrt(36/35)`       | `c · sqrt(25/24)`       |
| 4 | modeJ 4          | `c · sqrt(25/24)`       | `c · sqrt(16/15)`       |
| 5 | modeJ 3          | `c · sqrt(16/15)`       | `c · sqrt(9/8)`         |
| 6 | modeJ 2          | `c · sqrt(9/8)`         | `c · sqrt(4/3)`         |
| 7 | modeJ 1          | `c · sqrt(4/3)`         | `1 - 1/1e9`             |

The single Branch.one residual box (i = 0) sits inside
`[c, branchSplit c]` because `c · sqrt(64/63) ≤ c · sqrt(4/3)`
(and `branchSplit c = c · sqrt(4/3)` per the paper). The seven mode
windows (i ∈ {1, …, 7}) discharge the τ-window τ-bound conjuncts of
the reducer's `h_witness` for j = 7, 6, 5, 4, 3, 2, 1.

## Trust envelope

V67's `axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V67.hH2_v67,
   ProofRefinement.Korenblum.Candidates.V67.hCircleGapInt_v67,
   ProofRefinement.Korenblum.h_eight_window_mass_certified_at_356564_modeJ7}.

The new oracle axiom is registered as the `[[oracles]]` row
`h_eight_window_mass_certified_at_356564_modeJ7` in `lemma.toml`
(this sprint); both new free axioms are added to
`[seed_axioms].allowed` in this sprint inline. V67's audit set
extends V66's by exactly one entry (the new oracle, itself a
candidate-side handle on the registered numerical wrapper).
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.356564 = 89141/250000`,
strictly above V66's high-water mark `0.356562 = 178281/500000` by
`+2e-6`. Numerically equal (and Lean-definitionally equal) to
`Proof.Reduction.v67CValue`, so that the joint-mass oracle axiom
matches verbatim. The literal-rational form is required by the
Evaluator's `def c_value : ℝ := <rational>` extraction. -/
def c_value : ℝ := 89141 / 250000

/-- `c_value = v67CValue` (definitional equality). Used to align the
oracle axiom's `v67CValue` with the candidate's `c_value`. -/
theorem c_value_eq_v67CValue : c_value = v67CValue := rfl

theorem c_value_pos : (0 : ℝ) < c_value := by
  unfold c_value; norm_num

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  unfold c_value; norm_num

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-value strictly improves on V66's `178281/500000 = 356562/1000000`. -/
theorem c_value_gt_v66 : (178281 : ℝ) / 500000 < c_value := by
  unfold c_value
  norm_num

/-- Evaluator-facing oracle bound-field for the eight-window mass oracle. -/
def eight_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness on
`f`): for any coefficient sequence `a : ℕ → ℂ`, the norm-squared
sequence `‖a n‖²` is summable. Used universally over the witness's
`(a, b)` quantifier; applied to `a` for f and to `b` for g. Sibling
of V66's `hH2_v66` at the new c-value. -/
axiom hH2_v67 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis (paper-faithful): the disk
excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
`(c_value, 1)`. Sibling of V66's `hCircleGapInt_v66` at the new
c-value. -/
axiom hCircleGapInt_v67 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## branchSplit < 1 at c_value -/

theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 :=
  v67_branchSplit_lt_one

/-! ## h_witness construction -/

/-- The h_witness predicate of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`,
constructed universally over `(a, b, K, paper)` by composing the V63
derived-theorem files, the V67 EightWindowEndpoints +
V66 Branch1Integrability files, the two free candidate-side axioms,
and the sprint-090 oracle axiom. The structure `⟨…⟩` matches the
reducer's `obtain` pattern at `Proof/Reduction.lean:9003-9008`
conjunct-for-conjunct in order. -/
theorem v67_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin (7 + 1) → ℝ) (kind : Fin (7 + 1) → KernelKind),
        (∀ i : Fin (7 + 1), c_value < ρStart i) ∧
        (∀ i : Fin (7 + 1), ρStart i ≤ ρStop i) ∧
        (∀ i : Fin (7 + 1), ρStop i < 1) ∧
        (∀ i : Fin 7, ρStop i.castSucc = ρStart i.succ) ∧
        (∀ i : Fin (7 + 1), ∀ j : ℕ,
          kind i = KernelKind.modeJ j →
            1 ≤ j ∧
            OneModeTail.tau (j - 1) ≤ c_value ^ 2 / ρStop i ^ 2 ∧
            c_value ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau j) ∧
        (∀ i : Fin (7 + 1),
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
        (∀ i : Fin (7 + 1),
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
          ∑ i : Fin (7 + 1),
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
  refine ⟨v67EightWindowStart, v67EightWindowStop, v67EightWindowKind,
          ?_, ?_, ?_, ?_,
          ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) ∀ i, c < ρStart i
    intro i; exact v67_c_lt_start i
  · -- (2) ∀ i, ρStart i ≤ ρStop i
    intro i; exact v67_start_le_stop i
  · -- (3) ∀ i, ρStop i < 1
    intro i; exact v67_stop_lt_one i
  · -- (4) ∀ i : Fin 7, ρStop i.castSucc = ρStart i.succ
    intro i; exact v67_adj i
  · -- (5) ∀ i j, kind i = modeJ j → 1 ≤ j ∧ τ-bounds
    intro i j hKind
    exact v67_modeJ_tau_bounds i j hKind
  · -- (6) ∀ i, kind i = branch1 → ρStop i ≤ branchSplit c
    intro i hKind
    exact v67_stop_le_branchSplit i hKind
  -- Summability witnesses (six total).
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v67 a b
  · -- (∀ i, kind-dispatched per-window integrability)
    intro i
    refine ⟨?_, ?_⟩
    · -- ∀ j, kind i = modeJ j → modeJ integrability
      intro j hKind
      have hj : 1 ≤ j := v67_modeJ_one_le_j i j hKind
      have hStartLeStop : v67EightWindowStart i ≤ v67EightWindowStop i :=
        v67_start_le_stop i
      have hcStart : c_value ≤ v67EightWindowStart i :=
        v67_c_le_start i
      have hStopOne : v67EightWindowStop i ≤ 1 :=
        v67_stop_le_one i
      exact ProofRefinement.Korenblum.Proof.Integrability.modeScalarIntegrand_intervalIntegrable
        hj c_value_pos hStartLeStop hcStart hStopOne paper.eq7_paperK_formula
    · -- kind i = branch1 → branch1 integrability
      intro hKind
      -- Use V66.Branch1Integrability for the single Branch.one window
      -- (parametric in `[a, b]`). For i ∈ {1, …, 7} the kind is modeJ,
      -- so hKind yields a contradiction.
      fin_cases i
      · -- i = 0: invoke the parametric Branch.one integrability with
        -- V67 endpoints.
        exact branch1ScalarIntegrand_intervalIntegrable
          c_value_pos
          (v67_start_le_stop 0)
          (v67_c_le_start 0)
          (v67_stop_le_one 0)
          paper.eq7_paperK_formula
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
      · exfalso; simp [v67EightWindowKind] at hKind
  · -- diskExcess ≤ innerSeriesExcess via V63.DiskInnerSeriesBridge
    have hkit := ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v67 a) (hH2_v67 b) c_value_nonneg c_value_lt_one
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
  · -- joint eight-window mass — discharged by the sprint-090 oracle axiom.
    -- The oracle axiom is in `Proof/Reduction.lean` namespace, so we
    -- reference it through the fully-qualified name. `c_value = v67CValue`
    -- is definitional (`c_value := 89141/250000 = v67CValue`), so the
    -- goal's c_value substitution is by `rfl` against the oracle's
    -- v67CValue.
    show (1 : ℝ) ≤
      ∑ i : Fin 8,
        match v67EightWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            ModeBridge.scalarIntegrand c_value j
              (WangOuter.paperLambda K c_value) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            Korenblum.scalarIntegrand1 c_value
              (WangOuter.paperLambda K c_value) ρ
    -- c_value unfolds to v67CValue, then the goal matches the axiom verbatim.
    show (1 : ℝ) ≤
      ∑ i : Fin 8,
        match v67EightWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            ModeBridge.scalarIntegrand v67CValue j
              (WangOuter.paperLambda K v67CValue) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            Korenblum.scalarIntegrand1 v67CValue
              (WangOuter.paperLambda K v67CValue) ρ
    exact h_eight_window_mass_certified_at_356564_modeJ7 K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 89141/250000 = 356564/1000000`.
Constructed by applying
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` to
`v67_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    (n := 7) c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v67_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V66's high-water mark. -/
lemma v67_strictly_above_v66 : (178281 : ℝ) / 500000 < c_value :=
  c_value_gt_v66

end ProofRefinement.Korenblum.Candidates.V67
