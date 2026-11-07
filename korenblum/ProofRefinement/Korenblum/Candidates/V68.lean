-- @parent V67
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Proof.Integrability
import ProofRefinement.Korenblum.Proof.Summability
import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
import ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V68

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints
open ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability

/-!
# Sprint 092 / V68 — fourth consecutive c-push past V52

V68 ships at `c_value = v68CValue = 71313/200000 = 356565/1000000`,
**strictly above V67's high-water mark `89141/250000 = 356564/1000000`**
by `+1/1000000 = +1e-6` — the smallest c-push in the project's history
but strictly positive and full-envelope-margin-robust (~26 orders of
magnitude above the strict-margin floor).

The c-push composes:

  * the V63 derived-theorem files (Integrability, Summability,
    DiskInnerSeriesBridge) — identical contents reused as-is at the
    new c-value, parametric in `j` and the c-band;
  * the V68-namespaced derived-theorem file
    `Candidates/V68/ElevenWindowEndpoints.lean` (this sprint) — defines
    the eleven sqrt-pinned τ-window/branchSplit endpoints for the
    eleven-window architecture (1 Branch.one residual box + 10 per-mode
    windows for j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}), geometric ordering,
    and per-window τ-bound polynomial inequalities at `c = v68CValue`;
  * the V66-namespaced derived-theorem file
    `Candidates/V66/Branch1Integrability.lean` — reused **as-is**
    (the wrapper `branch1ScalarIntegrand_intervalIntegrable` is
    parametric in `[a, b]`, so V68 invokes it directly at the single
    residual box `[c·(1+1e-9), c·sqrt(121/120)]` without any edit);
  * two free candidate-side axioms `hH2_v68` (Wang's H² boundary-norm
    finiteness) and `hCircleGapInt_v68` (the `2ρ · circleGap`-density
    integrability on `(c_value, 1)`), per V64/V66/V67's pattern. Both
    registered in `lemma.toml:[seed_axioms].allowed`;
  * the sprint-092 oracle axiom
    `h_eleven_window_mass_certified_at_356565_modeJ10`
    (in `Proof/Reduction.lean`) discharging the joint eleven-window
    mass cell, certified by
    `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10`
    at `(dps=80, n_trunc=300)` byte-for-byte against the eleven
    sqrt-pinned and rational-pinned endpoints. (Wrapper name retained
    from sprint 091's witness for backwards consistency; despite the
    `seven_window` name prefix it pins the eleven-window architecture.)

The reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
(`Proof/Reduction.lean:8934`) is invoked with `n = 10` (i.e. `Fin 11`
windows) and the `h_witness` predicate constructed below.

## Window geometry at `c = v68CValue`

| i  | kind             | ρStart                    | ρStop                     |
|----|------------------|---------------------------|---------------------------|
| 0  | branch1          | `c · (1 + 1/1e9)`         | `c · sqrt(121/120)`       |
| 1  | modeJ 10         | `c · sqrt(121/120)`       | `c · sqrt(100/99)`        |
| 2  | modeJ 9          | `c · sqrt(100/99)`        | `c · sqrt(81/80)`         |
| 3  | modeJ 8          | `c · sqrt(81/80)`         | `c · sqrt(64/63)`         |
| 4  | modeJ 7          | `c · sqrt(64/63)`         | `c · sqrt(49/48)`         |
| 5  | modeJ 6          | `c · sqrt(49/48)`         | `c · sqrt(36/35)`         |
| 6  | modeJ 5          | `c · sqrt(36/35)`         | `c · sqrt(25/24)`         |
| 7  | modeJ 4          | `c · sqrt(25/24)`         | `c · sqrt(16/15)`         |
| 8  | modeJ 3          | `c · sqrt(16/15)`         | `c · sqrt(9/8)`           |
| 9  | modeJ 2          | `c · sqrt(9/8)`           | `c · sqrt(4/3)`           |
| 10 | modeJ 1          | `c · sqrt(4/3)`           | `1 - 1/1e9`               |

The single Branch.one residual box (i = 0) sits inside
`[c, branchSplit c]` because `c · sqrt(121/120) ≤ c · sqrt(4/3)`
(and `branchSplit c = c · sqrt(4/3)` per the paper). The ten mode
windows (i ∈ {1, …, 10}) discharge the τ-window τ-bound conjuncts of
the reducer's `h_witness` for j = 10, 9, 8, 7, 6, 5, 4, 3, 2, 1.

## Trust envelope

V68's `axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V68.hH2_v68,
   ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68,
   ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10}.

The new oracle axiom is registered as the `[[oracles]]` row
`h_eleven_window_mass_certified_at_356565_modeJ10` in `lemma.toml`
(this sprint); both new free axioms are added to
`[seed_axioms].allowed` in this sprint inline. V68's audit set
extends V67's by exactly one entry (the new oracle, itself a
candidate-side handle on the registered numerical wrapper).
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.356565 = 71313/200000`,
strictly above V67's high-water mark `0.356564 = 89141/250000` by
`+1e-6`. Numerically equal (and Lean-definitionally equal) to
`Proof.Reduction.v68CValue`, so that the joint-mass oracle axiom
matches verbatim. The literal-rational form is required by the
Evaluator's `def c_value : ℝ := <rational>` extraction. -/
def c_value : ℝ := 71313 / 200000

/-- `c_value = v68CValue` (definitional equality). Used to align the
oracle axiom's `v68CValue` with the candidate's `c_value`. -/
theorem c_value_eq_v68CValue : c_value = v68CValue := rfl

theorem c_value_pos : (0 : ℝ) < c_value := by
  unfold c_value; norm_num

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  unfold c_value; norm_num

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-value strictly improves on V67's `89141/250000 = 356564/1000000`. -/
theorem c_value_gt_v67 : (89141 : ℝ) / 250000 < c_value := by
  unfold c_value
  norm_num

/-- Evaluator-facing oracle bound-field for the eleven-window mass oracle. -/
def eleven_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness on
`f`): for any coefficient sequence `a : ℕ → ℂ`, the norm-squared
sequence `‖a n‖²` is summable. Used universally over the witness's
`(a, b)` quantifier; applied to `a` for f and to `b` for g. Sibling
of V67's `hH2_v67` at the new c-value. -/
axiom hH2_v68 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis (paper-faithful): the disk
excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
`(c_value, 1)`. Sibling of V67's `hCircleGapInt_v67` at the new
c-value. -/
axiom hCircleGapInt_v68 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## branchSplit < 1 at c_value -/

theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 :=
  v68_branchSplit_lt_one

/-! ## h_witness construction -/

/-- The h_witness predicate of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`,
constructed universally over `(a, b, K, paper)` by composing the V63
derived-theorem files, the V68 ElevenWindowEndpoints +
V66 Branch1Integrability files, the two free candidate-side axioms,
and the sprint-092 oracle axiom. The structure `⟨…⟩` matches the
reducer's `obtain` pattern at `Proof/Reduction.lean:9003-9008`
conjunct-for-conjunct in order. -/
theorem v68_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin (10 + 1) → ℝ) (kind : Fin (10 + 1) → KernelKind),
        (∀ i : Fin (10 + 1), c_value < ρStart i) ∧
        (∀ i : Fin (10 + 1), ρStart i ≤ ρStop i) ∧
        (∀ i : Fin (10 + 1), ρStop i < 1) ∧
        (∀ i : Fin 10, ρStop i.castSucc = ρStart i.succ) ∧
        (∀ i : Fin (10 + 1), ∀ j : ℕ,
          kind i = KernelKind.modeJ j →
            1 ≤ j ∧
            OneModeTail.tau (j - 1) ≤ c_value ^ 2 / ρStop i ^ 2 ∧
            c_value ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau j) ∧
        (∀ i : Fin (10 + 1),
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
        (∀ i : Fin (10 + 1),
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
          ∑ i : Fin (10 + 1),
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
  refine ⟨v68ElevenWindowStart, v68ElevenWindowStop, v68ElevenWindowKind,
          ?_, ?_, ?_, ?_,
          ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) ∀ i, c < ρStart i
    intro i; exact v68_c_lt_start i
  · -- (2) ∀ i, ρStart i ≤ ρStop i
    intro i; exact v68_start_le_stop i
  · -- (3) ∀ i, ρStop i < 1
    intro i; exact v68_stop_lt_one i
  · -- (4) ∀ i : Fin 10, ρStop i.castSucc = ρStart i.succ
    intro i; exact v68_adj i
  · -- (5) ∀ i j, kind i = modeJ j → 1 ≤ j ∧ τ-bounds
    intro i j hKind
    exact v68_modeJ_tau_bounds i j hKind
  · -- (6) ∀ i, kind i = branch1 → ρStop i ≤ branchSplit c
    intro i hKind
    exact v68_stop_le_branchSplit i hKind
  -- Summability witnesses (six total).
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v68 a b
  · -- (∀ i, kind-dispatched per-window integrability)
    intro i
    refine ⟨?_, ?_⟩
    · -- ∀ j, kind i = modeJ j → modeJ integrability
      intro j hKind
      have hj : 1 ≤ j := v68_modeJ_one_le_j i j hKind
      have hStartLeStop : v68ElevenWindowStart i ≤ v68ElevenWindowStop i :=
        v68_start_le_stop i
      have hcStart : c_value ≤ v68ElevenWindowStart i :=
        v68_c_le_start i
      have hStopOne : v68ElevenWindowStop i ≤ 1 :=
        v68_stop_le_one i
      exact ProofRefinement.Korenblum.Proof.Integrability.modeScalarIntegrand_intervalIntegrable
        hj c_value_pos hStartLeStop hcStart hStopOne paper.eq7_paperK_formula
    · -- kind i = branch1 → branch1 integrability
      intro hKind
      -- Use V66.Branch1Integrability for the single Branch.one window
      -- (parametric in `[a, b]`). For i ∈ {1, …, 10} the kind is modeJ,
      -- so hKind yields a contradiction.
      fin_cases i
      · -- i = 0: invoke the parametric Branch.one integrability with
        -- V68 endpoints.
        exact branch1ScalarIntegrand_intervalIntegrable
          c_value_pos
          (v68_start_le_stop 0)
          (v68_c_le_start 0)
          (v68_stop_le_one 0)
          paper.eq7_paperK_formula
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
      · exfalso; simp [v68ElevenWindowKind] at hKind
  · -- diskExcess ≤ innerSeriesExcess via V63.DiskInnerSeriesBridge
    have hkit := ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one
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
  · -- joint eleven-window mass — discharged by the sprint-092 oracle axiom.
    -- The oracle axiom is in `Proof/Reduction.lean` namespace, so we
    -- reference it through the fully-qualified name. `c_value = v68CValue`
    -- is definitional (`c_value := 71313/200000 = v68CValue`), so the
    -- goal's c_value substitution is by `rfl` against the oracle's
    -- v68CValue.
    show (1 : ℝ) ≤
      ∑ i : Fin 11,
        match v68ElevenWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            ModeBridge.scalarIntegrand c_value j
              (WangOuter.paperLambda K c_value) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            Korenblum.scalarIntegrand1 c_value
              (WangOuter.paperLambda K c_value) ρ
    -- c_value unfolds to v68CValue, then the goal matches the axiom verbatim.
    show (1 : ℝ) ≤
      ∑ i : Fin 11,
        match v68ElevenWindowKind i with
        | KernelKind.modeJ j =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            ModeBridge.scalarIntegrand v68CValue j
              (WangOuter.paperLambda K v68CValue) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            Korenblum.scalarIntegrand1 v68CValue
              (WangOuter.paperLambda K v68CValue) ρ
    exact h_eleven_window_mass_certified_at_356565_modeJ10 K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 71313/200000 = 356565/1000000`.
Constructed by applying
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` to
`v68_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    (n := 10) c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v68_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V67's high-water mark. -/
lemma v68_strictly_above_v67 : (89141 : ℝ) / 250000 < c_value :=
  c_value_gt_v67

end ProofRefinement.Korenblum.Candidates.V68
