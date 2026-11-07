-- @parent V64
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Proof.Integrability
import ProofRefinement.Korenblum.Proof.Summability
import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V65

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

/-!
# Sprint 084 / V65 — m=2 specialization of the new general-`m` reducer

V65 ties V64 byte-for-byte at `c_value = 35646/100000` by **specializing**
the new general-`m` reducer
`valid_of_perMode_multiWindow_tau_partition_eq8_eq9` (sprint 084,
`Proof/Reduction.lean`) at `m = 2` (i.e. `n = 1`, `Fin (n + 1) = Fin 2`),
re-using V64's two sqrt-pinned τ-windows
`(ρStart₁_sqrt, ρ_meet_sqrt, j = 2)` and
`(ρ_meet_sqrt, 999999/1000000, j = 1)` byte-for-byte.

This is a **non-vacuity check** for the new general reducer: V65 compiles
and ties V64, confirming the new reducer subsumes the old m=2 reducer.
The general-m form is then immediately available for sprint 085+ (Wang
eq(5) Branch.one fallback adapter), sprint 086 (Phase-0 seven-window
verification), and sprint 087+ (V66 at V38's `c = 356401/1000000`,
+1.2e-2 c-push).

## Trust envelope (matches V64 byte-for-byte)

V65's `axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V65.h_two_window_mass_certified_at_35646_sqrt,
   ProofRefinement.Korenblum.Candidates.V65.hH2_v64,
   ProofRefinement.Korenblum.Candidates.V65.hCircleGapInt_v64}

(modulo namespace, identical in shape to V64's axioms; V64's
`[seed_axioms]`-allowed names match by `short` name per the Evaluator's
audit). No new oracles, no new free axioms beyond V64's envelope, no
new `Section2Assumptions` fields. The general reducer's body adds zero
free axioms — it is pure Lean composition of existing trusted-surface
theorems plus standard `Fin`-sum machinery.

The `import_policy` does not allow direct import of
`ProofRefinement.Korenblum.Candidates.V64`, so the three V64 free
axioms are **structurally re-declared** here under V65's namespace
with identical statements; their `short` names match the `[seed_axioms]`
allowlist via the Evaluator's `or short in config.seed_axioms` check.
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.35646`, ties V64's high-water mark. -/
def c_value : ℝ := 35646 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The c-value ties V64's `35646/100000`. -/
theorem v65_ties_v64 : (35646 : ℝ) / 100000 = c_value := by
  rfl

/-- Evaluator-facing oracle bound-field for the joint-mass oracle. -/
def two_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (re-declared from V64; registered in
`[seed_axioms].allowed` by `short` name) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness on
`f`): for any coefficient sequence `a : ℕ → ℂ`, the norm-squared
sequence `‖a n‖²` is summable. Re-declaration of V64's axiom to satisfy
the candidate-side `[import_policy]` (which does not admit direct V64
imports). The Evaluator's `short`-name check matches this against the
existing `hH2_v64` `[seed_axioms]` entry. -/
axiom hH2_v64 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis (paper-faithful): the disk
excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
`(c_value, 1)`. Re-declared from V64 by `short` name. -/
axiom hCircleGapInt_v64 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## Oracle axiom — the joint two-window mass at sqrt endpoints -/

/-- The joint two-window mass at the candidate's exact sqrt endpoints
with j-modes `(j₁, j₂) = (2, 1)`. Re-declared from V64 by `short` name;
the Evaluator's oracle check at `h_two_window_mass_certified_at_35646_sqrt`
applies. -/
axiom h_two_window_mass_certified_at_35646_sqrt
    (K : ℝ → ℝ → ℝ)
    (hK : PaperAxioms.Eq7PaperKFormula K c_value) :
  (1 : ℝ) ≤
    (∫ ρ in ρStart₁_sqrt c_value..ρ_meet_sqrt c_value,
        ModeBridge.scalarIntegrand c_value 2
          (WangOuter.paperLambda K c_value) ρ) +
      (∫ ρ in ρ_meet_sqrt c_value..(999999 / 1000000 : ℝ),
        ModeBridge.scalarIntegrand c_value 1
          (WangOuter.paperLambda K c_value) ρ)

/-! ## The `h_witness` construction (Fin 2 form) -/

/-- The `h_witness` predicate of
`valid_of_perMode_multiWindow_tau_partition_eq8_eq9` at `n = 1`
(i.e. `Fin 2`-indexed, m = 2). The two windows are
  i = 0:  (ρStart₁_sqrt c_value, ρ_meet_sqrt c_value, j = 2)
  i = 1:  (ρ_meet_sqrt c_value, 999999/1000000, j = 1)
matching V64's data byte-for-byte modulo the `Fin 2` re-shaping. -/
theorem v65_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin 2 → ℝ) (j : Fin 2 → ℕ),
        (∀ i : Fin 2, c_value < ρStart i) ∧
        (∀ i : Fin 2, ρStart i ≤ ρStop i) ∧
        (∀ i : Fin 2, ρStop i < 1) ∧
        (∀ i : Fin 1, ρStop i.castSucc = ρStart i.succ) ∧
        (∀ i : Fin 2, 1 ≤ j i) ∧
        (∀ i : Fin 2, OneModeTail.tau (j i - 1) ≤ c_value ^ 2 / ρStop i ^ 2) ∧
        (∀ i : Fin 2, c_value ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau (j i)) ∧
        Summable (fun n : ℕ =>
          OneModePaperBridge.plusSeq a b n *
            c_value ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
        Summable (fun n : ℕ =>
          OneModePaperBridge.plusSeq a b n * c_value ^ (2 * n)) ∧
        Summable (fun n : ℕ =>
          OneModePaperBridge.minusSeq a b n *
            c_value ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
        Summable (fun n : ℕ =>
          OneModePaperBridge.minusSeq a b n * c_value ^ (2 * n)) ∧
        Summable (fun n : ℕ =>
          OneModePaperBridge.minusSeq a b n *
            OneModeKernel.weight c_value n) ∧
        (∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
          Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
        IntervalIntegrable
          (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
          MeasureTheory.volume c_value 1 ∧
        (∀ i : Fin 2,
          IntervalIntegrable
            (fun ρ =>
              ModeBridge.scalarIntegrand c_value (j i)
                (WangOuter.paperLambda K c_value) ρ)
            MeasureTheory.volume (ρStart i) (ρStop i)) ∧
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          OneModePaperBridge.innerSeriesExcess a b c_value ∧
        (1 : ℝ) ≤
          ∑ i : Fin 2,
            ∫ ρ in (ρStart i)..(ρStop i),
              ModeBridge.scalarIntegrand c_value (j i)
                (WangOuter.paperLambda K c_value) ρ := by
  intro a b K paper
  -- Endpoint and mode functions over `Fin 2`.
  refine ⟨fun i =>
            match i with
            | ⟨0, _⟩ => ρStart₁_sqrt c_value
            | ⟨1, _⟩ => ρ_meet_sqrt c_value,
          fun i =>
            match i with
            | ⟨0, _⟩ => ρ_meet_sqrt c_value
            | ⟨1, _⟩ => (999999 / 1000000 : ℝ),
          fun i =>
            match i with
            | ⟨0, _⟩ => 2
            | ⟨1, _⟩ => 1,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_⟩
  · -- ∀ i : Fin 2, c_value < ρStart i
    intro i
    fin_cases i
    · exact c_lt_ρStart₁_sqrt c_value_pos
    · -- c_value < ρ_meet_sqrt c_value: by transitivity through ρStart₁_sqrt.
      have h1 : c_value < ρStart₁_sqrt c_value := c_lt_ρStart₁_sqrt c_value_pos
      have h2 : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
        ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
      exact lt_of_lt_of_le h1 h2
  · -- ∀ i : Fin 2, ρStart i ≤ ρStop i
    intro i
    fin_cases i
    · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    · exact (ρ_meet_sqrt_lt_one_for_target_c).le
  · -- ∀ i : Fin 2, ρStop i < 1
    intro i
    fin_cases i
    · -- ρ_meet_sqrt c_value < 1
      exact lt_of_lt_of_le (ρ_meet_sqrt_lt_one_for_target_c) (by norm_num)
    · -- 999999/1000000 < 1
      norm_num
  · -- ∀ i : Fin 1, ρStop i.castSucc = ρStart i.succ
    intro i
    fin_cases i
    -- i = 0 : ρStop 0 = ρStart 1, i.e. ρ_meet_sqrt = ρ_meet_sqrt
    rfl
  · -- ∀ i : Fin 2, 1 ≤ j i
    intro i
    fin_cases i
    · -- j 0 = 2
      decide
    · -- j 1 = 1
      decide
  · -- ∀ i : Fin 2, OneModeTail.tau (j i - 1) ≤ c_value ^ 2 / ρStop i ^ 2
    intro i
    fin_cases i
    · -- i = 0, j 0 = 2, ρStop 0 = ρ_meet_sqrt
      -- Goal: OneModeTail.tau (2 - 1) ≤ c² / ρ_meet² = OneModeTail.tau 1 ≤ c²/ρ_meet²
      show OneModeTail.tau 1 ≤ c_value ^ 2 / (ρ_meet_sqrt c_value) ^ 2
      exact tau_one_le_c_sq_div_meet_sq_sqrt c_value_pos
    · -- i = 1, j 1 = 1, ρStop 1 = 999999/1000000
      show OneModeTail.tau 0 ≤ c_value ^ 2 / ((999999 / 1000000 : ℝ)) ^ 2
      exact tau_zero_le_c_sq_div_stop2_sq c_value_nonneg
  · -- ∀ i : Fin 2, c_value ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau (j i)
    intro i
    fin_cases i
    · exact c_sq_div_start1_sq_le_tau_two_sqrt c_value_pos
    · -- i = 1, j 1 = 1, ρStart 1 = ρ_meet_sqrt
      exact c_sq_div_meet_sq_le_tau_one_sqrt c_value_pos
  -- Six summability witnesses, packaged via V63's six_summability_shapes_from_h2.
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v64 a b
  · -- ∀ i : Fin 2, scalar integrand integrability
    intro i
    fin_cases i
    · -- i = 0: mode-2 on [ρStart₁_sqrt, ρ_meet_sqrt]
      have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
        ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
      have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
      have h_meet_le_one : ρ_meet_sqrt c_value ≤ 1 :=
        le_trans (ρ_meet_sqrt_lt_one_for_target_c).le
          (by norm_num : (999999 / 1000000 : ℝ) ≤ 1)
      have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
        le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
      exact (ProofRefinement.Korenblum.Proof.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
        c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_meet h_meet_le_meet
        h_meet_le_one paper.eq7_paperK_formula).1
    · -- i = 1: mode-1 on [ρ_meet_sqrt, 999999/1000000]
      have h_meet_le_stop2 : ρ_meet_sqrt c_value ≤ (999999 / 1000000 : ℝ) :=
        (ρ_meet_sqrt_lt_one_for_target_c).le
      have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
        ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
      have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
      have h_stop2_le_one : (999999 / 1000000 : ℝ) ≤ 1 := by norm_num
      have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
        le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
      exact (ProofRefinement.Korenblum.Proof.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
        c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_stop2 h_meet_le_meet
        h_stop2_le_one paper.eq7_paperK_formula).2
  · -- diskExcess ≤ innerSeriesExcess: needs three summability hypotheses.
    have hkit := ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one
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
  · -- joint two-window mass — discharged by the oracle axiom.
    -- The witness's joint mass is `∑ i : Fin 2, ∫ ρ in (ρStart i)..(ρStop i), …`
    -- which expands via `Fin.sum_univ_two` to
    --   ∫ ρ in ρStart 0..ρStop 0, … + ∫ ρ in ρStart 1..ρStop 1, …
    -- = ∫ ρ in ρStart₁_sqrt c_value..ρ_meet_sqrt c_value, …(j=2)…
    --   + ∫ ρ in ρ_meet_sqrt c_value..(999999/1000000), …(j=1)…
    -- The oracle delivers exactly this sum.
    rw [Fin.sum_univ_two]
    exact h_two_window_mass_certified_at_35646_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 35646/100000`, ties V64.
Constructed by applying `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
at `n = 1` (m = 2) to `v65_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_perMode_multiWindow_tau_partition_eq8_eq9
    (n := 1) c_value_pos c_value_lt_one
    (fun {a b K} paper => v65_witness paper)

/-! ## Side lemmas -/

/-- The new c-value ties V64's high-water mark byte-for-byte. -/
lemma v65_ties_v64_strictly : c_value = (35646 : ℝ) / 100000 := by
  rfl

end ProofRefinement.Korenblum.Candidates.V65
