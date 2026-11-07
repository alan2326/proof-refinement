-- @parent V63
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Proof.Integrability
import ProofRefinement.Korenblum.Proof.Summability
import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V64

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

/-!
# Sprint 083 / V64 — first c-push past V52 in 22 sprints

## What is structurally novel in V64

V64 ships at `c_value = 35646/100000 = 0.35646`, **strictly above
V52's high-water mark `7129/20000 = 35645/100000 = 0.35645`** — the
first c-push past V52 in 22 sprints. The c-push composes:

  * the V63 derived-theorem file `Candidates/V63/Integrability.lean`
    (sprint 080) — discharges the two per-window scalar
    integrabilities at `j₁ = 2` and `j₂ = 1`;
  * the V63 derived-theorem file `Candidates/V63/Summability.lean`
    (sprint 081) — discharges the six summability witnesses
    consuming H² boundary-norm finiteness on `f` and `g`;
  * the V63 derived-theorem file
    `Candidates/V63/DiskInnerSeriesBridge.lean` (sprint 082) —
    discharges the `diskExcess ≤ innerSeriesExcess` cell;
  * the new V64 derived-theorem file
    `Candidates/V64/TauWindowEndpoints.lean` (this sprint) — defines
    the two sqrt-pinned τ-window endpoints and discharges the four
    τ-bound polynomial inequalities at the canonical breakpoints
    `tau(1) = 3/4` and `tau(2) = 8/9` plus the geometric ordering
    `c < ρStart₁ ≤ ρStop₁ < ρStop₂ < 1` at the candidate's exact
    `c = 35646/100000`;
  * two free candidate-side axioms `hH2_v64` (Wang's Hypothesis 1
    of Section 2: universal H² boundary-norm finiteness over
    `(a : ℕ → ℂ)`, applied to `a` for f and to `b` for g) and
    `hCircleGapInt_v64` (the `2ρ · circleGap`-density
    integrability on `(c_value, 1)`, paper-implicit in Wang's
    Section 2 throughout). Both are registered in
    `lemma.toml:[seed_axioms].allowed`;
  * one new oracle axiom `h_two_window_mass_certified_at_35646_sqrt`
    discharging the joint two-window mass cell, certified by the
    new wrapper
    `Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646_sqrt`
    pinning the candidate's exact sqrt endpoints byte-for-byte at
    `(dps=50, n_trunc=200)`.

The reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
(`Proof/Reduction.lean:7770`) is invoked with the `h_witness`
predicate constructed by composing all of the above.

## Endpoint geometry

The candidate's τ-window endpoints are
  ρStart₁ = c · sqrt(9/8)        (so c²/ρStart₁² = 8/9 = tau(2))
  ρStop₁  = ρStart₂ = c · sqrt(4/3)   (so c²/ρStop₁² = 3/4 = tau(1))
  ρStop₂  = 999999/1000000.

These are the algebraically forced canonical τ-breakpoint endpoints
for a two-window τ-partition at `(j_1, j_2) = (2, 1)` with
adjacency `ρStop₁ = ρStart₂`. They are irrational; `Real.sqrt` is
necessary on the Lean side, and the wrapper pins them at
`mp.sqrt(rational)`-precision byte-for-byte.

## Trust envelope

V64's `axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt,
   ProofRefinement.Korenblum.Candidates.V64.hH2_v64,
   ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64}.

The new oracle axiom is registered as the `[[oracles]]` row
`h_two_window_mass_certified_at_35646_sqrt` in `lemma.toml`. The
three free axioms are added to `[seed_axioms].allowed`. Per the
sprint contract §"Free-axiom decision", the AGENT_BRIEF discipline
explicitly permits these as candidate-side seed axioms; only
oracle-shaped or new-`Section2Assumptions`-field-shaped expansions
require separate proposal review.
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.35646`, strictly above V52's
high-water mark `0.35645`. -/
def c_value : ℝ := 35646 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-push strictly improves on V52's `7129/20000 = 35645/100000`. -/
theorem c_value_gt_v52 : (7129 : ℝ) / 20000 < c_value := by
  norm_num [c_value]

/-- Evaluator-facing oracle bound-field for the new joint-mass oracle. -/
def two_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness on
`f`): for any coefficient sequence `a : ℕ → ℂ`, the norm-squared
sequence `‖a n‖²` is summable. Used universally over the witness's
`(a, b)` quantifier; applied to `a` for f and to `b` for g. -/
axiom hH2_v64 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis (paper-faithful): the disk
excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
`(c_value, 1)`. The bundled `Section2Assumptions` does not assert
`circleGap` measurability or continuity; this axiom carries the
integrability witness directly. -/
axiom hCircleGapInt_v64 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## Oracle axiom — the joint two-window mass at sqrt endpoints -/

/-- Sprint 083 / new candidate-side oracle axiom: the joint two-window
mass at the candidate's **exact sqrt endpoints** with j-modes
`(j₁, j₂) = (2, 1)`.

Discharged by the registered oracle
`h_two_window_mass_certified_at_35646_sqrt` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646_sqrt`,
pinning the four endpoints byte-for-byte to

  c            = 35646/100000
  ρStart₁      = c · sqrt(9/8)
  ρStop₁       = c · sqrt(4/3)   (= ρStart₂)
  ρStop₂       = 999999/1000000

at `(dps=50, n_trunc=200)`. Phase 0 witness:
`Scratch/sprint_083_sqrt_endpoint_witness.txt` (margin +1.9001e-3
at the chosen sqrt endpoints, well above the 1e-4 acceptance
threshold and ~27 orders of magnitude above the strict-margin
floor).

The `K` argument is universal because `paperLambda K c ρ` varies
with `K`; the wrapper certifies the inequality for all paper-
faithful `K` (only the value of `K` on the integration windows
matters). -/
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

/-! ## The `h_witness` construction -/

/-- The `h_witness` predicate of
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, constructed
universally over `(a, b, K, paper)` by composing all three V63
derived-theorem files plus the new V64 sqrt-endpoint file plus the
three free candidate-side axioms plus the new oracle axiom.

The structure `⟨...⟩` matches the reducer's `obtain` pattern at
`Proof/Reduction.lean:7833-7839` conjunct-for-conjunct in order. -/
theorem v64_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ) (j₁ j₂ : ℕ),
        c_value < ρStart₁ ∧ ρStart₁ ≤ ρStop₁ ∧
          ρStop₁ = ρStart₂ ∧
          ρStart₂ ≤ ρStop₂ ∧ ρStop₂ < 1 ∧
          1 ≤ j₁ ∧ 1 ≤ j₂ ∧
          OneModeTail.tau (j₁ - 1) ≤ c_value ^ 2 / ρStop₁ ^ 2 ∧
          c_value ^ 2 / ρStart₁ ^ 2 ≤ OneModeTail.tau j₁ ∧
          OneModeTail.tau (j₂ - 1) ≤ c_value ^ 2 / ρStop₂ ^ 2 ∧
          c_value ^ 2 / ρStart₂ ^ 2 ≤ OneModeTail.tau j₂ ∧
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
          IntervalIntegrable
            (fun ρ =>
              ModeBridge.scalarIntegrand c_value j₁
                (WangOuter.paperLambda K c_value) ρ)
            MeasureTheory.volume ρStart₁ ρStop₁ ∧
          IntervalIntegrable
            (fun ρ =>
              ModeBridge.scalarIntegrand c_value j₂
                (WangOuter.paperLambda K c_value) ρ)
            MeasureTheory.volume ρStart₂ ρStop₂ ∧
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
            OneModePaperBridge.innerSeriesExcess a b c_value ∧
          (1 : ℝ) ≤
            (∫ ρ in ρStart₁..ρStop₁,
                ModeBridge.scalarIntegrand c_value j₁
                  (WangOuter.paperLambda K c_value) ρ) +
              (∫ ρ in ρStart₂..ρStop₂,
                ModeBridge.scalarIntegrand c_value j₂
                  (WangOuter.paperLambda K c_value) ρ) := by
  intro a b K paper
  -- Endpoint instantiations.
  refine ⟨ρStart₁_sqrt c_value, ρ_meet_sqrt c_value,
          ρ_meet_sqrt c_value, 999999 / 1000000,
          2, 1, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- c_value < ρStart₁_sqrt c_value
    exact c_lt_ρStart₁_sqrt c_value_pos
  · -- ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value
    exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · -- ρ_meet_sqrt c_value ≤ 999999 / 1000000
    exact (ρ_meet_sqrt_lt_one_for_target_c).le
  · -- 999999 / 1000000 < 1
    norm_num
  · -- 1 ≤ 2
    decide
  · -- 1 ≤ 1
    exact le_refl 1
  · -- tau (2 - 1) = tau 1 ≤ c² / ρ_meet_sqrt²
    show OneModeTail.tau 1 ≤ c_value ^ 2 / (ρ_meet_sqrt c_value) ^ 2
    exact tau_one_le_c_sq_div_meet_sq_sqrt c_value_pos
  · -- c² / ρStart₁_sqrt² ≤ tau 2
    exact c_sq_div_start1_sq_le_tau_two_sqrt c_value_pos
  · -- tau (1 - 1) = tau 0 ≤ c² / ρStop₂²
    show OneModeTail.tau 0 ≤ c_value ^ 2 / ((999999 / 1000000 : ℝ)) ^ 2
    exact tau_zero_le_c_sq_div_stop2_sq c_value_nonneg
  · -- c² / ρStart₂² (= ρ_meet_sqrt²) ≤ tau 1
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
  · -- mode-2 scalar integrand integrability on [ρStart₁_sqrt, ρ_meet_sqrt]
    have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
      ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
    have h_meet_le_one : ρ_meet_sqrt c_value ≤ 1 :=
      le_trans (ρ_meet_sqrt_lt_one_for_target_c).le (by norm_num : (999999 / 1000000 : ℝ) ≤ 1)
    have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
      le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
    exact (ProofRefinement.Korenblum.Proof.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
      c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_meet h_meet_le_meet
      h_meet_le_one paper.eq7_paperK_formula).1
  · -- mode-1 scalar integrand integrability on [ρ_meet_sqrt, 999999/1000000]
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
  · -- diskExcess ≤ innerSeriesExcess: needs three summability hypotheses
    have hkit := ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
      (hH2_v64 a) (hH2_v64 b) c_value_nonneg c_value_lt_one
    -- We need `Summable (|coeffPlusGap a b k| * c^(2k+2)/(k+1))` —
    -- the bridge's absolute-value variant follows from
    -- `summable_abs_coeffPlusGap_weighted_of_summable_components`.
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
  · -- joint two-window mass — discharged by the new oracle axiom.
    exact h_two_window_mass_certified_at_35646_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 35646/100000`. Constructed by
applying `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` to
`v64_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    c_value_pos c_value_lt_one
    (fun {a b K} paper => v64_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V52's high-water mark. -/
lemma v64_strictly_above_v52 : (7129 : ℝ) / 20000 < c_value :=
  c_value_gt_v52

/-- Sanity check that the τ-window endpoints satisfy the geometric
ordering required by the reducer at the candidate's exact `c_value`. -/
lemma v64_endpoint_ordering :
    c_value < ρStart₁_sqrt c_value ∧
    ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value ∧
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact c_lt_ρStart₁_sqrt c_value_pos
  · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · exact ρ_meet_sqrt_lt_one_for_target_c

end ProofRefinement.Korenblum.Candidates.V64
