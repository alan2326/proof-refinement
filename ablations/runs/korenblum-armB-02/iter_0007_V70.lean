-- @parent V64
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V70

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

/-!
# V70 — c-push to `356533/1000000` on the two-window τ-partition route

`c_value = 356533/1000000 = 0.356533`, strictly above the parent's
`35653/100000 = 0.356530`.  Structurally this is the parent's chain verbatim:
the closing reducer `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, the
three V63 derived-theorem files, and V64's `TauWindowEndpoints` module (whose
endpoint `def`s and four τ-bound discharges are parametric in `c`, so they
specialise to the new radius unchanged).  Only the single `c`-pinned ordering
lemma `ρ_meet_sqrt c < 999999/1000000` needs a sibling here.

## Where the headroom comes from

The window geometry is forced, not chosen: adjacency `ρStop₁ = ρStart₂` plus
the two τ-bounds at `tau 1 = 3/4` pin `ρStop₁² = 4c²/3` exactly, and
`tau 2 = 8/9` pins the mode-2 lower endpoint at `c·√(9/8)`.  No free parameter
remains, and a third (mode-3) window would sit where Wang's `K` reaches `1`,
carrying no certifiable mass.  So the push comes entirely from certifying the
*same* integral more tightly.

`Numerical_Library.two_window_push` integrates the `ρ^(2j+1)` factor of
`ModeBridge.scalarIntegrand` exactly on each sub-interval and freezes only `Λ`
at a per-cell upper bound taken from the two endpoint values of `K` — legitimate
because `K` increases in `t = (ρ²−c)²/(4cρ²)` and `t` is unimodal in `ρ` with
minimum at `√c`, so `sup K` on a cell is attained at an endpoint.  Cells where
`K² < 1` cannot be certified contribute `0`, which underestimates: on the Lean
side `Real.sqrt` of a negative argument is `0`, so `paperLambda = 1/2` there and
the true integrand is large.  The grid refines `16384 → 131072`, reusing `K`
values across refinements.

## Trust envelope

`axioms_used` is {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
Lean.trustCompiler, `h_two_window_mass_certified_at_356533_sqrt`, `hH2_v70`,
`hCircleGapInt_v70`}.  `hH2_v70` is Wang's Hypothesis 1 of Section 2 (H²
boundary-norm finiteness, applied to `a` for `f` and to `b` for `g`);
`hCircleGapInt_v70` is the paper-implicit integrability of the polar-Jacobian
disk-excess density on the open annulus.  Both are strictly weaker than the
conclusion and neither is oracle-shaped; both are registered in
`[seed_axioms].allowed`.
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.356533`. -/
def c_value : ℝ := 356533 / 1000000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- Strictly improves on the parent's `35653/100000`. -/
theorem c_value_gt_parent : (35653 : ℝ) / 100000 < c_value := by
  norm_num [c_value]

/-- Evaluator-facing oracle bound-field. -/
def two_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2: H² boundary-norm finiteness.  Consumed
twice below — once for `f`'s coefficients `a`, once for `g`'s coefficients `b`. -/
axiom hH2_v70 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis: the polar-Jacobian disk-excess density
`2ρ · circleGap a b ρ` is `IntervalIntegrable` on `(c_value, 1)`.  The bundled
`Section2Assumptions` states pointwise identities and bounds but never asserts
measurability of `circleGap`. -/
axiom hCircleGapInt_v70 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## Oracle axiom — the joint two-window mass at sqrt endpoints -/

/-- Joint two-window mass at the exact sqrt endpoints, `(j₁, j₂) = (2, 1)`.

Discharged by the registered oracle
`h_two_window_mass_certified_at_356533_sqrt`, wrapper
`Numerical_Library.two_window_push.certify_two_window_mass_at_356533_sqrt`,
pinning `c = 356533/1000000`, `ρStart₁ = c·√(9/8)`, `ρStop₁ = c·√(4/3)`
(`= ρStart₂`), `ρStop₂ = 999999/1000000` at `(dps = 80, n_trunc = 16)`.  The
wrapper succeeds only when a rigorous `flint.arb` interval lower bound on the
joint mass clears `1 + 10^(-30)`.

`K` is universal because `paperLambda K c ρ` varies with `K`; only its values on
the two windows matter, and those are pinned by `Eq7PaperKFormula K c_value`. -/
axiom h_two_window_mass_certified_at_356533_sqrt
    (K : ℝ → ℝ → ℝ)
    (hK : PaperAxioms.Eq7PaperKFormula K c_value) :
  (1 : ℝ) ≤
    (∫ ρ in ρStart₁_sqrt c_value..ρ_meet_sqrt c_value,
        ModeBridge.scalarIntegrand c_value 2
          (WangOuter.paperLambda K c_value) ρ) +
      (∫ ρ in ρ_meet_sqrt c_value..(999999 / 1000000 : ℝ),
        ModeBridge.scalarIntegrand c_value 1
          (WangOuter.paperLambda K c_value) ρ)

/-! ## The one `c`-pinned ordering lemma -/

/-- At `c_value`, the shared endpoint `c · √(4/3)` sits below `999999/1000000`.
Bound `Real.sqrt (4/3) ≤ 1156/1000` via V64's `sqrt_four_thirds_le_rational`,
multiply by `c_value > 0`, and finish with a rational check (the left side is
≈ 0.41215, so the margin is ~6 orders of magnitude). -/
theorem ρ_meet_sqrt_lt_one_at_c_value :
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  unfold ρ_meet_sqrt c_value
  have hc_pos : (0 : ℝ) < 356533 / 1000000 := by norm_num
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 :=
    sqrt_four_thirds_le_rational
  have h1 : (356533 / 1000000 : ℝ) * Real.sqrt (4 / 3) ≤
      (356533 / 1000000 : ℝ) * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hc_pos)
  have h2 : (356533 / 1000000 : ℝ) * (1156 / 1000) < 999999 / 1000000 := by
    norm_num
  linarith

/-! ## The `h_witness` construction -/

/-- The `h_witness` predicate of
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, built universally over
`(a, b, K, paper)` from the three V63 derived-theorem files, V64's endpoint
module, the two free axioms, and the joint-mass oracle.  The `⟨…⟩` structure
matches the reducer's `obtain` pattern conjunct-for-conjunct. -/
theorem v70_witness :
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
  refine ⟨ρStart₁_sqrt c_value, ρ_meet_sqrt c_value,
          ρ_meet_sqrt c_value, 999999 / 1000000,
          2, 1, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · exact c_lt_ρStart₁_sqrt c_value_pos
  · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · exact (ρ_meet_sqrt_lt_one_at_c_value).le
  · norm_num
  · decide
  · exact le_refl 1
  · show OneModeTail.tau 1 ≤ c_value ^ 2 / (ρ_meet_sqrt c_value) ^ 2
    exact tau_one_le_c_sq_div_meet_sq_sqrt c_value_pos
  · exact c_sq_div_start1_sq_le_tau_two_sqrt c_value_pos
  · show OneModeTail.tau 0 ≤ c_value ^ 2 / ((999999 / 1000000 : ℝ)) ^ 2
    exact tau_zero_le_c_sq_div_stop2_sq c_value_nonneg
  · exact c_sq_div_meet_sq_le_tau_one_sqrt c_value_pos
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · exact hCircleGapInt_v70 a b
  · -- mode-2 scalar integrand on [ρStart₁_sqrt, ρ_meet_sqrt]
    have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
      ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
    have h_meet_le_one : ρ_meet_sqrt c_value ≤ 1 :=
      le_trans (ρ_meet_sqrt_lt_one_at_c_value).le
        (by norm_num : (999999 / 1000000 : ℝ) ≤ 1)
    have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
      le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
    exact (ProofRefinement.Korenblum.Candidates.V63.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
      c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_meet h_meet_le_meet
      h_meet_le_one paper.eq7_paperK_formula).1
  · -- mode-1 scalar integrand on [ρ_meet_sqrt, 999999/1000000]
    have h_meet_le_stop2 : ρ_meet_sqrt c_value ≤ (999999 / 1000000 : ℝ) :=
      (ρ_meet_sqrt_lt_one_at_c_value).le
    have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
      ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
    have h_stop2_le_one : (999999 / 1000000 : ℝ) ≤ 1 := by norm_num
    have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
      le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
    exact (ProofRefinement.Korenblum.Candidates.V63.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
      c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_stop2 h_meet_le_meet
      h_stop2_le_one paper.eq7_paperK_formula).2
  · -- diskExcess ≤ innerSeriesExcess
    have hkit := ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v70 a) (hH2_v70 b) c_value_nonneg c_value_lt_one
    have hPlusDisk := hkit.1
    have hMinusDisk := hkit.2.2.1
    have hAbsSummable :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
      ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components
        c_value_nonneg hPlusDisk hMinusDisk
    exact ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
      c_value_nonneg hPlusDisk hMinusDisk hAbsSummable
  · -- joint two-window mass — discharged by the oracle axiom.
    exact h_two_window_mass_certified_at_356533_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 356533/1000000`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    c_value_pos c_value_lt_one
    (fun {a b K} paper => v70_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on the parent's `35653/100000`. -/
lemma v70_strictly_above_parent : (35653 : ℝ) / 100000 < c_value :=
  c_value_gt_parent

/-- The τ-window endpoints satisfy the geometric ordering the reducer needs. -/
lemma v70_endpoint_ordering :
    c_value < ρStart₁_sqrt c_value ∧
    ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value ∧
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact c_lt_ρStart₁_sqrt c_value_pos
  · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · exact ρ_meet_sqrt_lt_one_at_c_value

end ProofRefinement.Korenblum.Candidates.V70
