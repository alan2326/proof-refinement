-- @parent V66
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V68

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

/-!
# V68 — c-push to `35653/100000` on the two-window τ-partition route

## What changes relative to V66

V68 is V66's closing chain re-pinned at

  `c_value = 35653/100000 = 0.35653`,

strictly above V66's `35651/100000 = 0.35651`. Everything structural is
reused unchanged:

  * the closing reducer
    `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
    (`Proof/Reduction.lean`);
  * the V63 derived-theorem files
    (`Integrability`, `Summability`, `DiskInnerSeriesBridge`);
  * V64's `TauWindowEndpoints` module — its endpoint `def`s and the four
    τ-bound discharges are **parametric in `c`**, so they specialise to
    the new `c_value` verbatim. Only the single `c`-pinned ordering
    lemma (`ρ_meet_sqrt c < 999999/1000000`) needs a sibling here,
    proved below from the same rational sqrt bound
    `Real.sqrt (4/3) ≤ 1156/1000`.

The one genuinely new input is the joint two-window mass at the pushed
radius. That is discharged by the new oracle-backed axiom
`h_two_window_mass_certified_at_35653_sqrt`, registered in
`lemma.toml:[[oracles]]` against the wrapper
`Numerical_Library.two_window_sqrt_push.certify_two_window_mass_at_35653_sqrt`,
which imports and reuses the audited `flint.arb` interval helpers from
`rigorous_scalar` unchanged with only the pinned `c` and the precision
envelope changed — and the envelope change is strictly in the
tightening direction (fewer truncation factors, which are conservative
either way, traded for a larger subdivision budget).

## Endpoint geometry (unchanged from V64/V65/V66, re-pinned)

  ρStart₁ = c · √(9/8)              ⇒ c²/ρStart₁² = 8/9 = tau(2)
  ρStop₁  = ρStart₂ = c · √(4/3)    ⇒ c²/ρStop₁²  = 3/4 = tau(1)
  ρStop₂  = 999999/1000000

These are the algebraically forced canonical τ-breakpoint endpoints for a
two-window τ-partition at `(j₁, j₂) = (2, 1)` with adjacency
`ρStop₁ = ρStart₂`; all four τ-bound inequalities hold with equality, so
no numerical headroom is consumed on the Lean side. The only
headroom-consuming Lean step is the coarse ordering check
`c · √(4/3) < 999999/1000000`, which has roughly six orders of magnitude
of slack.

## Where this sits on the route

Sprint 078's Phase 0 sweep places the joint two-window mass crossing
below `1` near `c ≈ 0.35654`. At `c = 0.35653` this candidate is
therefore close to saturating the two-window τ-partition route; a
further push on this axis would need either a finer partition (the
Bulletin's `m = 4`/`m = 7` V38-style envelope) or a tighter disk-side
bound.

## Trust envelope

`axioms_used` is

  {propext, Classical.choice, Quot.sound,
   …V68.h_two_window_mass_certified_at_35653_sqrt,
   …V68.hH2_v68,
   …V68.hCircleGapInt_v68}.

`hH2_v68` is Wang's Hypothesis 1 of Section 2 (H² boundary-norm
finiteness, applied to `a` for `f` and to `b` for `g`); `hCircleGapInt_v68`
is the paper-implicit integrability of the polar-Jacobian disk-excess
density on the open annulus. Both are strictly weaker than the conclusion
`ValidKorenblumBound c_value` and neither is oracle-shaped; both are
registered in `[seed_axioms].allowed`, exactly as their V64/V65/V66
siblings.
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.35653`, strictly above V66's
`0.35651`. -/
def c_value : ℝ := 35653 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-push strictly improves on V66's `35651/100000`. -/
theorem c_value_gt_v66 : (35651 : ℝ) / 100000 < c_value := by
  norm_num [c_value]

/-- Evaluator-facing oracle bound-field for the joint-mass oracle. -/
def two_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness): for
any coefficient sequence `a : ℕ → ℂ`, the norm-squared sequence `‖a n‖²`
is summable. Consumed twice inside `v68_witness` — once for `f`'s
coefficients `a`, once for `g`'s coefficients `b`. -/
axiom hH2_v68 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis: the polar-Jacobian disk-excess
density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on `(c_value, 1)`.
The bundled `Section2Assumptions` states pointwise identities and bounds
but never asserts measurability of `circleGap`; this axiom carries the
integrability witness directly. -/
axiom hCircleGapInt_v68 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## Oracle axiom — the joint two-window mass at sqrt endpoints -/

/-- The joint two-window mass at the candidate's exact sqrt endpoints with
j-modes `(j₁, j₂) = (2, 1)`.

Discharged by the registered oracle
`h_two_window_mass_certified_at_35653_sqrt`, whose wrapper is
`Numerical_Library.two_window_sqrt_push.certify_two_window_mass_at_35653_sqrt`,
pinning

  c            = 35653/100000
  ρStart₁      = c · √(9/8)
  ρStop₁       = c · √(4/3)   (= ρStart₂)
  ρStop₂       = 999999/1000000

at `(n_trunc = 60, dps = 60)` with a subdivision budget of `8192 → 32768`.
The wrapper returns success only when a **rigorous `flint.arb` interval
lower bound** on the joint mass — computed by equal-width left-Riemann
subdivision with monotonicity-aware Λ-upper dispatch around the single
peak of `K` at `ρ = √c`, refined until it clears `1 + 10^(-30)` — exceeds
the floor; otherwise it raises and the Evaluator records an oracle-check
failure.

The `K` argument is universal because `paperLambda K c ρ` varies with `K`;
only the values of `K` on the two integration windows matter, and those are
pinned by `Eq7PaperKFormula K c_value`. -/
axiom h_two_window_mass_certified_at_35653_sqrt
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

/-- At the pushed `c_value = 35653/100000`, the shared window endpoint
`ρ_meet_sqrt c_value = c · √(4/3)` sits strictly below `999999/1000000`.

Proof: bound `Real.sqrt (4/3) ≤ 1156/1000` via V64's
`sqrt_four_thirds_le_rational`, multiply by `c_value > 0`, and finish with
the rational check `(35653/100000) · (1156/1000) < 999999/1000000` (the
left side is ≈ 0.41215, so the margin is ~6 orders of magnitude). -/
theorem ρ_meet_sqrt_lt_one_at_c_value :
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  unfold ρ_meet_sqrt c_value
  have hc_pos : (0 : ℝ) < 35653 / 100000 := by norm_num
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 :=
    sqrt_four_thirds_le_rational
  have h1 : (35653 / 100000 : ℝ) * Real.sqrt (4 / 3) ≤
      (35653 / 100000 : ℝ) * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hc_pos)
  have h2 : (35653 / 100000 : ℝ) * (1156 / 1000) < 999999 / 1000000 := by
    norm_num
  linarith

/-! ## The `h_witness` construction -/

/-- The `h_witness` predicate of
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, constructed
universally over `(a, b, K, paper)` by composing the three V63
derived-theorem files, V64's parametric τ-window endpoint module, the two
free candidate-side axioms, and the new joint-mass oracle axiom.

The `⟨…⟩` structure matches the reducer's `obtain` pattern
conjunct-for-conjunct in order. -/
theorem v68_witness :
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
    exact (ρ_meet_sqrt_lt_one_at_c_value).le
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
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v68 a b
  · -- mode-2 scalar integrand integrability on [ρStart₁_sqrt, ρ_meet_sqrt]
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
  · -- mode-1 scalar integrand integrability on [ρ_meet_sqrt, 999999/1000000]
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
      (hH2_v68 a) (hH2_v68 b) c_value_nonneg c_value_lt_one
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
  · -- joint two-window mass — discharged by the new oracle axiom.
    exact h_two_window_mass_certified_at_35653_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 35653/100000`. Constructed by
applying `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` to
`v68_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    c_value_pos c_value_lt_one
    (fun {a b K} paper => v68_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V66's `35651/100000`. -/
lemma v68_strictly_above_v66 : (35651 : ℝ) / 100000 < c_value :=
  c_value_gt_v66

/-- Sanity check that the τ-window endpoints satisfy the geometric
ordering required by the reducer at the pushed `c_value`. -/
lemma v68_endpoint_ordering :
    c_value < ρStart₁_sqrt c_value ∧
    ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value ∧
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact c_lt_ρStart₁_sqrt c_value_pos
  · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · exact ρ_meet_sqrt_lt_one_at_c_value

end ProofRefinement.Korenblum.Candidates.V68
