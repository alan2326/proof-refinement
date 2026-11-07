Resuming with the complete `ThreeWindow.lean` (compact form — the earlier emission was cut, so this is the whole file). The remaining three files follow in the next turn.

```lean path=ProofRefinement/Korenblum/Candidates/V69/ThreeWindow.lean
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

open Set MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V69.ThreeWindow

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-!
# V69 — three-window per-mode τ-partition

The two-window reducer is forced by adjacency plus the τ-bounds at
`(j₁, j₂) = (2, 1)` to take `ρStop₁ = c·√(4/3)` and `ρStart₁ ≥ c·√(9/8)`, so
it discards all annulus mass on `(c, c·√(9/8))`. This file adds the next
τ-window down — the mode-3 window `[c·√(16/15), c·√(9/8)]`, on which
`tau 2 ≤ c²/ρ² ≤ tau 3` — and ships `valid_of_perMode_threeWindow`.

Only `theorem`s and `def`s: no `axiom`, no `sorry`, no bundle extension.
-/

/-- Non-negativity of the polar-Jacobian annulus density on `(c, 1)`. -/
private theorem density_nonneg
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ} (hcr : c < ρ) (hρ1 : ρ < 1) :
    0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  have hC : 0 ≤ paper.circleGap ρ :=
    OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper hcr hρ1
  have hρpos : 0 < ρ := lt_trans hc_pos hcr
  change 0 ≤ 2 * ρ * paper.circleGap ρ
  nlinarith

/-- Sub-interval integrability of the annulus density. -/
private theorem dens_int_of_sub
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
    {x y : ℝ} (hxy : x ≤ y) (hcx : c ≤ x) (hy1 : y ≤ 1) (hc1 : c ≤ 1) :
    IntervalIntegrable
      (AnnulusIntegralReduction.annulusDensity paper.circleGap) volume x y := by
  have hsub : Set.uIcc x y ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hxy, Set.uIcc_of_le hc1]
    exact Set.Icc_subset_Icc hcx hy1
  exact hIntCircle.mono_set hsub

/-- Non-negativity of an annulus slice contained in `[c, 1]`. -/
private theorem slice_nonneg
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (paper : Section2Assumptions a b K c)
    {x y : ℝ} (hxy : x ≤ y) (hcx : c ≤ x) (hy1 : y ≤ 1) :
    0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap x y := by
  have hNonnegAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc x y),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo x y),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      exact density_nonneg hc_pos paper
        (lt_of_le_of_lt hcx hρ.1) (lt_of_lt_of_le hρ.2 hy1)
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
    (circleGap := paper.circleGap) (a := x) (b := y) hxy hNonnegAE

/-- One τ-window: its kernel mass is non-negative, and times `diskExcess` it is
dominated by the window's annulus slice. -/
theorem window_facts
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    {start stop : ℝ} {j : ℕ}
    (hj : 1 ≤ j)
    (hcStart : c < start) (hStartStop : start ≤ stop) (hStopOne : stop < 1)
    (hLower : OneModeTail.tau (j - 1) ≤ c ^ 2 / stop ^ 2)
    (hUpper : c ^ 2 / start ^ 2 ≤ OneModeTail.tau j)
    (hPlusDisk :
      Summable (fun n : ℕ =>
        OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hPlusSigma :
      Summable (fun n : ℕ => OneModePaperBridge.plusSeq a b n * c ^ (2 * n)))
    (hMinusDisk :
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
    (hMinusSigmaC :
      Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * c ^ (2 * n)))
    (hMinusWeight :
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n))
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
    (hInner :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        OneModePaperBridge.innerSeriesExcess a b c)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
    (hIntMode :
      IntervalIntegrable
        (fun ρ =>
          ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
        volume start stop) :
    0 ≤ (∫ ρ in start..stop,
            ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) ∧
      (∫ ρ in start..stop,
          ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) *
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap start stop := by
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  have hc_le_start : c ≤ start := hcStart.le
  have hStop_le_one : stop ≤ 1 := hStopOne.le
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c := by
    have h0c : (0 : ℝ) ≤ 0 := le_refl 0
    have h_eq4_at_zero :
        PaperAxioms.Eq4SigmaPlusBound (PaperAxioms.sigmaPlus a b)
          (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b) 0 c :=
      paper.eq4_sigmaPlus_bound h0c hc_pos hc_lt_one
    exact h_eq4_at_zero.2.1
  have hPointwiseIcc :
      ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc start stop →
        ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
    OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
      hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hPlusLeMinus hInner
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hMinusSigma hj hcStart hStopOne hLower hUpper
  have hPointwiseDensity :
      ∀ ρ ∈ Set.Icc start stop,
        (fun ρ' =>
          ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ') ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hPt := hPointwiseIcc hρ
    change ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ *
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      2 * ρ * paper.circleGap ρ
    have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
    rw [hCircleEq]
    exact hPt
  have hAnnNonneg :
      ∀ ρ ∈ Set.Icc start stop,
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    exact density_nonneg hc_pos paper
      (lt_of_lt_of_le hcStart hρ.1) (lt_of_le_of_lt hρ.2 hStopOne)
  have hIntDens :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume start stop :=
    dens_int_of_sub paper hIntCircle hStartStop hc_le_start hStop_le_one hc_le_one
  have hScalarNonneg :
      ∀ ρ ∈ Set.Icc start stop,
        0 ≤ ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hcStart hρ.1
    have hρpos : 0 < ρ := lt_trans hc_pos hcρ
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hTermNonneg : 0 ≤ OneModeKernel.term c ρ j := by
      unfold OneModeKernel.term OneModeKernel.weight
      have hcp : (0 : ℝ) ≤ c ^ (2 * j + 2) := pow_nonneg hc_pos.le _
      have hrp : (0 : ℝ) ≤ ρ ^ (2 * j) := pow_nonneg hρpos.le _
      have hjc : (0 : ℝ) ≤ (j : ℝ) / ((j : ℝ) + 1) := by
        refine div_nonneg (Nat.cast_nonneg j) ?_
        positivity
      exact div_nonneg (mul_nonneg hjc hcp) hrp
    have hDen :
        0 ≤ OneModeKernel.term c ρ j * WangOuter.paperLambda K c ρ :=
      mul_nonneg hTermNonneg hΛpos.le
    unfold ModeBridge.scalarIntegrand
    exact div_nonneg (by linarith) hDen
  have hMassNonneg :
      0 ≤ ∫ ρ in start..stop,
            ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ :=
    intervalIntegral.integral_nonneg hStartStop hScalarNonneg
  refine ⟨hMassNonneg, ?_⟩
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
    (modeIntegrand :=
      fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
    (circleGap := paper.circleGap) (a := start) (b := stop)
    (mass := ∫ ρ in start..stop,
      ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
    (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
    hStartStop hMassNonneg le_rfl hIntMode hIntDens
    hPointwiseDensity hAnnNonneg

/-- Three adjacent τ-windows with dominant modes `3, 2, 1`. If the three window
masses sum to at least `1`, the contract closes. -/
theorem valid_of_perMode_threeWindow
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ}
    (hcρ₀ : c < ρ₀) (h01 : ρ₀ ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (h23 : ρ₂ ≤ ρ₃)
    (hρ₃ : ρ₃ < 1)
    (hτ3lo : OneModeTail.tau 2 ≤ c ^ 2 / ρ₁ ^ 2)
    (hτ3hi : c ^ 2 / ρ₀ ^ 2 ≤ OneModeTail.tau 3)
    (hτ2lo : OneModeTail.tau 1 ≤ c ^ 2 / ρ₂ ^ 2)
    (hτ2hi : c ^ 2 / ρ₁ ^ 2 ≤ OneModeTail.tau 2)
    (hτ1lo : OneModeTail.tau 0 ≤ c ^ 2 / ρ₃ ^ 2)
    (hτ1hi : c ^ 2 / ρ₂ ^ 2 ≤ OneModeTail.tau 1)
    (h_data :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        Summable (fun n : ℕ =>
            OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
        Summable (fun n : ℕ =>
            OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
        Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
        Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
        Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) ∧
        (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
        IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1 ∧
        IntervalIntegrable
            (fun ρ => ModeBridge.scalarIntegrand c 3
              (WangOuter.paperLambda K c) ρ) volume ρ₀ ρ₁ ∧
        IntervalIntegrable
            (fun ρ => ModeBridge.scalarIntegrand c 2
              (WangOuter.paperLambda K c) ρ) volume ρ₁ ρ₂ ∧
        IntervalIntegrable
            (fun ρ => ModeBridge.scalarIntegrand c 1
              (WangOuter.paperLambda K c) ρ) volume ρ₂ ρ₃ ∧
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            OneModePaperBridge.innerSeriesExcess a b c ∧
        (1 : ℝ) ≤
            (∫ ρ in ρ₀..ρ₁, ModeBridge.scalarIntegrand c 3
                (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in ρ₁..ρ₂, ModeBridge.scalarIntegrand c 2
                (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in ρ₂..ρ₃, ModeBridge.scalarIntegrand c 1
                (WangOuter.paperLambda K c) ρ)) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨hPlusDisk, hPlusSigma, hMinusDisk, hMinusSigmaC, hMinusWeight,
      hMinusSigma, hIntCircle, hI3, hI2, hI1, hInner, hMass⟩ := h_data paper
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hcρ₀ h01
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ h12
  have hcρ₃ : c < ρ₃ := lt_of_lt_of_le hcρ₂ h23
  have h13 : ρ₁ ≤ ρ₃ := le_trans h12 h23
  have h03 : ρ₀ ≤ ρ₃ := le_trans h01 h13
  have h02 : ρ₀ ≤ ρ₂ := le_trans h01 h12
  have hρ₀1 : ρ₀ < 1 := lt_of_le_of_lt h03 hρ₃
  have hρ₁1 : ρ₁ < 1 := lt_of_le_of_lt h13 hρ₃
  have hρ₂1 : ρ₂ < 1 := lt_of_le_of_lt h23 hρ₃
  obtain ⟨hM3nn, hM3le⟩ :=
    window_facts paper hc_pos hc_lt_one (j := 3) (by decide) hcρ₀ h01 hρ₁1
      hτ3lo hτ3hi hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hMinusSigma hInner hIntCircle hI3
  obtain ⟨hM2nn, hM2le⟩ :=
    window_facts paper hc_pos hc_lt_one (j := 2) (by decide) hcρ₁ h12 hρ₂1
      hτ2lo hτ2hi hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hMinusSigma hInner hIntCircle hI2
  obtain ⟨hM1nn, hM1le⟩ :=
    window_facts paper hc_pos hc_lt_one (j := 1) (le_refl 1) hcρ₂ h23 hρ₃
      hτ1lo hτ1hi hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hMinusSigma hInner hIntCircle hI1
  have d01 := dens_int_of_sub paper hIntCircle h01 hcρ₀.le hρ₁1.le hc_le_one
  have d12 := dens_int_of_sub paper hIntCircle h12 hcρ₁.le hρ₂1.le hc_le_one
  have d23 := dens_int_of_sub paper hIntCircle h23 hcρ₂.le hρ₃.le hc_le_one
  have d02 := dens_int_of_sub paper hIntCircle h02 hcρ₀.le hρ₂1.le hc_le_one
  have d03 := dens_int_of_sub paper hIntCircle h03 hcρ₀.le hρ₃.le hc_le_one
  have dc0 := dens_int_of_sub paper hIntCircle hcρ₀.le (le_refl c) hρ₀1.le hc_le_one
  have d31 := dens_int_of_sub paper hIntCircle hρ₃.le hcρ₃.le (le_refl 1) hc_le_one
  have d0one := dens_int_of_sub paper hIntCircle
    (le_trans h03 hρ₃.le) hcρ₀.le (le_refl 1) hc_le_one
  have hA1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₂ :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent d01 d12
  have hA2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ ρ₃ =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₃ :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent d02 d23
  have hSum :
      ((∫ ρ in ρ₀..ρ₁, ModeBridge.scalarIntegrand c 3
            (WangOuter.paperLambda K c) ρ) +
          (∫ ρ in ρ₁..ρ₂, ModeBridge.scalarIntegrand c 2
            (WangOuter.paperLambda K c) ρ) +
          (∫ ρ in ρ₂..ρ₃, ModeBridge.scalarIntegrand c 1
            (WangOuter.paperLambda K c) ρ)) *
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₃ := by
    rw [add_mul, add_mul]
    linarith [hM3le, hM2le, hM1le, hA1, hA2]
  have hSlice03nn :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₃ :=
    slice_nonneg hc_pos paper h03 hcρ₀.le hρ₃.le
  have hDiskLe :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₃ := by
    by_cases hD : 0 ≤ PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
    · have h1 :
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            ((∫ ρ in ρ₀..ρ₁, ModeBridge.scalarIntegrand c 3
                (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in ρ₁..ρ₂, ModeBridge.scalarIntegrand c 2
                (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in ρ₂..ρ₃, ModeBridge.scalarIntegrand c 1
                (WangOuter.paperLambda K c) ρ)) *
              PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
        have := mul_le_mul_of_nonneg_right hMass hD
        simpa [one_mul] using this
      exact le_trans h1 hSum
    · exact le_trans (le_of_lt (lt_of_not_ge hD)) hSlice03nn
  have hS1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₀ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent dc0 d0one
  have hS2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ ρ₃ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₃ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₀ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent d03 d31
  have hN1 :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₀ :=
    slice_nonneg hc_pos paper hcρ₀.le (le_refl c) hρ₀1.le
  have hN2 :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₃ 1 :=
    slice_nonneg hc_pos paper hρ₃.le hcρ₃.le (le_refl 1)
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  rw [show PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
      = AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 from rfl]
  linarith [hDiskLe, hS1, hS2, hN1, hN2]

/-! ## The mode-3 window's left endpoint -/

/-- `ρ₀ = c·√(16/15)`, pinned so that `c²/ρ₀² = 15/16 = tau 3`. -/
def ρ_mode3_start (c : ℝ) : ℝ := c * Real.sqrt (16 / 15)

theorem ρ_mode3_start_sq (c : ℝ) :
    (ρ_mode3_start c) ^ 2 = c ^ 2 * (16 / 15) := by
  unfold ρ_mode3_start
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16 / 15)]

theorem c_sq_div_mode3_start_sq_le_tau_three {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (ρ_mode3_start c) ^ 2 ≤ OneModeTail.tau 3 := by
  rw [ρ_mode3_start_sq]
  have hcs : c ^ 2 ≠ 0 := by positivity
  have heq : c ^ 2 / (c ^ 2 * (16 / 15)) = 15 / 16 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

theorem tau_two_le_c_sq_div_start1_sq {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 2 ≤
      c ^ 2 / (V64.TauWindowEndpoints.ρStart₁_sqrt c) ^ 2 := by
  rw [V64.TauWindowEndpoints.ρStart₁_sqrt_sq]
  have hcs : c ^ 2 ≠ 0 := by positivity
  have heq : c ^ 2 / (c ^ 2 * (9 / 8)) = 8 / 9 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

theorem c_lt_ρ_mode3_start {c : ℝ} (hc : 0 < c) : c < ρ_mode3_start c := by
  unfold ρ_mode3_start
  have h : (1 : ℝ) < Real.sqrt (16 / 15) := by
    have h0 : Real.sqrt 1 < Real.sqrt (16 / 15) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using h0
  have := mul_lt_mul_of_pos_left h hc
  simpa using this

theorem ρ_mode3_start_le_ρStart₁ {c : ℝ} (hc : 0 ≤ c) :
    ρ_mode3_start c ≤ V64.TauWindowEndpoints.ρStart₁_sqrt c := by
  unfold ρ_mode3_start V64.TauWindowEndpoints.ρStart₁_sqrt
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by norm_num : (16 : ℝ) / 15 ≤ 9 / 8)) hc

end ProofRefinement.Korenblum.Candidates.V69.ThreeWindow
```

Next turn: `Numerical_Library/three_window_sqrt.py` (the rigorous `flint.arb` three-window wrapper at `c = 35656/100000`, reusing `rigorous_scalar`'s audited `_arb_exact` / `_pow_cached` / `_two_window_mass_window_lower_arb` helpers unchanged), then `lemma.toml` with the new oracle row and seed-axiom entries, then `Candidates/V69.lean`.