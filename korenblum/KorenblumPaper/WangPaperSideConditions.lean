import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import KorenblumPaper.WangKernelExact

open scoped BigOperators Topology
open Filter Finset MeasureTheory Set

noncomputable section

namespace KorenblumPaper

namespace WangPaperSideConditions

theorem paperFactor_measurable (c : ℝ) (n : Nat) :
    Measurable (fun ρ : ℝ => WangKernelExact.paperFactor c ρ n) := by
  unfold WangKernelExact.paperFactor
  fun_prop

theorem paperTrunc_measurable (c : ℝ) (N : Nat) :
    Measurable (fun ρ : ℝ => WangKernelExact.paperTrunc c ρ N) := by
  have hProd : Measurable (fun ρ : ℝ => ∏ i ∈ range N, WangKernelExact.paperFactor c ρ i) := by
    exact Finset.measurable_fun_prod (range N) fun i _ => paperFactor_measurable c i
  have hBase : Measurable (fun ρ : ℝ => 2 * ρ * (1 + c / ρ ^ 2)) := by
    fun_prop
  simpa [WangKernelExact.paperTrunc] using hBase.mul hProd

theorem lambdaOfKSq_measurable : Measurable WangOuter.lambdaOfKSq := by
  unfold WangOuter.lambdaOfKSq
  fun_prop

theorem paperLambda_ge_half
    {K : ℝ → ℝ → ℝ} {c ρ : ℝ} :
    (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ := by
  unfold WangOuter.paperLambda WangOuter.lambdaOfKSq
  have hsqrt : 0 ≤ Real.sqrt ((1 + 3 * (K c ρ) ^ 2) / (1 - (K c ρ) ^ 2)) := Real.sqrt_nonneg _
  linarith

theorem paperLambda_pos
    {K : ℝ → ℝ → ℝ} {c ρ : ℝ} :
    0 < WangOuter.paperLambda K c ρ := by
  have hHalf := paperLambda_ge_half (K := K) (c := c) (ρ := ρ)
  linarith

theorem paperK_aemeasurableOn_Icc
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    AEMeasurable (fun ρ => K c ρ) (volume.restrict (Icc a b)) := by
  have hApprox : ∀ N, AEMeasurable (fun ρ => WangKernelExact.paperTrunc c ρ N)
      (volume.restrict (Icc a b)) := fun N => (paperTrunc_measurable c N).aemeasurable
  have hTendsto :
      ∀ᵐ ρ ∂volume.restrict (Icc a b),
        Tendsto (fun N => WangKernelExact.paperTrunc c ρ N) atTop (𝓝 (K c ρ)) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun ρ hρ => by
      have hρPaper : ρ ∈ Icc c 1 := ⟨le_trans hca hρ.1, le_trans hρ.2 hb1⟩
      rcases hPaperK ρ hρPaper with ⟨hmul, hEq⟩
      have hProd :
          Tendsto (fun N => ∏ i ∈ range N, WangKernelExact.paperFactor c ρ i) atTop
            (𝓝 (∏' n, WangKernelExact.paperFactor c ρ n)) :=
        hmul.tendsto_prod_tprod_nat
      have hMul :
          Tendsto
            (fun N => 2 * ρ * (1 + c / ρ ^ 2) *
              ∏ i ∈ range N, WangKernelExact.paperFactor c ρ i)
            atTop
            (𝓝 (2 * ρ * (1 + c / ρ ^ 2) * ∏' n, WangKernelExact.paperFactor c ρ n)) := by
        exact Tendsto.const_mul (2 * ρ * (1 + c / ρ ^ 2)) hProd
      simpa [WangKernelExact.paperTrunc, hEq] using hMul
  exact aemeasurable_of_tendsto_metrizable_ae' hApprox hTendsto

theorem paperLambda_aemeasurableOn_Icc
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    AEMeasurable (fun ρ => WangOuter.paperLambda K c ρ) (volume.restrict (Icc a b)) := by
  exact lambdaOfKSq_measurable.comp_aemeasurable
    ((paperK_aemeasurableOn_Icc hca hb1 hPaperK).pow_const 2)

theorem paperScalarIntegrand1_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let μ := volume.restrict (Icc a b)
  have hΛmeas : AEMeasurable (fun ρ => WangOuter.paperLambda K c ρ) μ :=
    paperLambda_aemeasurableOn_Icc hca hb1 hPaperK
  have hMeas :
      AEStronglyMeasurable
        (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) μ := by
    have h :
        AEMeasurable
          (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) μ := by
      unfold Korenblum.scalarIntegrand1
      exact (((measurable_id.aemeasurable.pow_const 3).const_mul 12).mul
          ((measurable_id.aemeasurable.pow_const 2).sub_const (c ^ 2))).div
        (hΛmeas.const_mul (c ^ 6))
    exact h.aestronglyMeasurable
  refine IntegrableOn.of_bound ?_ hMeas (24 / c ^ 6) ?_
  · simpa using (measure_Icc_lt_top (μ := volume) (a := a) (b := b))
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun ρ hρ => by
      have hρnonneg : 0 ≤ ρ := le_trans hc.le (le_trans hca hρ.1)
      have hρle1 : ρ ≤ 1 := le_trans hρ.2 hb1
      have hρsq_le_one : ρ ^ 2 ≤ 1 := by nlinarith
      have hc_sq_nonneg : 0 ≤ c ^ 2 := sq_nonneg c
      have hDiff_nonneg : 0 ≤ ρ ^ 2 - c ^ 2 := by
        have hc_le_ρ : c ≤ ρ := le_trans hca hρ.1
        nlinarith
      have hDiff_le_one : ρ ^ 2 - c ^ 2 ≤ 1 := by
        nlinarith
      have hNum_nonneg : 0 ≤ 12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2) := by positivity
      have hNum_le : 12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2) ≤ 12 := by
        have hρcube_le_one : ρ ^ 3 ≤ 1 := by
          nlinarith [hρsq_le_one, hρnonneg, hρle1]
        nlinarith
      have hΛhalf : (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ := paperLambda_ge_half
      have hΛpos : 0 < WangOuter.paperLambda K c ρ := paperLambda_pos
      have hc6pos : 0 < c ^ 6 := by positivity
      have hDen_pos : 0 < c ^ 6 * WangOuter.paperLambda K c ρ := by positivity
      calc
        ‖Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ‖
            = (12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2)) / (c ^ 6 * WangOuter.paperLambda K c ρ) := by
                rw [Korenblum.scalarIntegrand1, Real.norm_eq_abs,
                  abs_of_nonneg (div_nonneg hNum_nonneg hDen_pos.le)]
        _ ≤ 24 / c ^ 6 := by
          apply (div_le_iff₀ hDen_pos).2
          have hMain : 12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2) ≤ 24 * WangOuter.paperLambda K c ρ := by
            linarith
          have hRewrite : (24 / c ^ 6) * (c ^ 6 * WangOuter.paperLambda K c ρ) =
              24 * WangOuter.paperLambda K c ρ := by
            field_simp [hc6pos.ne']
          rw [hRewrite]
          exact hMain

theorem paperScalarIntegrand2_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let μ := volume.restrict (Icc a b)
  have hΛmeas : AEMeasurable (fun ρ => WangOuter.paperLambda K c ρ) μ :=
    paperLambda_aemeasurableOn_Icc hca hb1 hPaperK
  have hMeas :
      AEStronglyMeasurable
        (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) μ := by
    have h :
        AEMeasurable
          (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) μ := by
      unfold Korenblum.scalarIntegrand2
      exact ((measurable_id.aemeasurable.pow_const 3).const_mul 4).div
        (hΛmeas.const_mul (c ^ 4))
    exact h.aestronglyMeasurable
  refine IntegrableOn.of_bound ?_ hMeas (8 / c ^ 4) ?_
  · simpa using (measure_Icc_lt_top (μ := volume) (a := a) (b := b))
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun ρ hρ => by
      have hρnonneg : 0 ≤ ρ := le_trans hc.le (le_trans hca hρ.1)
      have hρle1 : ρ ≤ 1 := le_trans hρ.2 hb1
      have hNum_nonneg : 0 ≤ 4 * ρ ^ 3 := by positivity
      have hρsq_le_one : ρ ^ 2 ≤ 1 := by nlinarith
      have hNum_le : 4 * ρ ^ 3 ≤ 4 := by
        have hρcube_le_one : ρ ^ 3 ≤ 1 := by
          nlinarith [hρsq_le_one, hρnonneg, hρle1]
        nlinarith
      have hΛhalf : (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ := paperLambda_ge_half
      have hDen_pos : 0 < c ^ 4 * WangOuter.paperLambda K c ρ := by
        positivity [paperLambda_pos (K := K) (c := c) (ρ := ρ)]
      have hc4pos : 0 < c ^ 4 := by positivity
      calc
        ‖Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ‖
            = (4 * ρ ^ 3) / (c ^ 4 * WangOuter.paperLambda K c ρ) := by
                rw [Korenblum.scalarIntegrand2, Real.norm_eq_abs,
                  abs_of_nonneg (div_nonneg hNum_nonneg hDen_pos.le)]
        _ ≤ 8 / c ^ 4 := by
          apply (div_le_iff₀ hDen_pos).2
          have hMain : 4 * ρ ^ 3 ≤ 8 * WangOuter.paperLambda K c ρ := by
            linarith
          have hRewrite : (8 / c ^ 4) * (c ^ 4 * WangOuter.paperLambda K c ρ) =
              8 * WangOuter.paperLambda K c ρ := by
            field_simp [hc4pos.ne']
          rw [hRewrite]
          exact hMain

end WangPaperSideConditions

end KorenblumPaper
