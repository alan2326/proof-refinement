import KorenblumProofSearch3.ModeBridge

open scoped Topology
open Filter Finset MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace WangPaperSideConditions

theorem paperModeScalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ} {j : ℕ}
    (hc : 0 < c)
    (hj : 0 < j)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let μ := volume.restrict (Icc a b)
  have hΛmeas : AEMeasurable (fun ρ => WangOuter.paperLambda K c ρ) μ :=
    paperLambda_aemeasurableOn_Icc hca hb1 hPaperK
  have hTermMeas :
      AEMeasurable (fun ρ => OneModeKernel.term c ρ j) μ := by
    unfold OneModeKernel.term OneModeKernel.weight
    exact (measurable_id.aemeasurable.pow_const (2 * j)).const_div
      ((((j : ℝ) / (j + 1)) * c ^ (2 * j + 2)))
  have hMeas :
      AEStronglyMeasurable
        (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) μ := by
    have h :
        AEMeasurable
          (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ) μ := by
      unfold ModeBridge.scalarIntegrand
      exact (measurable_id.aemeasurable.const_mul (2 : ℝ)).div (hTermMeas.mul hΛmeas)
    exact h.aestronglyMeasurable
  refine IntegrableOn.of_bound ?_ hMeas (((4 : ℝ) * (j + 1) / j) / c ^ (2 * j + 2)) ?_
  · simpa using (measure_Icc_lt_top (μ := volume) (a := a) (b := b))
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun ρ hρ => by
      have hρnonneg : 0 ≤ ρ := le_trans hc.le (le_trans hca hρ.1)
      have hρle1 : ρ ≤ 1 := le_trans hρ.2 hb1
      have hρpow_le_one : ρ ^ (2 * j + 1) ≤ 1 := by
        exact pow_le_one₀ hρnonneg hρle1
      have hρpos : 0 < ρ := lt_of_lt_of_le hc (le_trans hca hρ.1)
      have hρne : ρ ≠ 0 := ne_of_gt hρpos
      have hΛhalf : (1 / 2 : ℝ) ≤ WangOuter.paperLambda K c ρ := paperLambda_ge_half
      have hΛpos : 0 < WangOuter.paperLambda K c ρ := paperLambda_pos
      have hcPowPos : 0 < c ^ (2 * j + 2) := by positivity
      have hDenPos : 0 < c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ := by positivity
      calc
        ‖ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ‖
            = (((2 : ℝ) * (j + 1) / j) * ρ ^ (2 * j + 1)) /
                (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ) := by
                  rw [ModeBridge.scalarIntegrand_eq (c := c) hj (WangOuter.paperLambda K c) hc hρne hΛpos.ne',
                    Real.norm_eq_abs,
                    abs_of_nonneg (div_nonneg (by positivity) hDenPos.le)]
        _ ≤ (((4 : ℝ) * (j + 1) / j) / c ^ (2 * j + 2)) := by
          apply (div_le_iff₀ hDenPos).2
          have hMain :
              (((2 : ℝ) * (j + 1) / j) * ρ ^ (2 * j + 1)) ≤
                (((4 : ℝ) * (j + 1) / j) * WangOuter.paperLambda K c ρ) := by
            let coeff : ℝ := ((2 : ℝ) * (j + 1) / j)
            have hCoeffNonneg : 0 ≤ ((2 : ℝ) * (j + 1) / j) := by positivity
            have hOne : (1 : ℝ) ≤ 2 * WangOuter.paperLambda K c ρ := by linarith
            have hPowLe : coeff * ρ ^ (2 * j + 1) ≤ coeff * 1 := by
              exact mul_le_mul_of_nonneg_left hρpow_le_one hCoeffNonneg
            have hΛLe : coeff * 1 ≤ coeff * (2 * WangOuter.paperLambda K c ρ) := by
              exact mul_le_mul_of_nonneg_left hOne hCoeffNonneg
            calc
              coeff * ρ ^ (2 * j + 1) ≤ coeff * 1 := hPowLe
              _ ≤ coeff * (2 * WangOuter.paperLambda K c ρ) := hΛLe
              _ = (((4 : ℝ) * (j + 1) / j) * WangOuter.paperLambda K c ρ) := by
                    dsimp [coeff]
                    ring
          have hRewrite :
              ((((4 : ℝ) * (j + 1) / j) / c ^ (2 * j + 2)) *
                (c ^ (2 * j + 2) * WangOuter.paperLambda K c ρ)) =
                  (((4 : ℝ) * (j + 1) / j) * WangOuter.paperLambda K c ρ) := by
            field_simp [hcPowPos.ne']
          rw [hRewrite]
          exact hMain

end WangPaperSideConditions

end KorenblumProofSearch3
