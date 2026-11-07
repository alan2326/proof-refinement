import KorenblumProofSearch3.AnnulusIntegralReduction
import KorenblumProofSearch3.OneModePaperBridge
import KorenblumProofSearch3.PaperAxioms
import KorenblumProofSearch3.WangKernelExact

open MeasureTheory

noncomputable section

namespace KorenblumProofSearch3.EvaluatorFixture

def cValueQ : ℚ := 0

theorem direct_disk_vs_annulus
    (K : ℝ → ℝ → ℝ)
    {a b : ℕ → ℂ}
    (paper : KorenblumProofSearch3.PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    (hPlusSigma :
      Summable
        (fun n : ℕ =>
          KorenblumProofSearch3.OneModePaperBridge.plusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigmaC :
      Summable
        (fun n : ℕ =>
          KorenblumProofSearch3.OneModePaperBridge.minusSeq a b n * (cValueQ : ℝ) ^ (2 * n)))
    (hMinusSigma :
      ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < 1 →
        Summable
          (fun n : ℕ => KorenblumProofSearch3.OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
    (hAnnInt :
      IntervalIntegrable
        (KorenblumProofSearch3.AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (cValueQ : ℝ) (1 : ℝ)) :
    KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap 0 (cValueQ : ℝ) ≤
      KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap (cValueQ : ℝ)
        (1 : ℝ) := by
  have hZero :
      KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap 0 (cValueQ : ℝ) =
        0 := by
    simp [KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice, cValueQ]
  have hRightNonneg :
      0 ≤
        KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap (cValueQ : ℝ)
          (1 : ℝ) := by
    have hRightNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (cValueQ : ℝ) (1 : ℝ)),
          0 ≤ KorenblumProofSearch3.AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo (cValueQ : ℝ) (1 : ℝ)),
            0 ≤ KorenblumProofSearch3.AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun ρ hρ => by
          have hCircleNonneg :
              0 ≤ paper.circleGap ρ :=
            KorenblumProofSearch3.OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper
              (by simpa [cValueQ] using hρ.1) hρ.2
          change 0 ≤ 2 * ρ * paper.circleGap ρ
          have hρpos : 0 < ρ := by simpa [cValueQ] using hρ.1
          nlinarith
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    simpa [cValueQ] using
      KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
        (circleGap := paper.circleGap)
        (a := (cValueQ : ℝ))
        (b := (1 : ℝ))
        (by norm_num [cValueQ])
        hRightNonnegAE
  rw [hZero]
  exact hRightNonneg

end KorenblumProofSearch3.EvaluatorFixture
