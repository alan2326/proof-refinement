import KorenblumProofSearch3.Candidates.V38.Data

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3.V38

open KorenblumProofSearch3


private theorem branch1WindowMassQ_cast_le_intervalIntegral
    (K : ℝ → ℝ → ℝ)
    (c start stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hOrd : WangBoxQ.OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : WangBoxQ.Valid boxes)
    (hKsq : WangBoxQ.KSqUpperHolds K c boxes)
    (hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ)
    (hInt :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
        volume (start : ℝ) (stop : ℝ)) :
    (((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
      ∫ ρ in (start : ℝ)..(stop : ℝ),
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
  have hOrdC : ConstantBoxQ.OrderedFrom start (boxes.map WangBoxQ.toConstant) := hOrd.toConstant
  have hHiC : ∀ box ∈ boxes.map WangBoxQ.toConstant, box.hi ≤ stop :=
    WangBoxQ.hi_le_toConstant_of_hi_le hHi
  have hValidC : ConstantBoxQ.Valid (boxes.map WangBoxQ.toConstant) := WangBoxQ.toConstant_valid hValid
  have hUpper :
      ConstantBoxQ.UpperHolds (boxes.map WangBoxQ.toConstant)
        (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    WangBoxQ.toConstant_upperHolds hValid hKsq
  have hΛposBoxes :
      ∀ box ∈ boxes.map WangBoxQ.toConstant, ∀ ρ ∈ Icc box.loR box.hiR,
        0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro box hMem ρ hρ
    rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
    have hlo : (start : ℝ) ≤ orig.loR := by
      simpa [WangBoxQ.loR] using hOrd.start_le_lo_of_mem hOrigMem
    have hhi : orig.hiR ≤ (stop : ℝ) := by
      simpa [WangBoxQ.hiR] using hHi orig hOrigMem
    exact hΛpos ρ ⟨le_trans hlo hρ.1, le_trans hρ.2 hhi⟩
  have hAffine :
      AffineBoxQ.AffineLowerHolds
        ((boxes.map WangBoxQ.toConstant).map ConstantBoxQ.toAffine)
        (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    ConstantBoxQ.affineLowerHolds_of_upperHolds hValidC hUpper hΛposBoxes
  have hBound :
      AffineBoxQ.totalMass Branch.one c
          ((boxes.map WangBoxQ.toConstant).map ConstantBoxQ.toAffine) ≤
        ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    unfold AffineBoxQ.totalMass
    refine AffineBoxQ.totalMass_le_intervalIntegral
      (f := fun ρ =>
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      (mass := fun b => b.massR Branch.one c)
      start stop hstartstop ((boxes.map WangBoxQ.toConstant).map ConstantBoxQ.toAffine)
      hOrdC.toAffine (ConstantBoxQ.hi_le_toAffine_of_hi_le hHiC) hInt ?_ ?_
    · intro ρ hρ
      exact AffineBoxQ.scalarIntegrand1_nonneg
        (c := (c : ℝ))
        (Λ := WangOuter.paperLambda K (c : ℝ))
        hc (hΛpos ρ hρ) (le_trans (by exact_mod_cast hcstart) hρ.1)
    · intro box hMem
      rcases List.mem_map.1 hMem with ⟨constBox, hConstMem, rfl⟩
      have hloStart : (start : ℝ) ≤ constBox.loR := by
        simpa [ConstantBoxQ.loR] using hOrdC.start_le_lo_of_mem hConstMem
      have hlo : (c : ℝ) ≤ constBox.loR := by
        exact le_trans (by exact_mod_cast hcstart) hloStart
      have hlohi : constBox.loR ≤ constBox.hiR := by
        simpa [ConstantBoxQ.loR, ConstantBoxQ.hiR] using hOrdC.lo_le_hi_of_mem hConstMem
      have hhi : constBox.hiR ≤ (stop : ℝ) := by
        simpa [ConstantBoxQ.hiR] using hHiC constBox hConstMem
      have hSub : Set.uIcc constBox.loR constBox.hiR ⊆ Set.uIcc (start : ℝ) (stop : ℝ) := by
        apply Set.uIcc_subset_uIcc
        · exact Set.mem_uIcc_of_le hloStart (le_trans hlohi hhi)
        · exact Set.mem_uIcc_of_le (le_trans hloStart hlohi) hhi
      have hIntBox :
          IntervalIntegrable
            (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
            volume constBox.loR constBox.hiR := hInt.mono_set hSub
      exact AffineBoxQ.massR_branch1_le_intervalIntegral c constBox.toAffine
        (WangOuter.paperLambda K (c : ℝ)) hc hlo
        (by simpa using hlohi) hIntBox (hAffine _ hMem)
  calc
    (((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ))
        = AffineBoxQ.totalMass Branch.one c
            ((boxes.map WangBoxQ.toConstant).map ConstantBoxQ.toAffine) := by
            simp [WangBoxQ.totalMassQ, ConstantBoxQ.totalMassQ,
              AffineBoxQ.totalMassQ_cast_eq_totalMass]
    _ ≤ ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := hBound

private theorem branch1WindowMass_mul_le_slice
    (K : ℝ → ℝ → ℝ)
    (c start stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hstop1 : (stop : ℝ) ≤ 1)
    (hOrd : WangBoxQ.OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : WangBoxQ.Valid boxes)
    (hKsq : WangBoxQ.KSqUpperHolds K c boxes)
    (hMassNonneg : 0 ≤ (((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ)))
    (hPaperK : WangKernelExact.PaperKFormula K (c : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPointwise :
      ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ),
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ * innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (start : ℝ) (stop : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    ((((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ)) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (start : ℝ) (stop : ℝ) := by
  have hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro ρ hρ
    exact WangPaperSideConditions.paperLambda_pos (K := K) (c := (c : ℝ)) (ρ := ρ)
  have hInt :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
        volume (start : ℝ) (stop : ℝ) := by
    exact WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      (K := K) (c := (c : ℝ)) (a := (start : ℝ)) (b := (stop : ℝ))
      hc (by exact_mod_cast hstartstop) (by exact_mod_cast hcstart) hstop1 hPaperK
  have hMass :
      (((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
        ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    exact branch1WindowMassQ_cast_le_intervalIntegral
      K c start stop boxes hc hcstart hstartstop hOrd hHi hValid hKsq hΛpos hInt
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
    (a := (start : ℝ)) (b := (stop : ℝ))
    (modeIntegrand := fun ρ =>
      Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
    (circleGap := circleGap)
    (mass := (((WangBoxQ.totalMassQ Branch.one c boxes : ℚ) : ℝ)))
    (by exact_mod_cast hstartstop) hMassNonneg hMass hInt hAnnInt hPointwise hAnnNonneg

theorem hybridTotalMass_ge_one : (1 : ℝ) ≤ (hybridTotalMassQ : ℝ) := by
  exact_mod_cast hybridTotalMassQ_ge_one

theorem fallbackA_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (cValueQ : ℝ) (fallbackAStopQ : ℝ),
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (cValueQ : ℝ) (fallbackAStopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (cValueQ : ℝ) (fallbackAStopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    ((((WangBoxQ.totalMassQ Branch.one cValueQ fallbackABoxes : ℚ) : ℝ)) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (cValueQ : ℝ) (fallbackAStopQ : ℝ) := by
  exact WangBoxQ.branch1TotalMass_mul_le_annulusSlice
    K cValueQ fallbackAStopQ fallbackABoxes
    cValue_pos c_le_fallbackAStop
    (show (fallbackAStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackAStop_le_one)
    fallbackABoxes_ordered fallbackABoxes_hi_le fallbackABoxes_valid
    (fallbackABoxes_kSqUpper (K := K) (a := a) (b := b) paper)
    fallbackA_mass_nonneg paper.eq7_paperK_formula
    hPoint hAnnInt hAnnNonneg

theorem mode4_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (mode4StartQ : ℝ) (mode4StopQ : ℝ),
        ModeBridge.scalarIntegrand (cValueQ : ℝ) 4 (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode4StartQ : ℝ) (mode4StopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (mode4StartQ : ℝ) (mode4StopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    WangBoxQ.modeTotalMass 4 cValueQ mode4Boxes * innerExcess ≤
      AnnulusIntegralReduction.annulusSlice circleGap (mode4StartQ : ℝ) (mode4StopQ : ℝ) := by
  exact WangBoxQ.modeTotalMass_mul_le_annulusSlice
    (j := 4) (by norm_num) K cValueQ mode4StartQ mode4StopQ mode4Boxes
    cValue_pos c_le_mode4Start mode4Start_le_mode4Stop
    (show (mode4StopQ : ℝ) ≤ 1 by exact_mod_cast mode4Stop_le_one)
    mode4Boxes_ordered mode4Boxes_hi_le mode4Boxes_valid
    (mode4Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
    mode4_mass_nonneg paper.eq7_paperK_formula
    hPoint hAnnInt hAnnNonneg

theorem fallbackB_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ),
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    ((((WangBoxQ.totalMassQ Branch.one cValueQ fallbackBBox : ℚ) : ℝ)) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (fallbackBStartQ : ℝ) (fallbackBStopQ : ℝ) := by
  exact branch1WindowMass_mul_le_slice
    K cValueQ fallbackBStartQ fallbackBStopQ fallbackBBox
    cValue_pos c_le_fallbackBStart fallbackBStart_le_fallbackBStop
    (show (fallbackBStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackBStop_le_one)
    fallbackBBox_ordered fallbackBBox_hi_le fallbackBBox_valid
    (fallbackBBox_kSqUpper (K := K) (a := a) (b := b) paper) fallbackB_mass_nonneg
    paper.eq7_paperK_formula hPoint hAnnInt hAnnNonneg

theorem mode3_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (mode3StartQ : ℝ) (mode3StopQ : ℝ),
        ModeBridge.scalarIntegrand (cValueQ : ℝ) 3 (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode3StartQ : ℝ) (mode3StopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (mode3StartQ : ℝ) (mode3StopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    WangBoxQ.modeTotalMass 3 cValueQ mode3Boxes * innerExcess ≤
      AnnulusIntegralReduction.annulusSlice circleGap (mode3StartQ : ℝ) (mode3StopQ : ℝ) := by
  exact WangBoxQ.modeTotalMass_mul_le_annulusSlice
    (j := 3) (by norm_num) K cValueQ mode3StartQ mode3StopQ mode3Boxes
    cValue_pos c_le_mode3Start mode3Start_le_mode3Stop
    (show (mode3StopQ : ℝ) ≤ 1 by exact_mod_cast mode3Stop_le_one)
    mode3Boxes_ordered mode3Boxes_hi_le mode3Boxes_valid
    (mode3Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
    mode3_mass_nonneg paper.eq7_paperK_formula
    hPoint hAnnInt hAnnNonneg

theorem fallbackC_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ),
        Korenblum.scalarIntegrand1 (cValueQ : ℝ) (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    ((((WangBoxQ.totalMassQ Branch.one cValueQ fallbackCBox : ℚ) : ℝ)) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (fallbackCStartQ : ℝ) (fallbackCStopQ : ℝ) := by
  exact branch1WindowMass_mul_le_slice
    K cValueQ fallbackCStartQ fallbackCStopQ fallbackCBox
    cValue_pos c_le_fallbackCStart fallbackCStart_le_fallbackCStop
    (show (fallbackCStopQ : ℝ) ≤ 1 by exact_mod_cast fallbackCStop_le_one)
    fallbackCBox_ordered fallbackCBox_hi_le fallbackCBox_valid
    (fallbackCBox_kSqUpper (K := K) (a := a) (b := b) paper) fallbackC_mass_nonneg
    paper.eq7_paperK_formula hPoint hAnnInt hAnnNonneg

theorem mode2_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (mode2StartQ : ℝ) (mode2StopQ : ℝ),
        ModeBridge.scalarIntegrand (cValueQ : ℝ) 2 (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode2StartQ : ℝ) (mode2StopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (mode2StartQ : ℝ) (mode2StopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    WangBoxQ.modeTotalMass 2 cValueQ mode2Boxes * innerExcess ≤
      AnnulusIntegralReduction.annulusSlice circleGap (mode2StartQ : ℝ) (mode2StopQ : ℝ) := by
  exact WangBoxQ.modeTotalMass_mul_le_annulusSlice
    (j := 2) (by norm_num) K cValueQ mode2StartQ mode2StopQ mode2Boxes
    cValue_pos c_le_mode2Start mode2Start_le_mode2Stop
    (show (mode2StopQ : ℝ) ≤ 1 by exact_mod_cast mode2Stop_le_one)
    mode2Boxes_ordered mode2Boxes_hi_le mode2Boxes_valid
    (mode2Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
    mode2_mass_nonneg paper.eq7_paperK_formula
    hPoint hAnnInt hAnnNonneg

theorem mode1_mass_mul_le_slice
    {K : ℝ → ℝ → ℝ}
    {a b : ℕ → ℂ}
    (paper : PaperAxioms.Section2Assumptions a b K (cValueQ : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPoint :
      ∀ ρ ∈ Icc (mode1StartQ : ℝ) (mode1StopQ : ℝ),
        ModeBridge.scalarIntegrand (cValueQ : ℝ) 1 (WangOuter.paperLambda K (cValueQ : ℝ)) ρ *
            innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt :
      IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
        volume (mode1StartQ : ℝ) (mode1StopQ : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (mode1StartQ : ℝ) (mode1StopQ : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    WangBoxQ.modeTotalMass 1 cValueQ mode1Boxes * innerExcess ≤
      AnnulusIntegralReduction.annulusSlice circleGap (mode1StartQ : ℝ) (mode1StopQ : ℝ) := by
  exact WangBoxQ.modeTotalMass_mul_le_annulusSlice
    (j := 1) (by norm_num) K cValueQ mode1StartQ mode1StopQ mode1Boxes
    cValue_pos c_le_mode1Start mode1Start_le_mode1Stop
    (show (mode1StopQ : ℝ) ≤ 1 by exact_mod_cast mode1Stop_le_one)
    (by simpa [mode1StartQ, mode1Boxes] using branch2Boxes_ordered)
    mode1Boxes_hi_le mode1Boxes_valid
    (mode1Boxes_kSqUpper (K := K) (a := a) (b := b) paper)
    mode1_mass_nonneg paper.eq7_paperK_formula
    hPoint hAnnInt hAnnNonneg

end KorenblumProofSearch3.V38
