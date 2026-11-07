import KorenblumProofSearch3.AnnulusIntegralReduction
import KorenblumProofSearch3.WangModeCertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace WangBoxQ

theorem branch1TotalMassQ_cast_le_intervalIntegral
    (K : ℝ → ℝ → ℝ)
    (c stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstop : c ≤ stop)
    (hOrd : OrderedFrom c boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes)
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ)
    (hInt : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (c : ℝ) (stop : ℝ)) :
    (((totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
      ∫ ρ in (c : ℝ)..(stop : ℝ),
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
  have hOrdC : ConstantBoxQ.OrderedFrom c (boxes.map toConstant) := hOrd.toConstant
  have hHiC : ∀ box ∈ boxes.map toConstant, box.hi ≤ stop := hi_le_toConstant_of_hi_le hHi
  have hValidC : ConstantBoxQ.Valid (boxes.map toConstant) := toConstant_valid hValid
  have hUpper :
      ConstantBoxQ.UpperHolds (boxes.map toConstant) (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    toConstant_upperHolds hValid hKsq
  have hΛposBoxes :
      ∀ box ∈ boxes.map toConstant, ∀ ρ ∈ Icc box.loR box.hiR, 0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro box hMem ρ hρ
    rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
    have hlo : (c : ℝ) ≤ orig.loR := by
      simpa [loR] using hOrd.start_le_lo_of_mem hOrigMem
    have hhi : orig.hiR ≤ (stop : ℝ) := by
      simpa [hiR] using hHi orig hOrigMem
    exact hΛpos ρ ⟨le_trans hlo hρ.1, le_trans hρ.2 hhi⟩
  have hAffine :
      AffineBoxQ.AffineLowerHolds ((boxes.map toConstant).map ConstantBoxQ.toAffine)
        (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    ConstantBoxQ.affineLowerHolds_of_upperHolds hValidC hUpper hΛposBoxes
  have hBound :
      AffineBoxQ.totalMass Branch.one c ((boxes.map toConstant).map ConstantBoxQ.toAffine) ≤
        ∫ ρ in (c : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    exact AffineBoxQ.branch1_totalMass_le_intervalIntegral
      c stop ((boxes.map toConstant).map ConstantBoxQ.toAffine)
      (WangOuter.paperLambda K (c : ℝ))
      hc hcstop hOrdC.toAffine (ConstantBoxQ.hi_le_toAffine_of_hi_le hHiC) hInt hΛpos hAffine
  calc
    (((totalMassQ Branch.one c boxes : ℚ) : ℝ))
        = AffineBoxQ.totalMass Branch.one c ((boxes.map toConstant).map ConstantBoxQ.toAffine) := by
            simp [totalMassQ, ConstantBoxQ.totalMassQ, AffineBoxQ.totalMassQ_cast_eq_totalMass]
    _ ≤ ∫ ρ in (c : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := hBound

theorem branch1TotalMass_mul_le_annulusSlice
    (K : ℝ → ℝ → ℝ)
    (c stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstop : c ≤ stop)
    (hstop1 : (stop : ℝ) ≤ 1)
    (hOrd : OrderedFrom c boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes)
    (hMassNonneg : 0 ≤ (((totalMassQ Branch.one c boxes : ℚ) : ℝ)))
    (hPaperK : WangKernelExact.PaperKFormula K (c : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPointwise :
      ∀ ρ ∈ Icc (c : ℝ) (stop : ℝ),
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ * innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt : IntervalIntegrable
      (AnnulusIntegralReduction.annulusDensity circleGap)
      volume (c : ℝ) (stop : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (c : ℝ) (stop : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    (((totalMassQ Branch.one c boxes : ℚ) : ℝ) * innerExcess) ≤
      AnnulusIntegralReduction.annulusSlice circleGap (c : ℝ) (stop : ℝ) := by
  have hΛpos : ∀ ρ ∈ Icc (c : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro ρ hρ
    exact WangPaperSideConditions.paperLambda_pos (K := K) (c := (c : ℝ)) (ρ := ρ)
  have hInt : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (c : ℝ) (stop : ℝ) := by
    exact WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      (K := K) (c := (c : ℝ)) (a := (c : ℝ)) (b := (stop : ℝ))
      hc (by exact_mod_cast hcstop) le_rfl hstop1 hPaperK
  have hMass :
      (((totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
        ∫ ρ in (c : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    exact branch1TotalMassQ_cast_le_intervalIntegral
      K c stop boxes hc hcstop hOrd hHi hValid hKsq hΛpos hInt
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
    (a := (c : ℝ))
    (b := (stop : ℝ))
    (modeIntegrand := fun ρ =>
      Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
    (circleGap := circleGap)
    (mass := (((totalMassQ Branch.one c boxes : ℚ) : ℝ)))
    (by exact_mod_cast hcstop) hMassNonneg hMass hInt hAnnInt hPointwise hAnnNonneg

theorem branch1WindowTotalMassQ_cast_le_intervalIntegral
    (K : ℝ → ℝ → ℝ)
    (c start stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes)
    (hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ)
    (hInt : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (start : ℝ) (stop : ℝ)) :
    (((totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
      ∫ ρ in (start : ℝ)..(stop : ℝ),
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
  have hOrdC : ConstantBoxQ.OrderedFrom start (boxes.map toConstant) := hOrd.toConstant
  have hHiC : ∀ box ∈ boxes.map toConstant, box.hi ≤ stop := hi_le_toConstant_of_hi_le hHi
  have hValidC : ConstantBoxQ.Valid (boxes.map toConstant) := toConstant_valid hValid
  have hUpper :
      ConstantBoxQ.UpperHolds (boxes.map toConstant)
        (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    toConstant_upperHolds hValid hKsq
  have hΛposBoxes :
      ∀ box ∈ boxes.map toConstant, ∀ ρ ∈ Icc box.loR box.hiR,
        0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro box hMem ρ hρ
    rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
    have hlo : (start : ℝ) ≤ orig.loR := by
      simpa [loR] using hOrd.start_le_lo_of_mem hOrigMem
    have hhi : orig.hiR ≤ (stop : ℝ) := by
      simpa [hiR] using hHi orig hOrigMem
    exact hΛpos ρ ⟨le_trans hlo hρ.1, le_trans hρ.2 hhi⟩
  have hAffine :
      AffineBoxQ.AffineLowerHolds
        ((boxes.map toConstant).map ConstantBoxQ.toAffine)
        (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) :=
    ConstantBoxQ.affineLowerHolds_of_upperHolds hValidC hUpper hΛposBoxes
  have hBound :
      AffineBoxQ.totalMass Branch.one c
          ((boxes.map toConstant).map ConstantBoxQ.toAffine) ≤
        ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    unfold AffineBoxQ.totalMass
    refine AffineBoxQ.totalMass_le_intervalIntegral
      (f := fun ρ =>
        Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      (mass := fun b => b.massR Branch.one c)
      start stop hstartstop ((boxes.map toConstant).map ConstantBoxQ.toAffine)
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
    (((totalMassQ Branch.one c boxes : ℚ) : ℝ))
        = AffineBoxQ.totalMass Branch.one c
            ((boxes.map toConstant).map ConstantBoxQ.toAffine) := by
            simp [totalMassQ, ConstantBoxQ.totalMassQ,
              AffineBoxQ.totalMassQ_cast_eq_totalMass]
    _ ≤ ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := hBound

theorem branch1WindowTotalMass_mul_le_annulusSlice
    (K : ℝ → ℝ → ℝ)
    (c start stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hstop1 : (stop : ℝ) ≤ 1)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes)
    (hMassNonneg : 0 ≤ (((totalMassQ Branch.one c boxes : ℚ) : ℝ)))
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
    ((((totalMassQ Branch.one c boxes : ℚ) : ℝ)) * innerExcess) ≤
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
      (((totalMassQ Branch.one c boxes : ℚ) : ℝ)) ≤
        ∫ ρ in (start : ℝ)..(stop : ℝ),
          Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ := by
    exact branch1WindowTotalMassQ_cast_le_intervalIntegral
      K c start stop boxes hc hcstart hstartstop hOrd hHi hValid hKsq hΛpos hInt
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
    (a := (start : ℝ))
    (b := (stop : ℝ))
    (modeIntegrand := fun ρ =>
      Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
    (circleGap := circleGap)
    (mass := (((totalMassQ Branch.one c boxes : ℚ) : ℝ)))
    (by exact_mod_cast hstartstop) hMassNonneg hMass hInt hAnnInt hPointwise hAnnNonneg

theorem modeTotalMass_mul_le_annulusSlice
    {j : ℕ}
    (hj : 0 < j)
    (K : ℝ → ℝ → ℝ)
    (c start stop : ℚ)
    (boxes : List WangBoxQ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hstop1 : (stop : ℝ) ≤ 1)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes)
    (hMassNonneg : 0 ≤ modeTotalMass j c boxes)
    (hPaperK : WangKernelExact.PaperKFormula K (c : ℝ))
    {innerExcess : ℝ}
    {circleGap : ℝ → ℝ}
    (hPointwise :
      ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ),
        ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ * innerExcess ≤
          AnnulusIntegralReduction.annulusDensity circleGap ρ)
    (hAnnInt : IntervalIntegrable
      (AnnulusIntegralReduction.annulusDensity circleGap)
      volume (start : ℝ) (stop : ℝ))
    (hAnnNonneg :
      ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ),
        0 ≤ AnnulusIntegralReduction.annulusDensity circleGap ρ) :
    modeTotalMass j c boxes * innerExcess ≤
      AnnulusIntegralReduction.annulusSlice circleGap (start : ℝ) (stop : ℝ) := by
  have hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < WangOuter.paperLambda K (c : ℝ) ρ := by
    intro ρ hρ
    exact WangPaperSideConditions.paperLambda_pos (K := K) (c := (c : ℝ)) (ρ := ρ)
  have hIntMode : IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (start : ℝ) (stop : ℝ) := by
    exact WangPaperSideConditions.paperModeScalarIntegrand_intervalIntegrable
      (K := K) (c := (c : ℝ)) (a := (start : ℝ)) (b := (stop : ℝ))
      hc hj (by exact_mod_cast hstartstop) (by exact_mod_cast hcstart) hstop1 hPaperK
  have hMass :
      modeTotalMass j c boxes ≤
        ∫ ρ in (start : ℝ)..(stop : ℝ),
          ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ := by
    exact modeTotalMass_le_intervalIntegral
      hj K c start stop boxes hc hcstart hstartstop hOrd hHi hValid hKsq hΛpos hIntMode
  have hab : (start : ℝ) ≤ (stop : ℝ) := by
    exact_mod_cast hstartstop
  exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
    (a := (start : ℝ))
    (b := (stop : ℝ))
    (modeIntegrand := fun ρ =>
      ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ)
    (circleGap := circleGap)
    (mass := modeTotalMass j c boxes)
    hab hMassNonneg hMass hIntMode hAnnInt hPointwise hAnnNonneg

end WangBoxQ

end KorenblumProofSearch3
