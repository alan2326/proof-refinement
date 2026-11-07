import KorenblumProofSearch3.ModePaperSideConditions
import KorenblumProofSearch3.ModeCertificateCore
import KorenblumProofSearch3.ConstantCertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace AffineBoxQ

theorem modeScalarIntegrand_nonneg
    (c : ℝ)
    {j : ℕ}
    (hj : 0 < j)
    (Λ : ℝ → ℝ)
    (hc : 0 < c)
    (hΛpos : 0 < Λ ρ)
    (hρc : c ≤ ρ) :
    0 ≤ ModeBridge.scalarIntegrand c j Λ ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le hc hρc
  unfold ModeBridge.scalarIntegrand OneModeKernel.term OneModeKernel.weight
  positivity

theorem mode_totalMass_le_intervalIntegral
    {j : ℕ}
    (hj : 0 < j)
    (c start stop : ℚ)
    (boxes : List AffineBoxQ)
    (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hInt : IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ)
      volume (start : ℝ) (stop : ℝ))
    (hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < Λ ρ)
    (hAffine : AffineLowerHolds boxes Λ) :
    (boxes.map fun b => modeMassR j c b).sum ≤
      ∫ ρ in (start : ℝ)..(stop : ℝ), ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ := by
  refine totalMass_le_intervalIntegral
    (f := fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ)
    (mass := fun b => modeMassR j c b)
    (start := start)
    (stop := stop)
    hstartstop boxes hOrd hHi hInt ?_ ?_
  · intro ρ hρ
    have hcstartR : (c : ℝ) ≤ (start : ℝ) := by exact_mod_cast hcstart
    exact modeScalarIntegrand_nonneg (c := (c : ℝ)) hj Λ hc (hΛpos ρ hρ)
      (le_trans hcstartR hρ.1)
  · intro box hMem
    have hcstartR : (c : ℝ) ≤ (start : ℝ) := by exact_mod_cast hcstart
    have hloQ : start ≤ box.lo := OrderedFrom.start_le_lo_of_mem hOrd hMem
    have hlohiQ : box.lo ≤ box.hi := OrderedFrom.lo_le_hi_of_mem hOrd hMem
    have hloR : (start : ℝ) ≤ box.loR := by simpa [loR] using hloQ
    have hlohiR : box.loR ≤ box.hiR := by simpa [loR, hiR] using hlohiQ
    have hhiQ : box.hi ≤ stop := hHi box hMem
    have hhiR : box.hiR ≤ (stop : ℝ) := by simpa [hiR] using hhiQ
    have hcbox : (c : ℝ) ≤ box.loR := le_trans hcstartR hloR
    have hSub : Set.uIcc box.loR box.hiR ⊆ Set.uIcc (start : ℝ) (stop : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le hloR (le_trans hlohiR hhiR)
      · exact Set.mem_uIcc_of_le (le_trans hloR hlohiR) hhiR
    have hIntBox : IntervalIntegrable
        (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ)
        volume box.loR box.hiR := hInt.mono_set hSub
    exact modeMassR_le_intervalIntegral hj c box Λ hc hcbox hlohiR hIntBox (hAffine box hMem)

end AffineBoxQ

namespace ConstantBoxQ

def modeTotalMassQ (j : ℕ) (c : ℚ) (boxes : List ConstantBoxQ) : ℚ :=
  (boxes.map fun b => AffineBoxQ.modeMassQ j c b.toAffine).sum

def modeTotalMass (j : ℕ) (c : ℚ) (boxes : List ConstantBoxQ) : ℝ :=
  (boxes.map fun b => AffineBoxQ.modeMassR j c b.toAffine).sum

theorem modeTotalMassQ_cast_eq_modeTotalMass
    (j : ℕ) (c : ℚ) (boxes : List ConstantBoxQ) :
    ((modeTotalMassQ j c boxes : ℚ) : ℝ) = modeTotalMass j c boxes := by
  induction boxes with
  | nil =>
      simp [modeTotalMassQ, modeTotalMass]
  | cons head tail ih =>
      simp [modeTotalMassQ, modeTotalMass, AffineBoxQ.modeMassQ_cast_eq_modeMassR]
      simpa [modeTotalMassQ, modeTotalMass] using ih

theorem modeTotalMass_le_intervalIntegral
    {j : ℕ}
    (hj : 0 < j)
    (c start stop : ℚ)
    (boxes : List ConstantBoxQ)
    (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hcstart : c ≤ start)
    (hstartstop : start ≤ stop)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hValid : Valid boxes)
    (hUpper : UpperHolds boxes Λ)
    (hΛpos : ∀ ρ ∈ Icc (start : ℝ) (stop : ℝ), 0 < Λ ρ)
    (hInt : IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ)
      volume (start : ℝ) (stop : ℝ)) :
    modeTotalMass j c boxes ≤
      ∫ ρ in (start : ℝ)..(stop : ℝ), ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ := by
  have hOrd' : AffineBoxQ.OrderedFrom start (boxes.map toAffine) := hOrd.toAffine
  have hHi' : ∀ box ∈ boxes.map toAffine, box.hi ≤ stop := hi_le_toAffine_of_hi_le hHi
  have hΛposBoxes : ∀ box ∈ boxes, ∀ ρ ∈ Icc box.loR box.hiR, 0 < Λ ρ := by
    intro box hMem ρ hρ
    have hlo : (start : ℝ) ≤ box.loR := by
      simpa [loR] using hOrd.start_le_lo_of_mem hMem
    have hhi : box.hiR ≤ (stop : ℝ) := by
      simpa [hiR] using hHi box hMem
    exact hΛpos ρ ⟨le_trans hlo hρ.1, le_trans hρ.2 hhi⟩
  have hAffine : AffineBoxQ.AffineLowerHolds (boxes.map toAffine) Λ :=
    affineLowerHolds_of_upperHolds hValid hUpper hΛposBoxes
  simpa [modeTotalMass] using
    (AffineBoxQ.mode_totalMass_le_intervalIntegral
      hj c start stop (boxes.map toAffine) Λ
      hc hcstart hstartstop hOrd' hHi' hInt hΛpos hAffine)

end ConstantBoxQ

end KorenblumProofSearch3
