import KorenblumProofSearch3.ModeConstantCertificateCore
import KorenblumProofSearch3.WangCertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace WangBoxQ

def modeTotalMassQ (j : ℕ) (c : ℚ) (boxes : List WangBoxQ) : ℚ :=
  ConstantBoxQ.modeTotalMassQ j c (boxes.map toConstant)

def modeTotalMass (j : ℕ) (c : ℚ) (boxes : List WangBoxQ) : ℝ :=
  ConstantBoxQ.modeTotalMass j c (boxes.map toConstant)

theorem modeTotalMassQ_cast_eq_modeTotalMass
    (j : ℕ) (c : ℚ) (boxes : List WangBoxQ) :
    ((modeTotalMassQ j c boxes : ℚ) : ℝ) = modeTotalMass j c boxes := by
  simpa [modeTotalMassQ, modeTotalMass] using
    (ConstantBoxQ.modeTotalMassQ_cast_eq_modeTotalMass j c (boxes.map toConstant))

theorem modeTotalMass_le_intervalIntegral
    {j : ℕ}
    (hj : 0 < j)
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
      (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (start : ℝ) (stop : ℝ)) :
    modeTotalMass j c boxes ≤
      ∫ ρ in (start : ℝ)..(stop : ℝ),
        ModeBridge.scalarIntegrand (c : ℝ) j (WangOuter.paperLambda K (c : ℝ)) ρ := by
  simpa [modeTotalMass] using
    (ConstantBoxQ.modeTotalMass_le_intervalIntegral
      hj c start stop (boxes.map toConstant) (WangOuter.paperLambda K (c : ℝ))
      hc hcstart hstartstop hOrd.toConstant (hi_le_toConstant_of_hi_le hHi)
      (toConstant_valid hValid) (toConstant_upperHolds hValid hKsq) hΛpos hInt)

end WangBoxQ

end KorenblumProofSearch3
