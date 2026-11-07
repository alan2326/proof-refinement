import KorenblumPaper.CertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumPaper

structure ConstantBoxQ where
  lo : ℚ
  hi : ℚ
  alpha : ℚ
  lambdaUpper : ℚ
deriving DecidableEq, Repr

namespace ConstantBoxQ

def loR (b : ConstantBoxQ) : ℝ := b.lo

def hiR (b : ConstantBoxQ) : ℝ := b.hi

def alphaR (b : ConstantBoxQ) : ℝ := b.alpha

def lambdaUpperR (b : ConstantBoxQ) : ℝ := b.lambdaUpper

def toAffine (b : ConstantBoxQ) : AffineBoxQ :=
  { lo := b.lo, hi := b.hi, alpha := b.alpha, beta := 0 }

def totalMassQ (branch : Branch) (c : ℚ) (boxes : List ConstantBoxQ) : ℚ :=
  AffineBoxQ.totalMassQ branch c (boxes.map toAffine)

def OrderedFrom (start : ℚ) : List ConstantBoxQ → Prop
  | [] => True
  | b :: bs => start ≤ b.lo ∧ b.lo ≤ b.hi ∧ OrderedFrom b.hi bs

instance instDecidableOrderedFrom (start : ℚ) (boxes : List ConstantBoxQ) :
    Decidable (OrderedFrom start boxes) := by
  induction boxes generalizing start with
  | nil =>
      exact isTrue trivial
  | cons head tail ih =>
      dsimp [OrderedFrom]
      letI : Decidable (OrderedFrom head.hi tail) := ih head.hi
      infer_instance

def Valid (boxes : List ConstantBoxQ) : Prop :=
  ∀ box ∈ boxes, 0 ≤ box.alpha ∧ 0 < box.lambdaUpper ∧ box.alpha * box.lambdaUpper ≤ 1

def UpperHolds (boxes : List ConstantBoxQ) (Λ : ℝ → ℝ) : Prop :=
  ∀ box ∈ boxes, ∀ ρ ∈ Icc box.loR box.hiR, Λ ρ ≤ box.lambdaUpperR

instance instDecidableValid (boxes : List ConstantBoxQ) : Decidable (Valid boxes) := by
  unfold Valid
  infer_instance

theorem OrderedFrom.lo_le_hi_of_mem
    {start : ℚ} {boxes : List ConstantBoxQ} (hOrd : OrderedFrom start boxes) :
    ∀ {box : ConstantBoxQ}, box ∈ boxes → box.lo ≤ box.hi := by
  induction boxes generalizing start with
  | nil =>
      intro box hMem
      cases hMem
  | cons head tail ih =>
      intro box hMem
      rcases hOrd with ⟨_, hhead, htail⟩
      simp at hMem
      rcases hMem with rfl | hMem
      · exact hhead
      · exact ih htail hMem

theorem OrderedFrom.start_le_lo_of_mem
    {start : ℚ} {boxes : List ConstantBoxQ} (hOrd : OrderedFrom start boxes) :
    ∀ {box : ConstantBoxQ}, box ∈ boxes → start ≤ box.lo := by
  induction boxes generalizing start with
  | nil =>
      intro box hMem
      cases hMem
  | cons head tail ih =>
      intro box hMem
      rcases hOrd with ⟨hstart, hlohi, htail⟩
      simp at hMem
      rcases hMem with rfl | hMem
      · exact hstart
      · exact le_trans (le_trans hstart hlohi) (ih htail hMem)

theorem OrderedFrom.toAffine
    {start : ℚ} {boxes : List ConstantBoxQ} (hOrd : OrderedFrom start boxes) :
    AffineBoxQ.OrderedFrom start (boxes.map toAffine) := by
  induction boxes generalizing start with
  | nil =>
      simp [AffineBoxQ.OrderedFrom]
  | cons head tail ih =>
      rcases hOrd with ⟨hstart, hlohi, htail⟩
      exact ⟨by simpa [toAffine] using hstart, by simpa [toAffine] using hlohi, ih htail⟩

theorem hi_le_toAffine_of_hi_le
    {stop : ℚ} {boxes : List ConstantBoxQ}
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop) :
    ∀ box ∈ boxes.map toAffine, box.hi ≤ stop := by
  intro box hMem
  rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
  exact hHi orig hOrigMem

theorem affineLowerHolds_of_upperHolds
    {boxes : List ConstantBoxQ} {Λ : ℝ → ℝ}
    (hValid : Valid boxes)
    (hUpper : UpperHolds boxes Λ)
    (hΛpos : ∀ box ∈ boxes, ∀ ρ ∈ Icc box.loR box.hiR, 0 < Λ ρ) :
    AffineBoxQ.AffineLowerHolds (boxes.map toAffine) Λ := by
  intro box hMem ρ hρ
  rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
  rcases hValid orig hOrigMem with ⟨hAlpha, _, hProd⟩
  have hAlphaR : 0 ≤ orig.alphaR := by
    simpa [alphaR] using (show (0 : ℝ) ≤ (orig.alpha : ℝ) from by exact_mod_cast hAlpha)
  have hMul : orig.alphaR * Λ ρ ≤ 1 := by
    have hMulUpper :
        orig.alphaR * Λ ρ ≤ orig.alphaR * orig.lambdaUpperR := by
      exact mul_le_mul_of_nonneg_left (hUpper orig hOrigMem ρ hρ) hAlphaR
    exact hMulUpper.trans (by
      simpa [alphaR, lambdaUpperR] using
        (show ((orig.alpha * orig.lambdaUpper : ℚ) : ℝ) ≤ (1 : ℝ) from by
          exact_mod_cast hProd))
  have hInv : orig.alphaR ≤ (Λ ρ)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ (hΛpos orig hOrigMem ρ hρ)).2 (by simpa using hMul)
  simpa [toAffine, AffineBoxQ.lowerAffine, AffineBoxQ.alphaR, AffineBoxQ.betaR]
    using hInv

theorem totalMassQ_pair_le_scalarCriterion
    (c splitLo splitHi oneCut : ℚ)
    (boxes1 boxes2 : List ConstantBoxQ)
    (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hc1 : (c : ℝ) < 1)
    (hcsplit : c ≤ splitLo)
    (hSplitLoSq : 3 * splitLo ^ 2 ≤ 4 * c ^ 2)
    (hSplitHiNonneg : 0 ≤ (splitHi : ℝ))
    (hSplitHiSq : 4 * c ^ 2 ≤ 3 * splitHi ^ 2)
    (hSplitHiCut : splitHi ≤ oneCut)
    (hOneCutLeOne : oneCut ≤ 1)
    (hOrd1 : OrderedFrom c boxes1)
    (hHi1 : ∀ box ∈ boxes1, box.hi ≤ splitLo)
    (hOrd2 : OrderedFrom splitHi boxes2)
    (hHi2 : ∀ box ∈ boxes2, box.hi ≤ oneCut)
    (hValid1 : Valid boxes1)
    (hValid2 : Valid boxes2)
    (hUpper1 : UpperHolds boxes1 Λ)
    (hUpper2 : UpperHolds boxes2 Λ)
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) 1, 0 < Λ ρ)
    (hInt1 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ)
      volume (c : ℝ) (AffineBoxQ.branchEndR c .one))
    (hInt2 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ)
      volume (AffineBoxQ.branchEndR c .one) 1) :
    (((totalMassQ .one c boxes1 + totalMassQ .two c boxes2 : ℚ) : ℝ)) ≤
      Korenblum.scalarCriterion (c : ℝ) Λ := by
  let split : ℝ := AffineBoxQ.branchEndR c .one
  have hcNonneg : 0 ≤ (c : ℝ) := le_of_lt hc
  have hSplitLoLe : (splitLo : ℝ) ≤ split := by
    simpa [split] using AffineBoxQ.le_branchOneEnd_of_sq (c := c) (splitLo := splitLo)
      hcNonneg (le_trans hc.le (by exact_mod_cast hcsplit)) hSplitLoSq
  have hSplitLeHi : split ≤ (splitHi : ℝ) := by
    simpa [split] using AffineBoxQ.branchOneEnd_le_of_sq (c := c) (splitHi := splitHi)
      hcNonneg hSplitHiNonneg hSplitHiSq
  have hSplitLoLeOne : (splitLo : ℝ) ≤ (1 : ℝ) := by
    exact le_trans hSplitLoLe <| le_trans hSplitLeHi <|
      le_trans (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut)
        (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne)
  have hCLeSplitHi : (c : ℝ) ≤ (splitHi : ℝ) := by
    exact le_trans (show (c : ℝ) ≤ (splitLo : ℝ) by exact_mod_cast hcsplit) (le_trans hSplitLoLe hSplitLeHi)
  have hOrd1' : AffineBoxQ.OrderedFrom c (boxes1.map toAffine) := hOrd1.toAffine
  have hOrd2' : AffineBoxQ.OrderedFrom splitHi (boxes2.map toAffine) := hOrd2.toAffine
  have hHi1' : ∀ box ∈ boxes1.map toAffine, box.hi ≤ splitLo := hi_le_toAffine_of_hi_le hHi1
  have hHi2' : ∀ box ∈ boxes2.map toAffine, box.hi ≤ oneCut := hi_le_toAffine_of_hi_le hHi2
  have hΛpos1 : ∀ box ∈ boxes1, ∀ ρ ∈ Icc box.loR box.hiR, 0 < Λ ρ := by
    intro box hMem ρ hρ
    have hlo : (c : ℝ) ≤ box.loR := by
      simpa [loR] using hOrd1.start_le_lo_of_mem hMem
    have hhi : box.hiR ≤ (splitLo : ℝ) := by
      simpa [hiR] using hHi1 box hMem
    exact hΛpos ρ ⟨le_trans hlo hρ.1, le_trans hρ.2 (le_trans hhi hSplitLoLeOne)⟩
  have hΛpos2 : ∀ box ∈ boxes2, ∀ ρ ∈ Icc box.loR box.hiR, 0 < Λ ρ := by
    intro box hMem ρ hρ
    have hlo : (splitHi : ℝ) ≤ box.loR := by
      simpa [loR] using hOrd2.start_le_lo_of_mem hMem
    have hhi : box.hiR ≤ (oneCut : ℝ) := by
      simpa [hiR] using hHi2 box hMem
    exact hΛpos ρ ⟨le_trans hCLeSplitHi (le_trans hlo hρ.1), le_trans hρ.2 (le_trans hhi (by exact_mod_cast hOneCutLeOne))⟩
  have hAffine1 : AffineBoxQ.AffineLowerHolds (boxes1.map toAffine) Λ :=
    affineLowerHolds_of_upperHolds hValid1 hUpper1 hΛpos1
  have hAffine2 : AffineBoxQ.AffineLowerHolds (boxes2.map toAffine) Λ :=
    affineLowerHolds_of_upperHolds hValid2 hUpper2 hΛpos2
  simpa [totalMassQ] using
    (AffineBoxQ.totalMassQ_pair_le_scalarCriterion
      c splitLo splitHi oneCut (boxes1.map toAffine) (boxes2.map toAffine) Λ
      hc hc1 hcsplit hSplitLoSq hSplitHiNonneg hSplitHiSq hSplitHiCut hOneCutLeOne
      hOrd1' hHi1' hOrd2' hHi2' hAffine1 hAffine2 hΛpos hInt1 hInt2)

end ConstantBoxQ

end KorenblumPaper
