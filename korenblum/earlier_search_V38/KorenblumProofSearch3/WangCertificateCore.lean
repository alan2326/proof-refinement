import KorenblumProofSearch3.ConstantCertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace WangOuter

/-- The outer-control factor from equation (9), written as a function of `K^2`. -/
def lambdaOfKSq (s : ℝ) : ℝ :=
  (1 + Real.sqrt ((1 + 3 * s) / (1 - s))) / 2

/-- Wang's `Lambda(rho) = 1 + gamma_2(rho)` written using equation (9). -/
def paperLambda (K : ℝ → ℝ → ℝ) (c ρ : ℝ) : ℝ :=
  lambdaOfKSq ((K c ρ) ^ 2)

/-- Rational certificate that `lambdaUpper` dominates the paper formula coming
from a `K^2` upper bound `kSqUpper`. This is exactly the algebraic inequality
obtained by squaring the equation (9) expression. -/
def lambdaUpperWitnessQ (kSqUpper lambdaUpper : ℚ) : Prop :=
  0 ≤ kSqUpper ∧
  kSqUpper < 1 ∧
  0 ≤ 2 * lambdaUpper - 1 ∧
  1 + 3 * kSqUpper ≤ (2 * lambdaUpper - 1) ^ 2 * (1 - kSqUpper)

theorem lambdaUpperWitnessQ.lambdaUpper_pos
    {kSqUpper lambdaUpper : ℚ}
    (h : lambdaUpperWitnessQ kSqUpper lambdaUpper) :
    0 < lambdaUpper := by
  rcases h with ⟨_, _, hHalf, _⟩
  linarith

theorem frac_mono
    {x y : ℝ}
    (hxy : x ≤ y)
    (hy1 : y < 1) :
    (1 + 3 * x) / (1 - x) ≤ (1 + 3 * y) / (1 - y) := by
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hxden : 0 < 1 - x := sub_pos.mpr hx1
  have hyden : 0 < 1 - y := sub_pos.mpr hy1
  have hDiff :
      (1 + 3 * x) / (1 - x) - (1 + 3 * y) / (1 - y) ≤ 0 := by
    field_simp [hxden.ne', hyden.ne']
    nlinarith
  linarith

theorem lambdaOfKSq_mono
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y)
    (hy1 : y < 1) :
    lambdaOfKSq x ≤ lambdaOfKSq y := by
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hxden : 0 < 1 - x := sub_pos.mpr hx1
  have hyden : 0 < 1 - y := sub_pos.mpr hy1
  have hNumX : 0 ≤ 1 + 3 * x := by
    nlinarith
  have hNumY : 0 ≤ 1 + 3 * y := by
    nlinarith
  have hFrac :
      (1 + 3 * x) / (1 - x) ≤ (1 + 3 * y) / (1 - y) :=
    frac_mono hxy hy1
  have hSqrt :
      Real.sqrt ((1 + 3 * x) / (1 - x)) ≤
        Real.sqrt ((1 + 3 * y) / (1 - y)) := by
    exact Real.sqrt_le_sqrt hFrac
  have hAdd :
      1 + Real.sqrt ((1 + 3 * x) / (1 - x)) ≤
        1 + Real.sqrt ((1 + 3 * y) / (1 - y)) := by
    linarith
  have hDiff :
      (1 + Real.sqrt ((1 + 3 * x) / (1 - x))) / 2 -
        (1 + Real.sqrt ((1 + 3 * y) / (1 - y))) / 2 ≤ 0 := by
    linarith
  have hLe :
      (1 + Real.sqrt ((1 + 3 * x) / (1 - x))) / 2 ≤
        (1 + Real.sqrt ((1 + 3 * y) / (1 - y))) / 2 := by
    linarith
  simpa [lambdaOfKSq] using hLe

theorem lambdaOfKSq_le_of_witness
    {ksq : ℝ} {kSqUpper lambdaUpper : ℚ}
    (hKsq : ksq ≤ (kSqUpper : ℝ))
    (hWitness : lambdaUpperWitnessQ kSqUpper lambdaUpper)
    (hKsqNonneg : 0 ≤ ksq) :
    lambdaOfKSq ksq ≤ (lambdaUpper : ℝ) := by
  rcases hWitness with ⟨hSqNonnegQ, hSqLtOneQ, hHalfQ, hAlgQ⟩
  have hSqNonneg : (0 : ℝ) ≤ (kSqUpper : ℝ) := by
    exact_mod_cast hSqNonnegQ
  have hSqLtOne : ((kSqUpper : ℚ) : ℝ) < 1 := by
    exact_mod_cast hSqLtOneQ
  have hHalf : (0 : ℝ) ≤ 2 * (lambdaUpper : ℝ) - 1 := by
    exact_mod_cast hHalfQ
  have hAlg :
      (1 : ℝ) + 3 * (kSqUpper : ℝ) ≤
        (2 * (lambdaUpper : ℝ) - 1) ^ 2 * (1 - (kSqUpper : ℝ)) := by
    exact_mod_cast hAlgQ
  have hMono :
      lambdaOfKSq ksq ≤ lambdaOfKSq (kSqUpper : ℝ) := by
    exact lambdaOfKSq_mono hKsqNonneg hKsq hSqLtOne
  have hDen : (0 : ℝ) < 1 - (kSqUpper : ℝ) := sub_pos.mpr hSqLtOne
  have hFrac :
      ((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ)) ≤
        (2 * (lambdaUpper : ℝ) - 1) ^ 2 := by
    have hDiff :
        ((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ)) -
          (2 * (lambdaUpper : ℝ) - 1) ^ 2 ≤ 0 := by
      field_simp [hDen.ne']
      nlinarith
    linarith
  have hSqrt :
      Real.sqrt (((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ))) ≤
        |2 * (lambdaUpper : ℝ) - 1| := by
    simpa [Real.sqrt_sq_eq_abs] using (Real.sqrt_le_sqrt hFrac)
  have hSqrt' :
      Real.sqrt (((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ))) ≤
        2 * (lambdaUpper : ℝ) - 1 := by
    simpa [abs_of_nonneg hHalf] using hSqrt
  have hAdd :
      1 + Real.sqrt (((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ))) ≤
        2 * (lambdaUpper : ℝ) := by
    linarith
  have hTop :
      lambdaOfKSq (kSqUpper : ℝ) ≤ (lambdaUpper : ℝ) := by
    have hDiff :
        (1 + Real.sqrt (((1 : ℝ) + 3 * (kSqUpper : ℝ)) / (1 - (kSqUpper : ℝ)))) / 2 -
          (lambdaUpper : ℝ) ≤ 0 := by
      linarith
    simpa [lambdaOfKSq] using hDiff
  exact hMono.trans hTop

theorem paperLambda_le_of_witness
    {K : ℝ → ℝ → ℝ} {c ρ : ℝ} {kSqUpper lambdaUpper : ℚ}
    (hKsq : (K c ρ) ^ 2 ≤ (kSqUpper : ℝ))
    (hWitness : lambdaUpperWitnessQ kSqUpper lambdaUpper) :
    paperLambda K c ρ ≤ (lambdaUpper : ℝ) := by
  simpa [paperLambda] using
    lambdaOfKSq_le_of_witness hKsq hWitness (sq_nonneg (K c ρ))

end WangOuter

structure WangBoxQ where
  lo : ℚ
  hi : ℚ
  alpha : ℚ
  lambdaUpper : ℚ
  kSqUpper : ℚ
deriving DecidableEq, Repr

namespace WangBoxQ

def loR (b : WangBoxQ) : ℝ := b.lo

def hiR (b : WangBoxQ) : ℝ := b.hi

def alphaR (b : WangBoxQ) : ℝ := b.alpha

def lambdaUpperR (b : WangBoxQ) : ℝ := b.lambdaUpper

def kSqUpperR (b : WangBoxQ) : ℝ := b.kSqUpper

def toConstant (b : WangBoxQ) : ConstantBoxQ :=
  { lo := b.lo, hi := b.hi, alpha := b.alpha, lambdaUpper := b.lambdaUpper }

def totalMassQ (branch : Branch) (c : ℚ) (boxes : List WangBoxQ) : ℚ :=
  ConstantBoxQ.totalMassQ branch c (boxes.map toConstant)

def OrderedFrom (start : ℚ) : List WangBoxQ → Prop
  | [] => True
  | b :: bs => start ≤ b.lo ∧ b.lo ≤ b.hi ∧ OrderedFrom b.hi bs

instance instDecidableOrderedFrom (start : ℚ) (boxes : List WangBoxQ) :
    Decidable (OrderedFrom start boxes) := by
  induction boxes generalizing start with
  | nil =>
      exact isTrue trivial
  | cons head tail ih =>
      dsimp [OrderedFrom]
      letI : Decidable (OrderedFrom head.hi tail) := ih head.hi
      infer_instance

def BoxValid (box : WangBoxQ) : Prop :=
  0 ≤ box.alpha ∧
  WangOuter.lambdaUpperWitnessQ box.kSqUpper box.lambdaUpper ∧
  box.alpha * box.lambdaUpper ≤ 1

def Valid : List WangBoxQ → Prop
  | [] => True
  | box :: boxes => BoxValid box ∧ Valid boxes

def KSqUpperHolds (K : ℝ → ℝ → ℝ) (c : ℚ) (boxes : List WangBoxQ) : Prop :=
  ∀ box ∈ boxes, ∀ ρ ∈ Icc box.loR box.hiR,
    (K (c : ℝ) ρ) ^ 2 ≤ box.kSqUpperR

instance instDecidableBoxValid (box : WangBoxQ) : Decidable (BoxValid box) := by
  unfold BoxValid WangOuter.lambdaUpperWitnessQ
  infer_instance

instance instDecidableValid (boxes : List WangBoxQ) : Decidable (Valid boxes) := by
  induction boxes with
  | nil =>
      exact isTrue trivial
  | cons head tail ih =>
      dsimp [Valid]
      match instDecidableBoxValid head, ih with
      | isTrue hHead, isTrue hTail =>
          exact isTrue ⟨hHead, hTail⟩
      | isFalse hHead, _ =>
          exact isFalse (by intro h; exact hHead h.1)
      | _, isFalse hTail =>
          exact isFalse (by intro h; exact hTail h.2)

theorem Valid.of_mem
    {boxes : List WangBoxQ}
    (hValid : Valid boxes) :
    ∀ {box : WangBoxQ}, box ∈ boxes → BoxValid box := by
  induction boxes with
  | nil =>
      intro box hMem
      cases hMem
  | cons head tail ih =>
      intro box hMem
      rcases hValid with ⟨hHead, hTail⟩
      simp at hMem
      rcases hMem with rfl | hMem
      · exact hHead
      · exact ih hTail hMem

theorem OrderedFrom.start_le_lo_of_mem
    {start : ℚ} {boxes : List WangBoxQ} (hOrd : OrderedFrom start boxes) :
    ∀ {box : WangBoxQ}, box ∈ boxes → start ≤ box.lo := by
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

theorem OrderedFrom.toConstant
    {start : ℚ} {boxes : List WangBoxQ} (hOrd : OrderedFrom start boxes) :
    ConstantBoxQ.OrderedFrom start (boxes.map toConstant) := by
  induction boxes generalizing start with
  | nil =>
      simp [ConstantBoxQ.OrderedFrom]
  | cons head tail ih =>
      rcases hOrd with ⟨hstart, hlohi, htail⟩
      exact ⟨by simpa [toConstant] using hstart, by simpa [toConstant] using hlohi, ih htail⟩

theorem hi_le_toConstant_of_hi_le
    {stop : ℚ} {boxes : List WangBoxQ}
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop) :
    ∀ box ∈ boxes.map toConstant, box.hi ≤ stop := by
  intro box hMem
  rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
  exact hHi orig hOrigMem

theorem toConstant_valid
    {boxes : List WangBoxQ}
    (hValid : Valid boxes) :
    ConstantBoxQ.Valid (boxes.map toConstant) := by
  intro box hMem
  rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
  rcases hValid.of_mem hOrigMem with ⟨hAlpha, hWitness, hProd⟩
  have hPos : 0 < orig.lambdaUpper := hWitness.lambdaUpper_pos
  exact ⟨hAlpha, hPos, hProd⟩

theorem toConstant_upperHolds
    {K : ℝ → ℝ → ℝ} {c : ℚ} {boxes : List WangBoxQ}
    (hValid : Valid boxes)
    (hKsq : KSqUpperHolds K c boxes) :
    ConstantBoxQ.UpperHolds (boxes.map toConstant) (fun ρ => WangOuter.paperLambda K (c : ℝ) ρ) := by
  intro box hMem ρ hρ
  rcases List.mem_map.1 hMem with ⟨orig, hOrigMem, rfl⟩
  rcases hValid.of_mem hOrigMem with ⟨_, hWitness, _⟩
  exact WangOuter.paperLambda_le_of_witness (hKsq orig hOrigMem ρ hρ) hWitness

theorem totalMassQ_pair_le_scalarCriterion
    (K : ℝ → ℝ → ℝ)
    (c splitLo splitHi oneCut : ℚ)
    (boxes1 boxes2 : List WangBoxQ)
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
    (hKsq1 : KSqUpperHolds K c boxes1)
    (hKsq2 : KSqUpperHolds K c boxes2)
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) 1, 0 < WangOuter.paperLambda K (c : ℝ) ρ)
    (hInt1 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (c : ℝ) (AffineBoxQ.branchEndR c .one))
    (hInt2 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) ρ)
      volume (AffineBoxQ.branchEndR c .one) 1) :
    (((totalMassQ .one c boxes1 + totalMassQ .two c boxes2 : ℚ) : ℝ)) ≤
      Korenblum.scalarCriterion (c : ℝ) (WangOuter.paperLambda K (c : ℝ)) := by
  simpa [totalMassQ] using
    (ConstantBoxQ.totalMassQ_pair_le_scalarCriterion
      c splitLo splitHi oneCut (boxes1.map toConstant) (boxes2.map toConstant)
      (WangOuter.paperLambda K (c : ℝ))
      hc hc1 hcsplit hSplitLoSq hSplitHiNonneg hSplitHiSq hSplitHiCut hOneCutLeOne
      hOrd1.toConstant (hi_le_toConstant_of_hi_le hHi1) hOrd2.toConstant
      (hi_le_toConstant_of_hi_le hHi2) (toConstant_valid hValid1) (toConstant_valid hValid2)
      (toConstant_upperHolds hValid1 hKsq1) (toConstant_upperHolds hValid2 hKsq2)
      hΛpos hInt1 hInt2)

end WangBoxQ

end KorenblumProofSearch3
