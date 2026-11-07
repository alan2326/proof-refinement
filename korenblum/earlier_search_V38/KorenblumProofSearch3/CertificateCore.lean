import Mathlib
import KorenblumProofSearch3.PaperEq15

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

inductive Branch where
  | one
  | two
deriving DecidableEq, Repr

structure AffineBoxQ where
  lo : ℚ
  hi : ℚ
  alpha : ℚ
  beta : ℚ
deriving DecidableEq, Repr

namespace AffineBoxQ

def loR (b : AffineBoxQ) : ℝ := b.lo

def hiR (b : AffineBoxQ) : ℝ := b.hi

def alphaR (b : AffineBoxQ) : ℝ := b.alpha

def betaR (b : AffineBoxQ) : ℝ := b.beta

def branch1PrimitiveQ (c : ℚ) (b : AffineBoxQ) (x : ℚ) : ℚ :=
  b.alpha * ((2 * x ^ 6) / c ^ 6 - (3 * x ^ 4) / c ^ 4) +
    b.beta * (((12 : ℚ) / 7) * x ^ 7 / c ^ 6 - ((12 : ℚ) / 5) * x ^ 5 / c ^ 4)

def branch2PrimitiveQ (c : ℚ) (b : AffineBoxQ) (x : ℚ) : ℚ :=
  b.alpha * (x ^ 4 / c ^ 4) + b.beta * (((4 : ℚ) / 5) * x ^ 5 / c ^ 4)

def massQ (branch : Branch) (c : ℚ) (b : AffineBoxQ) : ℚ :=
  match branch with
  | .one => branch1PrimitiveQ c b b.hi - branch1PrimitiveQ c b b.lo
  | .two => branch2PrimitiveQ c b b.hi - branch2PrimitiveQ c b b.lo

def lowerAffine (b : AffineBoxQ) (ρ : ℝ) : ℝ :=
  b.alphaR + b.betaR * ρ

def massR (branch : Branch) (c : ℚ) (b : AffineBoxQ) : ℝ :=
  match branch with
  | .one =>
      b.alphaR *
          ((2 * b.hiR ^ 6) / (c : ℝ) ^ 6 - (3 * b.hiR ^ 4) / (c : ℝ) ^ 4
            - ((2 * b.loR ^ 6) / (c : ℝ) ^ 6 - (3 * b.loR ^ 4) / (c : ℝ) ^ 4)) +
        b.betaR *
          (((12 : ℝ) / 7) * (b.hiR ^ 7 - b.loR ^ 7) / (c : ℝ) ^ 6
            - ((12 : ℝ) / 5) * (b.hiR ^ 5 - b.loR ^ 5) / (c : ℝ) ^ 4)
  | .two =>
      b.alphaR * ((b.hiR ^ 4 - b.loR ^ 4) / (c : ℝ) ^ 4) +
        b.betaR * (((4 : ℝ) / 5) * (b.hiR ^ 5 - b.loR ^ 5) / (c : ℝ) ^ 4)

def branch1LowerIntegrand (c : ℚ) (b : AffineBoxQ) (ρ : ℝ) : ℝ :=
  (12 * ρ ^ 3 * (ρ ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 6) * b.lowerAffine ρ

def branch2LowerIntegrand (c : ℚ) (b : AffineBoxQ) (ρ : ℝ) : ℝ :=
  (4 * ρ ^ 3 / (c : ℝ) ^ 4) * b.lowerAffine ρ

def OrderedFrom (start : ℚ) : List AffineBoxQ → Prop
  | [] => True
  | b :: bs => start ≤ b.lo ∧ b.lo ≤ b.hi ∧ OrderedFrom b.hi bs

instance instDecidableOrderedFrom (start : ℚ) (boxes : List AffineBoxQ) :
    Decidable (OrderedFrom start boxes) := by
  induction boxes generalizing start with
  | nil =>
      exact isTrue trivial
  | cons head tail ih =>
      dsimp [OrderedFrom]
      letI : Decidable (OrderedFrom head.hi tail) := ih head.hi
      infer_instance

def branchEndR (c : ℚ) (branch : Branch) : ℝ :=
  match branch with
  | .one => (c : ℝ) * Real.sqrt (4 / 3)
  | .two => 1

def totalMass (branch : Branch) (c : ℚ) (boxes : List AffineBoxQ) : ℝ :=
  (boxes.map fun b => b.massR branch c).sum

def totalMassQ (branch : Branch) (c : ℚ) (boxes : List AffineBoxQ) : ℚ :=
  (boxes.map fun b => b.massQ branch c).sum

def AffineLowerHolds (boxes : List AffineBoxQ) (Λ : ℝ → ℝ) : Prop :=
  ∀ box ∈ boxes, ∀ ρ ∈ Icc box.loR box.hiR, box.lowerAffine ρ ≤ (Λ ρ)⁻¹

theorem OrderedFrom.lo_le_hi_of_mem
    {start : ℚ} {boxes : List AffineBoxQ} (hOrd : OrderedFrom start boxes) :
    ∀ {box : AffineBoxQ}, box ∈ boxes → box.lo ≤ box.hi := by
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
    {start : ℚ} {boxes : List AffineBoxQ} (hOrd : OrderedFrom start boxes) :
    ∀ {box : AffineBoxQ}, box ∈ boxes → start ≤ box.lo := by
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

theorem massQ_cast_eq_massR (branch : Branch) (c : ℚ) (b : AffineBoxQ) :
    ((b.massQ branch c : ℚ) : ℝ) = b.massR branch c := by
  cases branch <;> unfold massQ massR branch1PrimitiveQ branch2PrimitiveQ loR hiR alphaR betaR <;> norm_num <;> ring

theorem totalMassQ_cast_eq_totalMass (branch : Branch) (c : ℚ) (boxes : List AffineBoxQ) :
    ((totalMassQ branch c boxes : ℚ) : ℝ) = totalMass branch c boxes := by
  induction boxes with
  | nil =>
      simp [totalMassQ, totalMass]
  | cons head tail ih =>
      simp [totalMassQ, totalMass, massQ_cast_eq_massR]
      simpa [totalMassQ, totalMass] using ih

theorem totalMassQ_pair_cast_eq
    (c : ℚ) (boxes1 boxes2 : List AffineBoxQ) :
    (((totalMassQ .one c boxes1 + totalMassQ .two c boxes2 : ℚ) : ℝ)) =
      totalMass .one c boxes1 + totalMass .two c boxes2 := by
  rw [Rat.cast_add, totalMassQ_cast_eq_totalMass, totalMassQ_cast_eq_totalMass]

theorem integral_branch2LowerIntegrand_eq_massR
    (c : ℚ) (b : AffineBoxQ) (hc0 : (c : ℝ) ≠ 0) :
    ∫ ρ in b.loR..b.hiR, branch2LowerIntegrand c b ρ = b.massR .two c := by
  have hc4 : ((c : ℝ) ^ 4) ≠ 0 := pow_ne_zero 4 hc0
  have hleftInt : IntervalIntegrable
      (fun ρ : ℝ => b.alphaR * (4 * ρ ^ 3 / (c : ℝ) ^ 4)) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    continuity
  have hrightInt : IntervalIntegrable
      (fun ρ : ℝ => b.betaR * (4 * ρ ^ 4 / (c : ℝ) ^ 4)) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    continuity
  have hsplit :
      ∫ ρ in b.loR..b.hiR, branch2LowerIntegrand c b ρ =
        ∫ ρ in b.loR..b.hiR, b.alphaR * (4 * ρ ^ 3 / (c : ℝ) ^ 4) +
          b.betaR * (4 * ρ ^ 4 / (c : ℝ) ^ 4) := by
    apply intervalIntegral.integral_congr
    intro ρ hρ
    unfold branch2LowerIntegrand lowerAffine
    ring
  rw [hsplit, intervalIntegral.integral_add hleftInt hrightInt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpow3 :
      ∫ ρ in b.loR..b.hiR, 4 * ρ ^ 3 / (c : ℝ) ^ 4 =
        (4 / (c : ℝ) ^ 4) * ∫ ρ in b.loR..b.hiR, ρ ^ 3 := by
    have hEq :
        (fun ρ : ℝ => 4 * ρ ^ 3 / (c : ℝ) ^ 4) =
          fun ρ : ℝ => (4 / (c : ℝ) ^ 4) * ρ ^ 3 := by
      ext ρ
      field_simp [hc4]
    rw [hEq, intervalIntegral.integral_const_mul]
  have hpow4 :
      ∫ ρ in b.loR..b.hiR, 4 * ρ ^ 4 / (c : ℝ) ^ 4 =
        (4 / (c : ℝ) ^ 4) * ∫ ρ in b.loR..b.hiR, ρ ^ 4 := by
    have hEq :
        (fun ρ : ℝ => 4 * ρ ^ 4 / (c : ℝ) ^ 4) =
          fun ρ : ℝ => (4 / (c : ℝ) ^ 4) * ρ ^ 4 := by
      ext ρ
      field_simp [hc4]
    rw [hEq, intervalIntegral.integral_const_mul]
  rw [hpow3, hpow4, integral_pow, integral_pow]
  unfold massR loR hiR alphaR betaR
  field_simp [hc0]
  ring

set_option maxHeartbeats 800000 in
theorem integral_branch1LowerIntegrand_eq_massR
    (c : ℚ) (b : AffineBoxQ) (hc0 : (c : ℝ) ≠ 0) :
    ∫ ρ in b.loR..b.hiR, branch1LowerIntegrand c b ρ = b.massR .one c := by
  have hc4 : ((c : ℝ) ^ 4) ≠ 0 := pow_ne_zero 4 hc0
  have hc6 : ((c : ℝ) ^ 6) ≠ 0 := pow_ne_zero 6 hc0
  let F : ℝ → ℝ := fun x =>
    b.alphaR * ((2 * x ^ 6) / (c : ℝ) ^ 6 - (3 * x ^ 4) / (c : ℝ) ^ 4) +
      b.betaR * (((12 : ℝ) / 7) * x ^ 7 / (c : ℝ) ^ 6 - ((12 : ℝ) / 5) * x ^ 5 / (c : ℝ) ^ 4)
  have hFDeriv : ∀ x ∈ uIcc b.loR b.hiR, HasDerivAt F (branch1LowerIntegrand c b x) x := by
    intro x hx
    dsimp [F]
    have hx4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
      simpa using (hasDerivAt_id x).pow 4
    have hx5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
      simpa using (hasDerivAt_id x).pow 5
    have hx6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * x ^ 5) x := by
      simpa using (hasDerivAt_id x).pow 6
    have hx7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by
      simpa using (hasDerivAt_id x).pow 7
    have hαCore :
        HasDerivAt
          (fun y : ℝ => (2 * y ^ 6) / (c : ℝ) ^ 6 - (3 * y ^ 4) / (c : ℝ) ^ 4)
          (12 * x ^ 5 / (c : ℝ) ^ 6 - 12 * x ^ 3 / (c : ℝ) ^ 4)
          x := by
      have h6 : HasDerivAt (fun y : ℝ => (2 * y ^ 6) / (c : ℝ) ^ 6) (12 * x ^ 5 / (c : ℝ) ^ 6) x := by
        convert (((hx6.const_mul (2 : ℝ)).div_const ((c : ℝ) ^ 6))) using 1 <;> ring
      have h4 : HasDerivAt (fun y : ℝ => (3 * y ^ 4) / (c : ℝ) ^ 4) (12 * x ^ 3 / (c : ℝ) ^ 4) x := by
        convert (((hx4.const_mul (3 : ℝ)).div_const ((c : ℝ) ^ 4))) using 1 <;> ring
      exact h6.sub h4
    have hβCore :
        HasDerivAt
          (fun y : ℝ => ((12 : ℝ) / 7) * y ^ 7 / (c : ℝ) ^ 6 - ((12 : ℝ) / 5) * y ^ 5 / (c : ℝ) ^ 4)
          (12 * x ^ 6 / (c : ℝ) ^ 6 - 12 * x ^ 4 / (c : ℝ) ^ 4)
          x := by
      have h7 : HasDerivAt (fun y : ℝ => ((12 : ℝ) / 7) * y ^ 7 / (c : ℝ) ^ 6) (12 * x ^ 6 / (c : ℝ) ^ 6) x := by
        convert (((hx7.const_mul ((12 : ℝ) / 7)).div_const ((c : ℝ) ^ 6))) using 1 <;> ring
      have h5 : HasDerivAt (fun y : ℝ => ((12 : ℝ) / 5) * y ^ 5 / (c : ℝ) ^ 4) (12 * x ^ 4 / (c : ℝ) ^ 4) x := by
        convert (((hx5.const_mul ((12 : ℝ) / 5)).div_const ((c : ℝ) ^ 4))) using 1 <;> ring
      exact h7.sub h5
    have h : HasDerivAt
        (fun y : ℝ =>
          b.alphaR * ((2 * y ^ 6) / (c : ℝ) ^ 6 - (3 * y ^ 4) / (c : ℝ) ^ 4) +
            b.betaR * (((12 : ℝ) / 7) * y ^ 7 / (c : ℝ) ^ 6 - ((12 : ℝ) / 5) * y ^ 5 / (c : ℝ) ^ 4))
        (b.alphaR * (12 * x ^ 5 / (c : ℝ) ^ 6 - 12 * x ^ 3 / (c : ℝ) ^ 4) +
          b.betaR * (12 * x ^ 6 / (c : ℝ) ^ 6 - 12 * x ^ 4 / (c : ℝ) ^ 4))
        x := by
      exact (hαCore.const_mul b.alphaR).add (hβCore.const_mul b.betaR)
    convert h using 1
    unfold branch1LowerIntegrand lowerAffine
    field_simp [hc4, hc6]
  have hFInt : IntervalIntegrable (fun x => branch1LowerIntegrand c b x) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    dsimp [branch1LowerIntegrand, lowerAffine]
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFDeriv hFInt]
  unfold F massR loR hiR alphaR betaR
  ring

theorem totalMass_le_intervalIntegral
    (f : ℝ → ℝ) (mass : AffineBoxQ → ℝ) (start stop : ℚ)
    (hstartstop : start ≤ stop)
    (boxes : List AffineBoxQ)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hInt : IntervalIntegrable f volume (start : ℝ) (stop : ℝ))
    (hNonneg : ∀ x ∈ Icc (start : ℝ) (stop : ℝ), 0 ≤ f x)
    (hMass : ∀ box ∈ boxes, mass box ≤ ∫ x in box.loR..box.hiR, f x) :
    (boxes.map mass).sum ≤ ∫ x in (start : ℝ)..(stop : ℝ), f x := by
  induction boxes generalizing start with
  | nil =>
      simp
      exact intervalIntegral.integral_nonneg (by exact_mod_cast hstartstop) hNonneg
  | cons box boxes ih =>
      rcases hOrd with ⟨hstartloQ, hlohiQ, hOrdTail⟩
      have hstartstopR : (start : ℝ) ≤ (stop : ℝ) := by
        exact_mod_cast hstartstop
      have hstartlo : (start : ℝ) ≤ box.loR := by
        simpa [loR] using hstartloQ
      have hlohi : box.loR ≤ box.hiR := by
        simpa [loR, hiR] using hlohiQ
      have hhiendQ : box.hi ≤ stop := hHi box (by simp)
      have hloendQ : box.lo ≤ stop := le_trans hlohiQ hhiendQ
      have hstarthi : (start : ℝ) ≤ box.hiR := le_trans hstartlo hlohi
      have hloend : box.loR ≤ (stop : ℝ) := by
        simpa [loR] using hloendQ
      have hhiend : box.hiR ≤ (stop : ℝ) := by
        simpa [hiR] using hhiendQ
      have hIntStartLo : IntervalIntegrable f volume (start : ℝ) box.loR := by
        apply hInt.mono_set
        simpa [uIcc_of_le hstartlo, uIcc_of_le hstartstopR] using
          (Icc_subset_Icc (show (start : ℝ) ≤ (start : ℝ) by rfl) hloend)
      have hIntLoHi : IntervalIntegrable f volume box.loR box.hiR := by
        apply hInt.mono_set
        simpa [uIcc_of_le hlohi, uIcc_of_le hstartstopR] using
          (Icc_subset_Icc hstartlo hhiend)
      have hIntHiEnd : IntervalIntegrable f volume box.hiR (stop : ℝ) := by
        apply hInt.mono_set
        simpa [uIcc_of_le hhiend, uIcc_of_le hstartstopR] using
          (Icc_subset_Icc hstarthi (show (stop : ℝ) ≤ (stop : ℝ) by rfl))
      have hGapNonneg : 0 ≤ ∫ x in (start : ℝ)..box.loR, f x := by
        apply intervalIntegral.integral_nonneg hstartlo
        intro x hx
        exact hNonneg x ((Icc_subset_Icc (show (start : ℝ) ≤ (start : ℝ) by rfl) hloend) hx)
      have hTail : (boxes.map mass).sum ≤ ∫ x in box.hiR..(stop : ℝ), f x := by
        apply ih (start := box.hi)
        · exact hhiendQ
        · exact hOrdTail
        · intro b hb
          exact hHi b (by simp [hb])
        · exact hIntHiEnd
        · intro x hx
          exact hNonneg x ((Icc_subset_Icc hstarthi (show (stop : ℝ) ≤ (stop : ℝ) by rfl)) hx)
        · intro b hb
          exact hMass b (by simp [hb])
      have hLoEnd : IntervalIntegrable f volume box.loR (stop : ℝ) := hIntLoHi.trans hIntHiEnd
      have hBox : mass box ≤ ∫ x in box.loR..box.hiR, f x := hMass box (by simp)
      simp
      calc
        mass box + (boxes.map mass).sum
            ≤ (∫ x in box.loR..box.hiR, f x) + ∫ x in box.hiR..(stop : ℝ), f x := add_le_add hBox hTail
        _ = ∫ x in box.loR..(stop : ℝ), f x := by
          simpa using intervalIntegral.integral_add_adjacent_intervals hIntLoHi hIntHiEnd
        _ ≤ (∫ x in (start : ℝ)..box.loR, f x) + ∫ x in box.loR..(stop : ℝ), f x := by
          exact le_add_of_nonneg_left hGapNonneg
        _ = ∫ x in (start : ℝ)..(stop : ℝ), f x := by
          simpa using intervalIntegral.integral_add_adjacent_intervals hIntStartLo hLoEnd

theorem branch1LowerIntegrand_le_scalarIntegrand
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : (c : ℝ) ≤ b.loR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    ∀ ρ ∈ Icc b.loR b.hiR, branch1LowerIntegrand c b ρ ≤ Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
  intro ρ hρ
  have hρgec : (c : ℝ) ≤ ρ := le_trans hlo hρ.1
  have hρnonneg : 0 ≤ ρ := le_trans hc.le hρgec
  have hdiff : 0 ≤ ρ ^ 2 - (c : ℝ) ^ 2 := by
    nlinarith
  have hweight_nonneg : 0 ≤ 12 * ρ ^ 3 * (ρ ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 6 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left (hAffine ρ hρ) hweight_nonneg
  simpa [branch1LowerIntegrand, Korenblum.scalarIntegrand1, lowerAffine, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hmul

theorem branch2LowerIntegrand_le_scalarIntegrand
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : 0 ≤ b.loR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    ∀ ρ ∈ Icc b.loR b.hiR, branch2LowerIntegrand c b ρ ≤ Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
  intro ρ hρ
  have hρnonneg : 0 ≤ ρ := le_trans hlo hρ.1
  have hweight_nonneg : 0 ≤ 4 * ρ ^ 3 / (c : ℝ) ^ 4 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left (hAffine ρ hρ) hweight_nonneg
  simpa [branch2LowerIntegrand, Korenblum.scalarIntegrand2, lowerAffine, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hmul

theorem massR_branch1_le_intervalIntegral
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : (c : ℝ) ≤ b.loR)
    (hlohi : b.loR ≤ b.hiR)
    (hInt : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) volume b.loR b.hiR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    b.massR .one c ≤ ∫ ρ in b.loR..b.hiR, Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
  have hLowerInt : IntervalIntegrable (fun ρ => branch1LowerIntegrand c b ρ) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    dsimp [branch1LowerIntegrand, lowerAffine]
    continuity
  rw [← integral_branch1LowerIntegrand_eq_massR c b (by exact_mod_cast hc.ne')]
  exact intervalIntegral.integral_mono_on hlohi hLowerInt hInt
    (branch1LowerIntegrand_le_scalarIntegrand c b Λ hc hlo hAffine)

theorem massR_branch2_le_intervalIntegral
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : 0 ≤ b.loR)
    (hlohi : b.loR ≤ b.hiR)
    (hInt : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume b.loR b.hiR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    b.massR .two c ≤ ∫ ρ in b.loR..b.hiR, Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
  have hLowerInt : IntervalIntegrable (fun ρ => branch2LowerIntegrand c b ρ) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    dsimp [branch2LowerIntegrand, lowerAffine]
    continuity
  rw [← integral_branch2LowerIntegrand_eq_massR c b (by exact_mod_cast hc.ne')]
  exact intervalIntegral.integral_mono_on hlohi hLowerInt hInt
    (branch2LowerIntegrand_le_scalarIntegrand c b Λ hc hlo hAffine)

theorem scalarIntegrand1_nonneg
    (c : ℝ) (Λ : ℝ → ℝ) (hc : 0 < c)
    (hΛpos : 0 < Λ ρ) (hρc : c ≤ ρ) :
    0 ≤ Korenblum.scalarIntegrand1 c Λ ρ := by
  have hρnonneg : 0 ≤ ρ := le_trans hc.le hρc
  have hdiff : 0 ≤ ρ ^ 2 - c ^ 2 := by
    nlinarith
  unfold Korenblum.scalarIntegrand1
  have hnum : 0 ≤ 12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2) := by positivity
  have hden : 0 ≤ c ^ 6 * Λ ρ := by positivity
  exact div_nonneg hnum hden

theorem scalarIntegrand2_nonneg
    (c : ℝ) (Λ : ℝ → ℝ) (hc : 0 < c)
    (hΛpos : 0 < Λ ρ) (hρnonneg : 0 ≤ ρ) :
    0 ≤ Korenblum.scalarIntegrand2 c Λ ρ := by
  unfold Korenblum.scalarIntegrand2
  have hnum : 0 ≤ 4 * ρ ^ 3 := by positivity
  have hden : 0 ≤ c ^ 4 * Λ ρ := by positivity
  exact div_nonneg hnum hden

theorem le_branchOneEnd_of_sq
    {c splitLo : ℚ}
    (hc : 0 ≤ (c : ℝ))
    (hs : 0 ≤ (splitLo : ℝ))
    (hSq : 3 * splitLo ^ 2 ≤ 4 * c ^ 2) :
    (splitLo : ℝ) ≤ branchEndR c .one := by
  have hsqrt_nonneg : 0 ≤ (4 / 3 : ℝ) := by norm_num
  have hbranch_sq : (branchEndR c .one) ^ 2 = (c : ℝ) ^ 2 * (4 / 3 : ℝ) := by
    unfold branchEndR
    calc
      (((c : ℝ) * Real.sqrt (4 / 3 : ℝ)) ^ 2) = (c : ℝ) ^ 2 * (Real.sqrt (4 / 3 : ℝ)) ^ 2 := by
        ring
      _ = (c : ℝ) ^ 2 * (4 / 3 : ℝ) := by
        rw [Real.sq_sqrt hsqrt_nonneg]
  have hSqr : (splitLo : ℝ) ^ 2 ≤ (branchEndR c .one) ^ 2 := by
    have hSqR : 3 * (splitLo : ℝ) ^ 2 ≤ 4 * (c : ℝ) ^ 2 := by
      exact_mod_cast hSq
    rw [hbranch_sq]
    nlinarith
  have hEndNonneg : 0 ≤ branchEndR c .one := by
    unfold branchEndR
    positivity
  nlinarith

theorem branchOneEnd_le_of_sq
    {c splitHi : ℚ}
    (hc : 0 ≤ (c : ℝ))
    (hs : 0 ≤ (splitHi : ℝ))
    (hSq : 4 * c ^ 2 ≤ 3 * splitHi ^ 2) :
    branchEndR c .one ≤ (splitHi : ℝ) := by
  have hsqrt_nonneg : 0 ≤ (4 / 3 : ℝ) := by norm_num
  have hbranch_sq : (branchEndR c .one) ^ 2 = (c : ℝ) ^ 2 * (4 / 3 : ℝ) := by
    unfold branchEndR
    calc
      (((c : ℝ) * Real.sqrt (4 / 3 : ℝ)) ^ 2) = (c : ℝ) ^ 2 * (Real.sqrt (4 / 3 : ℝ)) ^ 2 := by
        ring
      _ = (c : ℝ) ^ 2 * (4 / 3 : ℝ) := by
        rw [Real.sq_sqrt hsqrt_nonneg]
  have hSqr : (branchEndR c .one) ^ 2 ≤ (splitHi : ℝ) ^ 2 := by
    have hSqR : 4 * (c : ℝ) ^ 2 ≤ 3 * (splitHi : ℝ) ^ 2 := by
      exact_mod_cast hSq
    rw [hbranch_sq]
    nlinarith
  have hEndNonneg : 0 ≤ branchEndR c .one := by
    unfold branchEndR
    positivity
  nlinarith

theorem branch1_totalMass_le_intervalIntegral
    (c splitLo : ℚ) (boxes : List AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hcsplit : c ≤ splitLo)
    (hOrd : OrderedFrom c boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ splitLo)
    (hInt : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) volume (c : ℝ) (splitLo : ℝ))
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) (splitLo : ℝ), 0 < Λ ρ)
    (hAffine : AffineLowerHolds boxes Λ) :
    totalMass .one c boxes ≤ ∫ ρ in (c : ℝ)..(splitLo : ℝ), Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
  unfold totalMass
  refine totalMass_le_intervalIntegral
    (f := fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ)
    (mass := fun b => b.massR .one c)
    (start := c)
    (stop := splitLo)
    hcsplit boxes hOrd hHi hInt ?_ ?_
  · intro ρ hρ
    exact scalarIntegrand1_nonneg (c := (c : ℝ)) (Λ := Λ) hc (hΛpos ρ hρ) hρ.1
  · intro box hMem
    have hloQ : c ≤ box.lo := OrderedFrom.start_le_lo_of_mem hOrd hMem
    have hlohiQ : box.lo ≤ box.hi := OrderedFrom.lo_le_hi_of_mem hOrd hMem
    have hloR : (c : ℝ) ≤ box.loR := by simpa [loR] using hloQ
    have hlohiR : box.loR ≤ box.hiR := by simpa [loR, hiR] using hlohiQ
    have hhiQ : box.hi ≤ splitLo := hHi box hMem
    have hhiR : box.hiR ≤ (splitLo : ℝ) := by simpa [hiR] using hhiQ
    have hSub : Set.uIcc box.loR box.hiR ⊆ Set.uIcc (c : ℝ) (splitLo : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le hloR (le_trans hlohiR hhiR)
      · exact Set.mem_uIcc_of_le (le_trans hloR hlohiR) hhiR
    have hIntBox : IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) volume box.loR box.hiR := hInt.mono_set hSub
    exact massR_branch1_le_intervalIntegral c box Λ hc hloR hlohiR hIntBox (hAffine box hMem)

theorem branch2_totalMass_le_intervalIntegral
    (c splitHi oneCut : ℚ) (boxes : List AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hsplitNonneg : 0 ≤ (splitHi : ℝ))
    (hsplitcut : splitHi ≤ oneCut)
    (hOrd : OrderedFrom splitHi boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ oneCut)
    (hInt : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume (splitHi : ℝ) (oneCut : ℝ))
    (hΛpos : ∀ ρ ∈ Icc (splitHi : ℝ) (oneCut : ℝ), 0 < Λ ρ)
    (hAffine : AffineLowerHolds boxes Λ) :
    totalMass .two c boxes ≤ ∫ ρ in (splitHi : ℝ)..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
  unfold totalMass
  refine totalMass_le_intervalIntegral
    (f := fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ)
    (mass := fun b => b.massR .two c)
    (start := splitHi)
    (stop := oneCut)
    hsplitcut boxes hOrd hHi hInt ?_ ?_
  · intro ρ hρ
    exact scalarIntegrand2_nonneg (c := (c : ℝ)) (Λ := Λ) hc (hΛpos ρ hρ) (le_trans hsplitNonneg hρ.1)
  · intro box hMem
    have hloQ : splitHi ≤ box.lo := OrderedFrom.start_le_lo_of_mem hOrd hMem
    have hlohiQ : box.lo ≤ box.hi := OrderedFrom.lo_le_hi_of_mem hOrd hMem
    have hloR : (splitHi : ℝ) ≤ box.loR := by simpa [loR] using hloQ
    have hlohiR : box.loR ≤ box.hiR := by simpa [loR, hiR] using hlohiQ
    have hhiQ : box.hi ≤ oneCut := hHi box hMem
    have hhiR : box.hiR ≤ (oneCut : ℝ) := by simpa [hiR] using hhiQ
    have hSub : Set.uIcc box.loR box.hiR ⊆ Set.uIcc (splitHi : ℝ) (oneCut : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le hloR (le_trans hlohiR hhiR)
      · exact Set.mem_uIcc_of_le (le_trans hloR hlohiR) hhiR
    have hIntBox : IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume box.loR box.hiR := hInt.mono_set hSub
    have hloNonneg : 0 ≤ box.loR := by
      exact le_trans hsplitNonneg hloR
    exact massR_branch2_le_intervalIntegral c box Λ hc hloNonneg hlohiR hIntBox (hAffine box hMem)

theorem totalMass_le_scalarCriterion
    (c splitLo splitHi oneCut : ℚ)
    (boxes1 boxes2 : List AffineBoxQ)
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
    (hAffine1 : AffineLowerHolds boxes1 Λ)
    (hAffine2 : AffineLowerHolds boxes2 Λ)
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) 1, 0 < Λ ρ)
    (hInt1 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ)
      volume (c : ℝ) (branchEndR c .one))
    (hInt2 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ)
      volume (branchEndR c .one) 1) :
    totalMass .one c boxes1 + totalMass .two c boxes2 ≤ Korenblum.scalarCriterion (c : ℝ) Λ := by
  let split : ℝ := branchEndR c .one
  have hcNonneg : 0 ≤ (c : ℝ) := le_of_lt hc
  have hSplitLoLe : (splitLo : ℝ) ≤ split := by
    simpa [split] using le_branchOneEnd_of_sq (c := c) (splitLo := splitLo)
      hcNonneg (le_trans hc.le (by exact_mod_cast hcsplit)) hSplitLoSq
  have hSplitLeHi : split ≤ (splitHi : ℝ) := by
    simpa [split] using branchOneEnd_le_of_sq (c := c) (splitHi := splitHi)
      hcNonneg hSplitHiNonneg hSplitHiSq
  have hSplitNonneg : 0 ≤ split := by
    unfold split branchEndR
    positivity
  have hSplitLeOne : split ≤ (1 : ℝ) := by
    exact le_trans hSplitLeHi (le_trans (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut)
      (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne))
  have hInt1Left : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) volume (c : ℝ) (splitLo : ℝ) := by
    have hSub : Set.uIcc (c : ℝ) (splitLo : ℝ) ⊆ Set.uIcc (c : ℝ) split := by
      apply Set.uIcc_subset_uIcc
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le (by exact_mod_cast hcsplit) hSplitLoLe
    simpa [split] using hInt1.mono_set hSub
  have hInt1Gap : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) volume (splitLo : ℝ) split := by
    have hSub : Set.uIcc (splitLo : ℝ) split ⊆ Set.uIcc (c : ℝ) split := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le (by exact_mod_cast hcsplit) hSplitLoLe
      · exact Set.right_mem_uIcc
    simpa [split] using hInt1.mono_set hSub
  have hMass1 : totalMass .one c boxes1 ≤
      ∫ ρ in (c : ℝ)..(splitLo : ℝ), Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
    apply branch1_totalMass_le_intervalIntegral c splitLo boxes1 Λ hc hcsplit hOrd1 hHi1 hInt1Left
    · intro ρ hρ
      exact hΛpos ρ ⟨hρ.1, le_trans hρ.2 (le_trans hSplitLoLe hSplitLeOne)⟩
    · exact hAffine1
  have hGap1Nonneg : 0 ≤ ∫ ρ in (splitLo : ℝ)..split, Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
    apply intervalIntegral.integral_nonneg hSplitLoLe
    intro ρ hρ
    exact scalarIntegrand1_nonneg (c := (c : ℝ)) (Λ := Λ) hc
      (hΛpos ρ ⟨le_trans (by exact_mod_cast hcsplit) hρ.1, le_trans hρ.2 hSplitLeOne⟩)
      (le_trans (by exact_mod_cast hcsplit) hρ.1)
  have hMass1Full : totalMass .one c boxes1 ≤
      ∫ ρ in (c : ℝ)..split, Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
    calc
      totalMass .one c boxes1
          ≤ ∫ ρ in (c : ℝ)..(splitLo : ℝ), Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := hMass1
      _ ≤ (∫ ρ in (c : ℝ)..(splitLo : ℝ), Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ) +
            ∫ ρ in (splitLo : ℝ)..split, Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
          exact le_add_of_nonneg_right hGap1Nonneg
      _ = ∫ ρ in (c : ℝ)..split, Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ := by
          simpa [split] using intervalIntegral.integral_add_adjacent_intervals hInt1Left hInt1Gap
  have hInt2Mid : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume (splitHi : ℝ) (oneCut : ℝ) := by
    have hSub : Set.uIcc (splitHi : ℝ) (oneCut : ℝ) ⊆ Set.uIcc split (1 : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le hSplitLeHi
          (le_trans (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut)
            (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne))
      · exact Set.mem_uIcc_of_le
          (le_trans hSplitLeHi (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut))
          (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne)
    simpa [split] using hInt2.mono_set hSub
  have hInt2GapStart : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume split (splitHi : ℝ) := by
    have hSub : Set.uIcc split (splitHi : ℝ) ⊆ Set.uIcc split (1 : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le hSplitLeHi
          (le_trans (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut)
            (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne))
    simpa [split] using hInt2.mono_set hSub
  have hInt2GapEnd : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume (oneCut : ℝ) (1 : ℝ) := by
    have hSub : Set.uIcc (oneCut : ℝ) (1 : ℝ) ⊆ Set.uIcc split (1 : ℝ) := by
      apply Set.uIcc_subset_uIcc
      · exact Set.mem_uIcc_of_le
          (le_trans hSplitLeHi (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut))
          (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne)
      · exact Set.right_mem_uIcc
    simpa [split] using hInt2.mono_set hSub
  have hMass2 : totalMass .two c boxes2 ≤
      ∫ ρ in (splitHi : ℝ)..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
    apply branch2_totalMass_le_intervalIntegral c splitHi oneCut boxes2 Λ hc hSplitHiNonneg hSplitHiCut hOrd2 hHi2 hInt2Mid
    · intro ρ hρ
      exact hΛpos ρ ⟨le_trans (by exact_mod_cast hcsplit) (le_trans hSplitLoLe (le_trans hSplitLeHi hρ.1)),
        le_trans hρ.2 (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne)⟩
    · exact hAffine2
  have hGap2StartNonneg : 0 ≤
      ∫ ρ in split..(splitHi : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
    apply intervalIntegral.integral_nonneg hSplitLeHi
    intro ρ hρ
    exact scalarIntegrand2_nonneg (c := (c : ℝ)) (Λ := Λ) hc
      (hΛpos ρ ⟨le_trans (by exact_mod_cast hcsplit) (le_trans hSplitLoLe hρ.1),
        le_trans hρ.2 (le_trans (show (splitHi : ℝ) ≤ (oneCut : ℝ) by exact_mod_cast hSplitHiCut)
          (show (oneCut : ℝ) ≤ (1 : ℝ) by exact_mod_cast hOneCutLeOne))⟩)
      (le_trans hSplitNonneg hρ.1)
  have hGap2EndNonneg : 0 ≤
      ∫ ρ in (oneCut : ℝ)..(1 : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
    apply intervalIntegral.integral_nonneg (by exact_mod_cast hOneCutLeOne)
    intro ρ hρ
    exact scalarIntegrand2_nonneg (c := (c : ℝ)) (Λ := Λ) hc
      (hΛpos ρ ⟨le_trans (by exact_mod_cast hcsplit) (le_trans hSplitLoLe (le_trans hSplitLeHi (le_trans (by exact_mod_cast hSplitHiCut) hρ.1))),
        hρ.2⟩)
      (le_trans hSplitHiNonneg (le_trans (by exact_mod_cast hSplitHiCut) hρ.1))
  have hInt2SplitToCut : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) volume split (oneCut : ℝ) :=
    hInt2GapStart.trans hInt2Mid
  have hMass2Full : totalMass .two c boxes2 ≤
      ∫ ρ in split..(1 : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
    calc
      totalMass .two c boxes2
          ≤ ∫ ρ in (splitHi : ℝ)..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := hMass2
      _ ≤ (∫ ρ in split..(splitHi : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) +
            ∫ ρ in (splitHi : ℝ)..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
          exact le_add_of_nonneg_left hGap2StartNonneg
      _ = ∫ ρ in split..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
          simpa [split] using intervalIntegral.integral_add_adjacent_intervals hInt2GapStart hInt2Mid
      _ ≤ (∫ ρ in split..(oneCut : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ) +
            ∫ ρ in (oneCut : ℝ)..(1 : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
          exact le_add_of_nonneg_right hGap2EndNonneg
      _ = ∫ ρ in split..(1 : ℝ), Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ := by
          simpa [split] using intervalIntegral.integral_add_adjacent_intervals hInt2SplitToCut hInt2GapEnd
  have hFinal := add_le_add hMass1Full hMass2Full
  simpa [Korenblum.scalarCriterion, split, branchEndR] using hFinal

theorem totalMassQ_pair_le_scalarCriterion
    (c splitLo splitHi oneCut : ℚ)
    (boxes1 boxes2 : List AffineBoxQ)
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
    (hAffine1 : AffineLowerHolds boxes1 Λ)
    (hAffine2 : AffineLowerHolds boxes2 Λ)
    (hΛpos : ∀ ρ ∈ Icc (c : ℝ) 1, 0 < Λ ρ)
    (hInt1 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 (c : ℝ) Λ ρ)
      volume (c : ℝ) (branchEndR c .one))
    (hInt2 : IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand2 (c : ℝ) Λ ρ)
      volume (branchEndR c .one) 1) :
    (((totalMassQ .one c boxes1 + totalMassQ .two c boxes2 : ℚ) : ℝ)) ≤
      Korenblum.scalarCriterion (c : ℝ) Λ := by
  calc
    (((totalMassQ .one c boxes1 + totalMassQ .two c boxes2 : ℚ) : ℝ))
      = totalMass .one c boxes1 + totalMass .two c boxes2 := totalMassQ_pair_cast_eq c boxes1 boxes2
    _ ≤ Korenblum.scalarCriterion (c : ℝ) Λ := totalMass_le_scalarCriterion c splitLo splitHi oneCut
      boxes1 boxes2 Λ hc hc1 hcsplit hSplitLoSq hSplitHiNonneg hSplitHiSq hSplitHiCut
      hOneCutLeOne hOrd1 hHi1 hOrd2 hHi2 hAffine1 hAffine2 hΛpos hInt1 hInt2

end AffineBoxQ

end KorenblumProofSearch3
