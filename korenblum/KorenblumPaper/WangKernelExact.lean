import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import KorenblumPaper.WangCertificateCore

open scoped BigOperators
open Finset MeasureTheory Set

noncomputable section

namespace KorenblumPaper

namespace WangKernelExact

def defaultTerms : Nat := 80

def rhoToT (c ρ : ℝ) : ℝ :=
  ((ρ ^ 2 - c) ^ 2) / (4 * c * ρ ^ 2)

def rhoToTQ (c ρ : ℚ) : ℚ :=
  ((ρ ^ 2 - c) ^ 2) / (4 * c * ρ ^ 2)

def yToT (c y : ℝ) : ℝ :=
  ((y - c) ^ 2) / (4 * c * y)

def phi (x : ℝ) : ℝ :=
  4 * x / (1 + x) ^ 2

def phiQ (x : ℚ) : ℚ :=
  4 * x / (1 + x) ^ 2

def paperFactor (c ρ : ℝ) (n : Nat) : ℝ :=
  ((1 + ρ ^ 2 * c ^ (2 * n + 1)) *
      (1 + c ^ (2 * n + 3) / ρ ^ 2) *
      (1 + c ^ (2 * n + 2)) ^ 2) /
    ((1 + ρ ^ 2 * c ^ (2 * n)) *
      (1 + c ^ (2 * n + 2) / ρ ^ 2) *
      (1 + c ^ (2 * n + 1)) ^ 2)

def paperFactorQ (c ρ : ℚ) (n : Nat) : ℚ :=
  ((1 + ρ ^ 2 * c ^ (2 * n + 1)) *
      (1 + c ^ (2 * n + 3) / ρ ^ 2) *
      (1 + c ^ (2 * n + 2)) ^ 2) /
    ((1 + ρ ^ 2 * c ^ (2 * n)) *
      (1 + c ^ (2 * n + 2) / ρ ^ 2) *
      (1 + c ^ (2 * n + 1)) ^ 2)

def paperTrunc (c ρ : ℝ) (N : Nat := defaultTerms) : ℝ :=
  2 * ρ * (1 + c / ρ ^ 2) * ∏ i ∈ range N, paperFactor c ρ i

def paperTruncQ (c ρ : ℚ) (N : Nat := defaultTerms) : ℚ :=
  2 * ρ * (1 + c / ρ ^ 2) * ∏ i ∈ range N, paperFactorQ c ρ i

def paperTruncSq (c ρ : ℝ) (N : Nat := defaultTerms) : ℝ :=
  (paperTrunc c ρ N) ^ 2

def paperTruncSqQ (c ρ : ℚ) (N : Nat := defaultTerms) : ℚ :=
  (paperTruncQ c ρ N) ^ 2

def pTerm (c : ℝ) (n : Nat) : ℝ := phi (c ^ (2 * n + 2))
def qTerm (c : ℝ) (n : Nat) : ℝ := phi (c ^ (2 * n + 1))

def pTermQ (c : ℚ) (n : Nat) : ℚ := phiQ (c ^ (2 * n + 2))
def qTermQ (c : ℚ) (n : Nat) : ℚ := phiQ (c ^ (2 * n + 1))

def normFactor (c t : ℝ) (n : Nat) : ℝ :=
  ((1 + pTerm c n * t) / (1 + qTerm c n * t)) ^ 2

def normFactorQ (c t : ℚ) (n : Nat) : ℚ :=
  ((1 + pTermQ c n * t) / (1 + qTermQ c n * t)) ^ 2

def normTruncSq (c t : ℝ) (N : Nat := defaultTerms) : ℝ :=
  (1 + t) * ∏ i ∈ range N, normFactor c t i

def normTruncSqQ (c t : ℚ) (N : Nat := defaultTerms) : ℚ :=
  (1 + t) * ∏ i ∈ range N, normFactorQ c t i

def logNormTruncSq (c t : ℝ) (N : Nat := defaultTerms) : ℝ :=
  Real.log (1 + t) +
    ∑ i ∈ range N,
      2 * (Real.log (1 + pTerm c i * t) - Real.log (1 + qTerm c i * t))

def truncConst (c : ℝ) (N : Nat := defaultTerms) : ℝ :=
  16 * c * ∏ i ∈ range N, ((1 + c ^ (2 * i + 2)) / (1 + c ^ (2 * i + 1))) ^ 8

def truncConstQ (c : ℚ) (N : Nat := defaultTerms) : ℚ :=
  16 * c * ∏ i ∈ range N, ((1 + c ^ (2 * i + 2)) / (1 + c ^ (2 * i + 1))) ^ 8

def logDerivSq (c t : ℝ) (N : Nat := defaultTerms) : ℝ :=
  1 / (1 + t) +
    ∑ i ∈ range N,
      2 * (pTerm c i / (1 + pTerm c i * t) - qTerm c i / (1 + qTerm c i * t))

def logDerivSqQ (c t : ℚ) (N : Nat := defaultTerms) : ℚ :=
  1 / (1 + t) +
    ∑ i ∈ range N,
      2 * (pTermQ c i / (1 + pTermQ c i * t) - qTermQ c i / (1 + qTermQ c i * t))

def logDerivSqSlopeUpperQ (c t : ℚ) (N : Nat := defaultTerms) : ℚ :=
  -1 / (1 + t) ^ 2 +
    ∑ i ∈ range N,
      2 *
        (qTermQ c i ^ 2 / (1 + qTermQ c i * t) ^ 2 -
          pTermQ c i ^ 2 / (1 + pTermQ c i * t) ^ 2)

def logDerivSqSlope (c t : ℝ) (N : Nat := defaultTerms) : ℝ :=
  -1 / (1 + t) ^ 2 +
    ∑ i ∈ range N,
      2 *
        (qTerm c i ^ 2 / (1 + qTerm c i * t) ^ 2 -
          pTerm c i ^ 2 / (1 + pTerm c i * t) ^ 2)

def crossesSqrtQ (c lo hi : ℚ) : Prop := lo ^ 2 ≤ c ∧ c ≤ hi ^ 2

instance (c lo hi : ℚ) : Decidable (crossesSqrtQ c lo hi) := by
  unfold crossesSqrtQ
  infer_instance

def tLoQ (c lo hi : ℚ) : ℚ :=
  if crossesSqrtQ c lo hi then 0 else min (rhoToTQ c lo) (rhoToTQ c hi)
def tHiQ (c lo hi : ℚ) : ℚ := max (rhoToTQ c lo) (rhoToTQ c hi)

def anchorQ (c lo hi : ℚ) : ℚ :=
  if rhoToTQ c lo ≤ rhoToTQ c hi then hi else lo

def logDerivSqSlopeLowerQ (c lo hi : ℚ) (N : Nat := defaultTerms) : ℚ :=
  -1 / (1 + tLoQ c lo hi) ^ 2 +
    ∑ i ∈ range N,
      2 *
        (qTermQ c i ^ 2 / (1 + qTermQ c i * tHiQ c lo hi) ^ 2 -
          pTermQ c i ^ 2 / (1 + pTermQ c i * tLoQ c lo hi) ^ 2)

def logDerivSqSlopeLower (c tLo tHi : ℝ) (N : Nat := defaultTerms) : ℝ :=
  -1 / (1 + tLo) ^ 2 +
    ∑ i ∈ range N,
      2 *
        (qTerm c i ^ 2 / (1 + qTerm c i * tHi) ^ 2 -
          pTerm c i ^ 2 / (1 + pTerm c i * tLo) ^ 2)

def logDerivSqBoxLowerQ (c lo hi : ℚ) (N : Nat := defaultTerms) : ℚ :=
  let m := min (logDerivSqSlopeLowerQ c lo hi N) 0
  logDerivSqQ c (tLoQ c lo hi) N + (tHiQ c lo hi - tLoQ c lo hi) * m

def logDerivSqBoxLower (c tLo tHi : ℝ) (N : Nat := defaultTerms) : ℝ :=
  let m := min (logDerivSqSlopeLower c tLo tHi N) 0
  logDerivSq c tLo N + (tHi - tLo) * m

def boxKernelValidQ (c lo hi kSqUpper : ℚ) (N : Nat := defaultTerms) : Prop :=
  0 < logDerivSqBoxLowerQ c lo hi N ∧
  paperTruncSqQ c (anchorQ c lo hi) N ≤ kSqUpper

def PaperKFormula (K : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ρ ∈ Icc c 1, ∃ hmul : Multipliable (paperFactor c ρ),
    K c ρ = 2 * ρ * (1 + c / ρ ^ 2) * ∏' n, paperFactor c ρ n

instance (c lo hi kSqUpper : ℚ) (N : Nat) :
    Decidable (boxKernelValidQ c lo hi kSqUpper N) := by
  unfold boxKernelValidQ
  infer_instance

theorem phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phi x := by
  dsimp [phi]
  positivity

theorem rhoToT_nonneg
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : 0 < ρ) :
    0 ≤ rhoToT c ρ := by
  dsimp [rhoToT]
  positivity

theorem rhoToT_eq_yToT
    {c ρ : ℝ} :
    rhoToT c ρ = yToT c (ρ ^ 2) := by
  rfl

theorem yToT_sub_yToT
    {c x y : ℝ}
    (hc : 0 < c)
    (hx : 0 < x)
    (hy : 0 < y) :
    yToT c x - yToT c y = ((x - y) * (1 - c ^ 2 / (x * y))) / (4 * c) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  dsimp [yToT]
  field_simp [hc0, hx0, hy0]
  ring

theorem yToT_antitone_left_of_le_c
    {c x y : ℝ}
    (hc : 0 < c)
    (hx : 0 < x)
    (hxy : x ≤ y)
    (hyc : y ≤ c) :
    yToT c y ≤ yToT c x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hdiff := yToT_sub_yToT hc hx hy
  have hprod : 0 ≤ (x - y) * (1 - c ^ 2 / (x * y)) := by
    have hxy' : x - y ≤ 0 := by linarith
    have hxyc : x * y ≤ c ^ 2 := by
      nlinarith
    have hfactor : 1 - c ^ 2 / (x * y) ≤ 0 := by
      have hxypos : 0 < x * y := by positivity
      have hdiv : 1 ≤ c ^ 2 / (x * y) := by
        apply (le_div_iff₀ hxypos).2
        nlinarith
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hxy' hfactor
  have hden : 0 < 4 * c := by positivity
  have hmain : 0 ≤ yToT c x - yToT c y := by
    rw [yToT_sub_yToT hc hx hy]
    exact div_nonneg hprod hden.le
  linarith

theorem yToT_monotone_right_of_c_le
    {c x y : ℝ}
    (hc : 0 < c)
    (hcx : c ≤ x)
    (hxy : x ≤ y)
    (hx : 0 < x) :
    yToT c x ≤ yToT c y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hdiff := yToT_sub_yToT hc hx hy
  have hprod : ((x - y) * (1 - c ^ 2 / (x * y))) ≤ 0 := by
    have hxy' : x - y ≤ 0 := by linarith
    have hcxy : c ^ 2 ≤ x * y := by
      nlinarith
    have hfactor : 0 ≤ 1 - c ^ 2 / (x * y) := by
      have hxypos : 0 < x * y := by positivity
      have hdiv : c ^ 2 / (x * y) ≤ 1 := by
        apply (div_le_iff₀ hxypos).2
        nlinarith
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hxy' hfactor
  have hden : 0 < 4 * c := by positivity
  have hmain : yToT c x - yToT c y ≤ 0 := by
    rw [yToT_sub_yToT hc hx hy]
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith

theorem yToT_le_max_endpoints
    {c a b z : ℝ}
    (hc : 0 < c)
    (ha : 0 < a)
    (hab : a ≤ b)
    (haz : a ≤ z)
    (hzb : z ≤ b) :
    yToT c z ≤ max (yToT c a) (yToT c b) := by
  by_cases hzc : z ≤ c
  · have hza : yToT c z ≤ yToT c a := by
      exact yToT_antitone_left_of_le_c hc ha haz hzc
    exact hza.trans (le_max_left _ _)
  · have hcz : c ≤ z := by linarith
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hzb' : yToT c z ≤ yToT c b := by
      exact yToT_monotone_right_of_c_le hc hcz hzb (lt_of_lt_of_le ha haz)
    exact hzb'.trans (le_max_right _ _)

theorem rhoToT_le_tHi
    {c lo hi ρ : ℝ}
    (hc : 0 < c)
    (hlo : 0 < lo)
    (hloρ : lo ≤ ρ)
    (hρhi : ρ ≤ hi) :
  rhoToT c ρ ≤ max (rhoToT c lo) (rhoToT c hi) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hlo hloρ
  have hlo2 : 0 < lo ^ 2 := by positivity
  have hsq_loρ : lo ^ 2 ≤ ρ ^ 2 := by gcongr <;> exact hlo.le
  have hsq_ρhi : ρ ^ 2 ≤ hi ^ 2 := by
    have hhi : 0 < hi := lt_of_lt_of_le hρ hρhi
    gcongr <;> positivity
  have hsq_lohi : lo ^ 2 ≤ hi ^ 2 := le_trans hsq_loρ hsq_ρhi
  simpa [rhoToT_eq_yToT] using
    (yToT_le_max_endpoints hc hlo2 hsq_lohi hsq_loρ hsq_ρhi)

theorem rhoToTQ_cast (c ρ : ℚ) :
    ((rhoToTQ c ρ : ℚ) : ℝ) = rhoToT (c : ℝ) (ρ : ℝ) := by
  simp [rhoToTQ, rhoToT]

theorem rhoToTQ_nonneg
    {c ρ : ℚ}
    (hc : 0 < c)
    (hρ : 0 < ρ) :
    0 ≤ rhoToTQ c ρ := by
  dsimp [rhoToTQ]
  positivity

theorem tLoQ_nonneg
    {c lo hi : ℚ}
    (hc : 0 < c)
    (hclo : c ≤ lo)
    (hlohi : lo ≤ hi) :
    0 ≤ tLoQ c lo hi := by
  by_cases hcross : crossesSqrtQ c lo hi
  · simp [tLoQ, hcross]
  · have hlo : 0 < lo := lt_of_lt_of_le hc hclo
    have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
    simp [tLoQ, hcross]
    exact ⟨rhoToTQ_nonneg hc hlo, rhoToTQ_nonneg hc hhi⟩

theorem rhoToT_le_tHiQ
    {c lo hi : ℚ}
    {ρ : ℝ}
    (hc : 0 < (c : ℝ))
    (hclo : c ≤ lo)
    (hρ : ρ ∈ Icc (lo : ℝ) (hi : ℝ)) :
    rhoToT (c : ℝ) ρ ≤ (tHiQ c lo hi : ℝ) := by
  have hlo : 0 < (lo : ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hclo)
  have hmax := rhoToT_le_tHi hc hlo hρ.1 hρ.2
  simpa [tHiQ, rhoToTQ_cast] using hmax

theorem tLoQ_le_rhoToT
    {c lo hi : ℚ}
    {ρ : ℝ}
    (hc : 0 < (c : ℝ))
    (hclo : c ≤ lo)
    (hρ : ρ ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (tLoQ c lo hi : ℝ) ≤ rhoToT (c : ℝ) ρ := by
  by_cases hcross : crossesSqrtQ c lo hi
  · have hρpos : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le hc (by exact_mod_cast hclo)) hρ.1
    simp [tLoQ, hcross]
    exact rhoToT_nonneg hc hρpos
  · have hρpos : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le hc (by exact_mod_cast hclo)) hρ.1
    have hρ2pos : 0 < ρ ^ 2 := by positivity
    have hlo2 : 0 < ((lo : ℝ) ^ 2) := by
      have hlo : 0 < (lo : ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hclo)
      positivity
    have hsq_loρ : (lo : ℝ) ^ 2 ≤ ρ ^ 2 := by
      have hlo : 0 < (lo : ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hclo)
      nlinarith [hρ.1, hlo.le]
    by_cases hleft : hi ^ 2 ≤ c
    · have hhi2 : ((hi : ℝ) ^ 2) ≤ (c : ℝ) := by exact_mod_cast hleft
      have hρ2hi : ρ ^ 2 ≤ (hi : ℝ) ^ 2 := by
        have hhi : 0 < (hi : ℝ) := lt_of_lt_of_le hρpos hρ.2
        nlinarith [hρ.2, hhi.le]
      have hhi_lower : rhoToT (c : ℝ) (hi : ℝ) ≤ rhoToT (c : ℝ) ρ := by
        simpa [rhoToT_eq_yToT] using
          (yToT_antitone_left_of_le_c hc hρ2pos hρ2hi hhi2)
      have hmin :
          ((min (rhoToTQ c lo) (rhoToTQ c hi) : ℚ) : ℝ) ≤ rhoToT (c : ℝ) (hi : ℝ) := by
        have hminQ : min (rhoToTQ c lo) (rhoToTQ c hi) ≤ rhoToTQ c hi := min_le_right _ _
        have hmin' : (((min (rhoToTQ c lo) (rhoToTQ c hi) : ℚ) : ℝ) ≤ ((rhoToTQ c hi : ℚ) : ℝ)) := by
          exact_mod_cast hminQ
        simpa [rhoToTQ_cast] using hmin'
      have htLo :
          (tLoQ c lo hi : ℝ) ≤ rhoToT (c : ℝ) (hi : ℝ) := by
        simpa [tLoQ, hcross, rhoToTQ_cast] using hmin
      exact htLo.trans hhi_lower
    · have hlo2q : ¬ lo ^ 2 ≤ c := by
        intro hlo2q
        exact hcross ⟨hlo2q, le_of_not_ge hleft⟩
      have hlo2c : (c : ℝ) ≤ (lo : ℝ) ^ 2 := by
        exact_mod_cast (le_of_not_ge hlo2q)
      have hlo_lower : rhoToT (c : ℝ) (lo : ℝ) ≤ rhoToT (c : ℝ) ρ := by
        simpa [rhoToT_eq_yToT] using
          (yToT_monotone_right_of_c_le hc hlo2c hsq_loρ hlo2)
      have hmin :
          ((min (rhoToTQ c lo) (rhoToTQ c hi) : ℚ) : ℝ) ≤ rhoToT (c : ℝ) (lo : ℝ) := by
        have hminQ : min (rhoToTQ c lo) (rhoToTQ c hi) ≤ rhoToTQ c lo := min_le_left _ _
        have hmin' : (((min (rhoToTQ c lo) (rhoToTQ c hi) : ℚ) : ℝ) ≤ ((rhoToTQ c lo : ℚ) : ℝ)) := by
          exact_mod_cast hminQ
        simpa [rhoToTQ_cast] using hmin'
      have htLo :
          (tLoQ c lo hi : ℝ) ≤ rhoToT (c : ℝ) (lo : ℝ) := by
        simpa [tLoQ, hcross, rhoToTQ_cast] using hmin
      exact htLo.trans hlo_lower

theorem phiQ_cast (x : ℚ) :
    ((phiQ x : ℚ) : ℝ) = phi (x : ℝ) := by
  simp [phiQ, phi]

theorem pTermQ_cast (c : ℚ) (n : Nat) :
    ((pTermQ c n : ℚ) : ℝ) = pTerm (c : ℝ) n := by
  simp [pTermQ, pTerm, phiQ_cast]

theorem qTermQ_cast (c : ℚ) (n : Nat) :
    ((qTermQ c n : ℚ) : ℝ) = qTerm (c : ℝ) n := by
  simp [qTermQ, qTerm, phiQ_cast]

theorem paperFactorQ_cast (c ρ : ℚ) (n : Nat) :
    ((paperFactorQ c ρ n : ℚ) : ℝ) = paperFactor (c : ℝ) (ρ : ℝ) n := by
  simp [paperFactorQ, paperFactor]

theorem paperTruncQ_cast (c ρ : ℚ) (N : Nat := defaultTerms) :
    ((paperTruncQ c ρ N : ℚ) : ℝ) = paperTrunc (c : ℝ) (ρ : ℝ) N := by
  simp [paperTruncQ, paperTrunc, paperFactorQ_cast]

theorem paperTruncSqQ_cast (c ρ : ℚ) (N : Nat := defaultTerms) :
    ((paperTruncSqQ c ρ N : ℚ) : ℝ) = paperTruncSq (c : ℝ) (ρ : ℝ) N := by
  simp [paperTruncSqQ, paperTruncSq, paperTruncQ_cast]

theorem logDerivSqQ_cast (c t : ℚ) (N : Nat := defaultTerms) :
    ((logDerivSqQ c t N : ℚ) : ℝ) = logDerivSq (c : ℝ) (t : ℝ) N := by
  simp [logDerivSqQ, logDerivSq, pTermQ_cast, qTermQ_cast]

theorem logDerivSqSlopeLowerQ_cast (c lo hi : ℚ) (N : Nat := defaultTerms) :
    ((logDerivSqSlopeLowerQ c lo hi N : ℚ) : ℝ) =
      logDerivSqSlopeLower (c : ℝ) (tLoQ c lo hi) (tHiQ c lo hi) N := by
  simp [logDerivSqSlopeLowerQ, logDerivSqSlopeLower, pTermQ_cast, qTermQ_cast]

theorem logDerivSqBoxLowerQ_cast (c lo hi : ℚ) (N : Nat := defaultTerms) :
    ((logDerivSqBoxLowerQ c lo hi N : ℚ) : ℝ) =
      logDerivSqBoxLower (c : ℝ) (tLoQ c lo hi) (tHiQ c lo hi) N := by
  simp [logDerivSqBoxLowerQ, logDerivSqBoxLower, logDerivSqQ_cast, logDerivSqSlopeLowerQ_cast]

theorem rhoToT_anchor_eq_tHiQ (c lo hi : ℚ) :
    rhoToT (c : ℝ) (anchorQ c lo hi : ℝ) = (tHiQ c lo hi : ℝ) := by
  by_cases h : rhoToTQ c lo ≤ rhoToTQ c hi
  · simp [anchorQ, tHiQ, h, rhoToTQ_cast, max_eq_right h]
  · have h' : rhoToTQ c hi ≤ rhoToTQ c lo := le_of_not_ge h
    simp [anchorQ, tHiQ, h, rhoToTQ_cast, max_eq_left h']

theorem phi_mono_unit
    {x y : ℝ}
    (hx : 0 ≤ x)
    (hxy : x ≤ y)
    (hy1 : y ≤ 1) :
    phi x ≤ phi y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hx1 : 0 < (1 + x) ^ 2 := by positivity
  have hy1' : 0 < (1 + y) ^ 2 := by positivity
  have hmain : x * (1 + y) ^ 2 ≤ y * (1 + x) ^ 2 := by
    have hx1le : x ≤ 1 := le_trans hxy hy1
    have hprod : x * y ≤ 1 := by
      nlinarith
    nlinarith
  dsimp [phi]
  rw [div_le_div_iff₀ hx1 hy1']
  nlinarith

theorem pTerm_le_qTerm
    {c : ℝ}
    (hc : 0 ≤ c)
    (hc1 : c ≤ 1)
    (n : Nat) :
    pTerm c n ≤ qTerm c n := by
  have hpow : c ^ (2 * n + 2) = c ^ (2 * n + 1) * c := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
  have hx : 0 ≤ c ^ (2 * n + 2) := by positivity
  have hy : 0 ≤ c ^ (2 * n + 1) := by positivity
  have hxy : c ^ (2 * n + 2) ≤ c ^ (2 * n + 1) := by
    rw [hpow]
    exact mul_le_of_le_one_right hy hc1
  have hytop : c ^ (2 * n + 1) ≤ 1 := by
    simpa using (pow_le_one₀ (show 0 ≤ c by exact hc) hc1 : c ^ (2 * n + 1) ≤ 1)
  exact phi_mono_unit hx hxy hytop

theorem qTerm_nonneg
    {c : ℝ}
    (hc : 0 ≤ c)
    (n : Nat) :
    0 ≤ qTerm c n := by
  apply phi_nonneg
  positivity

theorem pTerm_nonneg
    {c : ℝ}
    (hc : 0 ≤ c)
    (n : Nat) :
    0 ≤ pTerm c n := by
  apply phi_nonneg
  positivity

theorem normFactor_pos
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (n : Nat) :
    0 < normFactor c t n := by
  have hp : 0 ≤ pTerm c n := pTerm_nonneg hc n
  have hq : 0 ≤ qTerm c n := qTerm_nonneg hc n
  dsimp [normFactor]
  positivity

theorem normTruncSq_pos
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (N : Nat := defaultTerms) :
    0 < normTruncSq c t N := by
  dsimp [normTruncSq]
  refine mul_pos ?_ ?_
  · positivity
  · refine Finset.prod_pos ?_
    intro i hi
    exact normFactor_pos hc ht i

theorem log_normFactor
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (n : Nat) :
    Real.log (normFactor c t n) =
      2 * (Real.log (1 + pTerm c n * t) - Real.log (1 + qTerm c n * t)) := by
  have hp : 0 ≤ pTerm c n := pTerm_nonneg hc n
  have hq : 0 ≤ qTerm c n := qTerm_nonneg hc n
  have hnum : 0 < 1 + pTerm c n * t := by
    nlinarith
  have hden : 0 < 1 + qTerm c n * t := by
    nlinarith
  dsimp [normFactor]
  rw [Real.log_pow, Real.log_div (ne_of_gt hnum) (ne_of_gt hden)]
  norm_num

theorem logNormTruncSq_eq_log_normTruncSq
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (N : Nat := defaultTerms) :
    logNormTruncSq c t N = Real.log (normTruncSq c t N) := by
  have hprod_ne (M : Nat) : ∏ x ∈ Finset.range M, normFactor c t x ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i hi => normFactor_pos hc ht i)
  dsimp [logNormTruncSq, normTruncSq]
  rw [Real.log_mul]
  · congr 1
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.prod_range_succ]
        rw [Real.log_mul]
        · rw [ih, log_normFactor hc ht N]
        · exact hprod_ne N
        · exact ne_of_gt (normFactor_pos hc ht N)
  · positivity
  · exact hprod_ne N

theorem normFactor_le_one
    {c t : ℝ}
    (hc : 0 ≤ c)
    (hc1 : c ≤ 1)
    (ht : 0 ≤ t)
    (n : Nat) :
    normFactor c t n ≤ 1 := by
  have hpq : pTerm c n ≤ qTerm c n := pTerm_le_qTerm hc hc1 n
  have hq : 0 ≤ qTerm c n := qTerm_nonneg hc n
  have hp : 0 ≤ pTerm c n := by
    apply phi_nonneg
    positivity
  have hden : 0 < 1 + qTerm c n * t := by
    nlinarith
  have hratio_nonneg :
      0 ≤ (1 + pTerm c n * t) / (1 + qTerm c n * t) := by
    positivity
  have hratio_le :
      (1 + pTerm c n * t) / (1 + qTerm c n * t) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  dsimp [normFactor]
  nlinarith

theorem hasDerivAt_logLinear
    {a t : ℝ}
    (ha : 0 ≤ a)
    (ht : 0 ≤ t) :
    HasDerivAt (fun u => Real.log (1 + a * u)) (a / (1 + a * t)) t := by
  have harg : 1 + a * t ≠ 0 := by
    have : 0 < 1 + a * t := by nlinarith
    linarith
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id t).const_mul a).const_add 1).log harg)

theorem hasDerivAt_logNormTruncSq
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (N : Nat := defaultTerms) :
    HasDerivAt (fun u => logNormTruncSq c u N) (logDerivSq c t N) t := by
  have hbase :
      HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t := by
    simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_logLinear (a := (1 : ℝ)) (t := t) (by positivity) ht)
  have hsum :
      HasDerivAt
        (∑ i ∈ range N,
          fun u => 2 * (Real.log (1 + pTerm c i * u) - Real.log (1 + qTerm c i * u)))
        (∑ i ∈ range N,
          2 *
            (pTerm c i / (1 + pTerm c i * t) -
              qTerm c i / (1 + qTerm c i * t))) t := by
    refine HasDerivAt.sum ?_
    intro i hi
    have hp : 0 ≤ pTerm c i := pTerm_nonneg hc i
    have hq : 0 ≤ qTerm c i := qTerm_nonneg hc i
    have hpder := hasDerivAt_logLinear hp ht
    have hqder := hasDerivAt_logLinear hq ht
    have hp' :
        HasDerivAt
          (fun u => 2 * Real.log (1 + pTerm c i * u))
          (2 * (pTerm c i / (1 + pTerm c i * t))) t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpder.const_mul 2
    have hq' :
        HasDerivAt
          (fun u => 2 * Real.log (1 + qTerm c i * u))
          (2 * (qTerm c i / (1 + qTerm c i * t))) t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hqder.const_mul 2
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hp'.sub hq'
  convert hbase.add hsum using 1
  ext u
  simp [logNormTruncSq]

theorem hasDerivAt_divLinear
    {a t : ℝ}
    (ha : 0 ≤ a)
    (ht : 0 ≤ t) :
    HasDerivAt (fun u => a / (1 + a * u)) (-(a ^ 2) / (1 + a * t) ^ 2) t := by
  have harg : 1 + a * t ≠ 0 := by
    have : 0 < 1 + a * t := by nlinarith
    linarith
  have hInv :
      HasDerivAt (fun u => (1 + a * u)⁻¹) (-(a) / (1 + a * t) ^ 2) t := by
    simpa [one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id t).const_mul a).const_add 1).inv harg)
  simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hInv.const_mul a

theorem hasDerivAt_logDerivSq
    {c t : ℝ}
    (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (N : Nat := defaultTerms) :
    HasDerivAt (fun u => logDerivSq c u N) (logDerivSqSlope c t N) t := by
  have hbase :
      HasDerivAt (fun u => 1 / (1 + u)) (-1 / (1 + t) ^ 2) t := by
    simpa [one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id t).const_add 1).inv (by positivity)))
  have hsum :
      HasDerivAt
        (∑ i ∈ range N,
          fun u => 2 * (pTerm c i / (1 + pTerm c i * u) - qTerm c i / (1 + qTerm c i * u)))
        (∑ i ∈ range N,
          2 *
            (qTerm c i ^ 2 / (1 + qTerm c i * t) ^ 2 -
              pTerm c i ^ 2 / (1 + pTerm c i * t) ^ 2)) t := by
    refine HasDerivAt.sum ?_
    intro i hi
    have hp : 0 ≤ pTerm c i := pTerm_nonneg hc i
    have hq : 0 ≤ qTerm c i := qTerm_nonneg hc i
    have hp' := hasDerivAt_divLinear hp ht
    have hq' := hasDerivAt_divLinear hq ht
    have hp'' :
        HasDerivAt
          (fun u => 2 * (pTerm c i / (1 + pTerm c i * u)))
          (2 * (-(pTerm c i ^ 2) / (1 + pTerm c i * t) ^ 2)) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hp'.const_mul 2
    have hq'' :
        HasDerivAt
          (fun u => 2 * (qTerm c i / (1 + qTerm c i * u)))
          (2 * (-(qTerm c i ^ 2) / (1 + qTerm c i * t) ^ 2)) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hq'.const_mul 2
    convert hp''.sub hq'' using 1
    · ext u
      simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      ring
    · ring_nf
  convert hbase.add hsum using 1
  ext u
  simp [logDerivSq]

theorem logDerivSqSlopeLower_le
    {c tLo tHi u : ℝ}
    (hc : 0 ≤ c)
    (htLo : 0 ≤ tLo)
    (htLoHi : tLo ≤ tHi)
    (hu : u ∈ Icc tLo tHi)
    (N : Nat := defaultTerms) :
    logDerivSqSlopeLower c tLo tHi N ≤ logDerivSqSlope c u N := by
  have hu0 : 0 ≤ u := le_trans htLo hu.1
  have htHi : 0 ≤ tHi := le_trans htLo htLoHi
  have hbaseBase : 1 + tLo ≤ 1 + u := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hu.1 (1 : ℝ)
  have hbaseNonneg : 0 ≤ 1 + tLo := by
    linarith
  have huBaseNonneg : 0 ≤ 1 + u := by
    linarith
  have hbaseSq : (1 + tLo) ^ 2 ≤ (1 + u) ^ 2 := by
    apply sq_le_sq.2
    simpa [abs_of_nonneg hbaseNonneg, abs_of_nonneg huBaseNonneg] using hbaseBase
  have hbaseInv : 1 / (1 + u) ^ 2 ≤ 1 / (1 + tLo) ^ 2 := by
    exact one_div_le_one_div_of_le (by positivity) hbaseSq
  have hbase :
      -1 / (1 + tLo) ^ 2 ≤ -1 / (1 + u) ^ 2 := by
    have hbase' : -(1 / (1 + tLo) ^ 2) ≤ -(1 / (1 + u) ^ 2) := neg_le_neg_iff.mpr hbaseInv
    simpa [neg_div] using hbase'
  have hsum :
      ∑ i ∈ range N,
        2 *
          (qTerm c i ^ 2 / (1 + qTerm c i * tHi) ^ 2 -
            pTerm c i ^ 2 / (1 + pTerm c i * tLo) ^ 2)
        ≤
      ∑ i ∈ range N,
        2 *
          (qTerm c i ^ 2 / (1 + qTerm c i * u) ^ 2 -
            pTerm c i ^ 2 / (1 + pTerm c i * u) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hp : 0 ≤ pTerm c i := pTerm_nonneg hc i
    have hq : 0 ≤ qTerm c i := qTerm_nonneg hc i
    have hqBase : 1 + qTerm c i * u ≤ 1 + qTerm c i * tHi := by
      have hmul : qTerm c i * u ≤ qTerm c i * tHi := mul_le_mul_of_nonneg_left hu.2 hq
      linarith
    have hqUNonneg : 0 ≤ 1 + qTerm c i * u := by
      nlinarith
    have hqHiNonneg : 0 ≤ 1 + qTerm c i * tHi := by
      nlinarith
    have hqSq : (1 + qTerm c i * u) ^ 2 ≤ (1 + qTerm c i * tHi) ^ 2 := by
      apply sq_le_sq.2
      simpa [abs_of_nonneg hqUNonneg, abs_of_nonneg hqHiNonneg] using hqBase
    have hqInv : 1 / (1 + qTerm c i * tHi) ^ 2 ≤ 1 / (1 + qTerm c i * u) ^ 2 := by
      exact one_div_le_one_div_of_le (by positivity) hqSq
    have hqTerm :
        qTerm c i ^ 2 / (1 + qTerm c i * tHi) ^ 2 ≤
          qTerm c i ^ 2 / (1 + qTerm c i * u) ^ 2 := by
      have hq2 : 0 ≤ qTerm c i ^ 2 := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hqInv hq2
    have hpBase : 1 + pTerm c i * tLo ≤ 1 + pTerm c i * u := by
      have hmul : pTerm c i * tLo ≤ pTerm c i * u := mul_le_mul_of_nonneg_left hu.1 hp
      linarith
    have hpLoNonneg : 0 ≤ 1 + pTerm c i * tLo := by
      nlinarith
    have hpUNonneg : 0 ≤ 1 + pTerm c i * u := by
      nlinarith
    have hpSq : (1 + pTerm c i * tLo) ^ 2 ≤ (1 + pTerm c i * u) ^ 2 := by
      apply sq_le_sq.2
      simpa [abs_of_nonneg hpLoNonneg, abs_of_nonneg hpUNonneg] using hpBase
    have hpInv : 1 / (1 + pTerm c i * u) ^ 2 ≤ 1 / (1 + pTerm c i * tLo) ^ 2 := by
      exact one_div_le_one_div_of_le (by positivity) hpSq
    have hpTerm :
        pTerm c i ^ 2 / (1 + pTerm c i * u) ^ 2 ≤
          pTerm c i ^ 2 / (1 + pTerm c i * tLo) ^ 2 := by
      have hp2 : 0 ≤ pTerm c i ^ 2 := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hpInv hp2
    nlinarith
  dsimp [logDerivSqSlopeLower, logDerivSqSlope]
  linarith

theorem logDerivSqBoxLower_le
    {c tLo tHi u : ℝ}
    (hc : 0 ≤ c)
    (htLo : 0 ≤ tLo)
    (htLoHi : tLo ≤ tHi)
    (hu : u ∈ Icc tLo tHi)
    (N : Nat := defaultTerms) :
    logDerivSqBoxLower c tLo tHi N ≤ logDerivSq c u N := by
  let m := min (logDerivSqSlopeLower c tLo tHi N) 0
  have hm_nonpos : m ≤ 0 := min_le_right _ _
  have hmono : MonotoneOn (fun x => logDerivSq c x N - m * x) (Icc tLo tHi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact ((hasDerivAt_logDerivSq hc (le_trans htLo hx.1) N).sub
        ((hasDerivAt_id x).const_mul m)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hasDerivAt_logDerivSq hc (le_trans htLo hx.1.le) N).sub
        ((hasDerivAt_id x).const_mul m)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := le_trans htLo hx.1.le
      have hm_le :
          m ≤ logDerivSqSlope c x N := by
        exact le_trans (min_le_left _ _)
          (logDerivSqSlopeLower_le hc htLo htLoHi ⟨hx.1.le, hx.2.le⟩ N)
      have hder :
          deriv (fun y => logDerivSq c y N - m * y) x =
            logDerivSqSlope c x N - m := by
        simpa [sub_eq_add_neg, m, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_logDerivSq hc hx0 N).sub ((hasDerivAt_id x).const_mul m)).deriv)
      linarith
  have hstart : tLo ∈ Icc tLo tHi := ⟨le_rfl, htLoHi⟩
  have hmonoEval := hmono hstart hu hu.1
  have hu_term : (tHi - tLo) * m ≤ (u - tLo) * m := by
    have hdiff : u - tLo ≤ tHi - tLo := by
      exact sub_le_sub_right hu.2 tLo
    exact mul_le_mul_of_nonpos_right hdiff hm_nonpos
  dsimp [logDerivSqBoxLower]
  change logDerivSq c tLo N + (tHi - tLo) * m ≤ logDerivSq c u N
  have haff : logDerivSq c tLo N + (u - tLo) * m ≤ logDerivSq c u N := by
    nlinarith
  linarith

theorem logNormTruncSq_monotoneOn
    {c tLo tHi : ℝ}
    (hc : 0 ≤ c)
    (htLo : 0 ≤ tLo)
    (htLoHi : tLo ≤ tHi)
    (N : Nat := defaultTerms)
    (hbox : 0 ≤ logDerivSqBoxLower c tLo tHi N) :
    MonotoneOn (fun t => logNormTruncSq c t N) (Icc tLo tHi) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx
    exact (hasDerivAt_logNormTruncSq hc (le_trans htLo hx.1) N).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_logNormTruncSq hc (le_trans htLo hx.1.le) N).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := le_trans htLo hx.1.le
    have hder : deriv (fun u => logNormTruncSq c u N) x = logDerivSq c x N := by
      simpa using (hasDerivAt_logNormTruncSq hc hx0 N).deriv
    have hbound :
        logDerivSqBoxLower c tLo tHi N ≤ logDerivSq c x N := by
      exact logDerivSqBoxLower_le hc htLo htLoHi ⟨hx.1.le, hx.2.le⟩ N
    linarith

theorem normTruncSq_monotoneOn
    {c tLo tHi : ℝ}
    (hc : 0 ≤ c)
    (htLo : 0 ≤ tLo)
    (htLoHi : tLo ≤ tHi)
    (N : Nat := defaultTerms)
    (hbox : 0 ≤ logDerivSqBoxLower c tLo tHi N) :
    MonotoneOn (fun t => normTruncSq c t N) (Icc tLo tHi) := by
  intro x hx y hy hxy
  have hlogMono := logNormTruncSq_monotoneOn hc htLo htLoHi N hbox
  have hx0 : 0 ≤ x := le_trans htLo hx.1
  have hy0 : 0 ≤ y := le_trans htLo hy.1
  have hlog :
      logNormTruncSq c x N ≤ logNormTruncSq c y N := hlogMono hx hy hxy
  rw [logNormTruncSq_eq_log_normTruncSq hc hx0 N, logNormTruncSq_eq_log_normTruncSq hc hy0 N] at hlog
  by_contra hxy'
  have hyx : normTruncSq c y N < normTruncSq c x N := lt_of_not_ge hxy'
  have hxpos : 0 < normTruncSq c x N := normTruncSq_pos hc hx0 N
  have hypos : 0 < normTruncSq c y N := normTruncSq_pos hc hy0 N
  have hlt : Real.log (normTruncSq c y N) < Real.log (normTruncSq c x N) := by
    exact Real.log_lt_log hypos hyx
  linarith

theorem paperFactor_pos
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : 0 < ρ)
    (n : Nat) :
    0 < paperFactor c ρ n := by
  dsimp [paperFactor]
  positivity

theorem factor_identity_core
    {c y a : ℝ}
    (hc : 0 < c)
    (hy : 0 < y)
    (ha : 0 ≤ a) :
    let t := ((y - c) ^ 2) / (4 * c * y)
    ((1 + y * a) * (1 + c ^ 2 * a / y) * (1 + c * a) ^ 2) /
        ((1 + y * a / c) * (1 + c * a / y) * (1 + a) ^ 2) =
      ((1 + c * a) / (1 + a)) ^ 4 * (1 + phi (c * a) * t) / (1 + phi a * t) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h1a : 0 < 1 + a := by linarith
  have h1ca : 0 < 1 + c * a := by
    nlinarith [mul_nonneg hc.le ha]
  have h1ya : 0 < 1 + y * a := by
    nlinarith [mul_nonneg hy.le ha]
  have h1c2ay : 0 < 1 + c ^ 2 * a / y := by
    have hnonneg : 0 ≤ c ^ 2 * a / y := by
      positivity
    linarith
  have h1yac : 0 < 1 + y * a / c := by
    have hnonneg : 0 ≤ y * a / c := by
      positivity
    linarith
  have h1cay : 0 < 1 + c * a / y := by
    have hnonneg : 0 ≤ c * a / y := by
      positivity
    linarith
  have hden1 : (1 + y * a / c) * (1 + c * a / y) * (1 + a) ^ 2 ≠ 0 := by
    positivity
  have hden2 : 1 + phi a * (((y - c) ^ 2) / (4 * c * y)) ≠ 0 := by
    have hnonneg : 0 ≤ phi a * (((y - c) ^ 2) / (4 * c * y)) := by
      have hphi : 0 ≤ phi a := by
        dsimp [phi]
        positivity
      have ht : 0 ≤ ((y - c) ^ 2) / (4 * c * y) := by
        positivity
      nlinarith
    linarith
  dsimp [phi]
  field_simp [hc0, hy0, hden1, hden2]
  ring

theorem paperFactor_sq_eq
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : 0 < ρ)
    (n : Nat) :
    (paperFactor c ρ n) ^ 2 =
      ((1 + c ^ (2 * n + 2)) / (1 + c ^ (2 * n + 1))) ^ 8 *
        normFactor c (rhoToT c ρ) n := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  dsimp [paperFactor, normFactor, rhoToT, pTerm, qTerm, phi]
  field_simp [hc0, hρ0]
  ring

theorem prefactor_sq_eq
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : 0 < ρ) :
    (2 * ρ * (1 + c / ρ ^ 2)) ^ 2 = 16 * c * (1 + rhoToT c ρ) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  dsimp [rhoToT]
  field_simp [hc0, hρ0]
  ring

theorem paperTruncSq_eq_truncConst_mul_normTruncSq
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : 0 < ρ)
    (N : Nat := defaultTerms) :
    paperTruncSq c ρ N = truncConst c N * normTruncSq c (rhoToT c ρ) N := by
  dsimp [paperTruncSq, paperTrunc]
  rw [show 2 * ρ * (1 + c / ρ ^ 2) * ∏ i ∈ range N, paperFactor c ρ i =
      (2 * ρ * (1 + c / ρ ^ 2)) * ∏ i ∈ range N, paperFactor c ρ i by ring]
  rw [mul_pow, ← Finset.prod_pow]
  rw [prefactor_sq_eq hc hρ, truncConst, normTruncSq]
  have hprod :
      ∏ x ∈ range N, paperFactor c ρ x ^ 2 =
        ∏ x ∈ range N,
          (((1 + c ^ (2 * x + 2)) / (1 + c ^ (2 * x + 1))) ^ 8 *
            normFactor c (rhoToT c ρ) x) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [paperFactor_sq_eq hc hρ i]
  rw [hprod, Finset.prod_mul_distrib]
  ring

theorem constRatio_le_one
    {c : ℝ}
    (hc : 0 ≤ c)
    (hc1 : c ≤ 1)
    (n : Nat) :
    (1 + c ^ (2 * n + 2)) / (1 + c ^ (2 * n + 1)) ≤ 1 := by
  have hpow : c ^ (2 * n + 2) ≤ c ^ (2 * n + 1) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hc1
  have hden : 0 < 1 + c ^ (2 * n + 1) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

theorem paperFactor_le_one
    {c ρ : ℝ}
    (hc : 0 < c)
    (hc1 : c < 1)
    (hρ : 0 < ρ)
    (n : Nat) :
    paperFactor c ρ n ≤ 1 := by
  have hsq := paperFactor_sq_eq hc hρ n
  have hconst_nonneg :
      0 ≤ ((1 + c ^ (2 * n + 2)) / (1 + c ^ (2 * n + 1))) ^ 8 := by
    positivity
  have hconst_le :
      ((1 + c ^ (2 * n + 2)) / (1 + c ^ (2 * n + 1))) ^ 8 ≤ 1 := by
    exact pow_le_one₀ (by positivity) (constRatio_le_one hc.le hc1.le n)
  have ht : 0 ≤ rhoToT c ρ := rhoToT_nonneg hc hρ
  have hnorm_nonneg : 0 ≤ normFactor c (rhoToT c ρ) n := by
    dsimp [normFactor]
    positivity
  have hnorm_le : normFactor c (rhoToT c ρ) n ≤ 1 := by
    apply normFactor_le_one hc.le hc1.le
    exact ht
  have hsq_le : (paperFactor c ρ n) ^ 2 ≤ 1 := by
    rw [paperFactor_sq_eq hc hρ n]
    nlinarith
  have hpos : 0 < paperFactor c ρ n := paperFactor_pos hc hρ n
  nlinarith

theorem tprod_paperFactor_le_trunc
    {c ρ : ℝ}
    (hc : 0 < c)
    (hc1 : c < 1)
    (hρc : c ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (N : Nat)
    (hmul : Multipliable (paperFactor c ρ)) :
    ∏' n, paperFactor c ρ n ≤ ∏ i ∈ range N, paperFactor c ρ i := by
  have hρ : 0 < ρ := lt_of_lt_of_le hc hρc
  refine le_of_tendsto hmul.hasProd.tendsto_prod_nat ?_
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  rw [Finset.prod_range_add]
  have htail_le : ∏ i ∈ range m, paperFactor c ρ (N + i) ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro i hi
      exact le_of_lt (paperFactor_pos hc hρ (N + i))
    · intro i hi
      exact paperFactor_le_one hc hc1 hρ (N + i)
  have hprefix_nonneg : 0 ≤ ∏ i ∈ range N, paperFactor c ρ i := by
    exact Finset.prod_nonneg fun i hi => (paperFactor_pos hc hρ i).le
  calc
    (∏ x ∈ range N, paperFactor c ρ x) * ∏ x ∈ range m, paperFactor c ρ (N + x)
      ≤ (∏ x ∈ range N, paperFactor c ρ x) * 1 := by
          gcongr
    _ = ∏ x ∈ range N, paperFactor c ρ x := by ring

theorem paperK_le_trunc
    {K : ℝ → ℝ → ℝ}
    {c ρ : ℝ}
    (hPaper : PaperKFormula K c)
    (hc : 0 < c)
    (hc1 : c < 1)
    (hρ : ρ ∈ Icc c 1)
    (N : Nat := defaultTerms) :
    K c ρ ≤ paperTrunc c ρ N := by
  rcases hPaper ρ hρ with ⟨hmul, hEq⟩
  rw [hEq, paperTrunc]
  have hpref_nonneg : 0 ≤ 2 * ρ * (1 + c / ρ ^ 2) := by
    have hρpos : 0 < ρ := lt_of_lt_of_le hc hρ.1
    positivity
  exact mul_le_mul_of_nonneg_left
    (tprod_paperFactor_le_trunc hc hc1 hρ.1 hρ.2 N hmul) hpref_nonneg

theorem paperKsq_le_truncSq
    {K : ℝ → ℝ → ℝ}
    {c ρ : ℝ}
    (hPaper : PaperKFormula K c)
    (hc : 0 < c)
    (hc1 : c < 1)
    (hρ : ρ ∈ Icc c 1)
    (N : Nat := defaultTerms) :
    (K c ρ) ^ 2 ≤ paperTruncSq c ρ N := by
  have hle := paperK_le_trunc hPaper hc hc1 hρ N
  have hnonneg : 0 ≤ K c ρ := by
    rcases hPaper ρ hρ with ⟨hmul, hEq⟩
    rw [hEq]
    have hρpos : 0 < ρ := lt_of_lt_of_le hc hρ.1
    have htprod_nonneg : 0 ≤ ∏' n, paperFactor c ρ n := by
      refine ge_of_tendsto' hmul.hasProd.tendsto_prod_nat ?_
      intro n
      exact Finset.prod_nonneg fun i hi => (paperFactor_pos hc hρpos i).le
    exact mul_nonneg (by positivity) htprod_nonneg
  have htrunc_nonneg : 0 ≤ paperTrunc c ρ N := by
    have hρpos : 0 < ρ := lt_of_lt_of_le hc hρ.1
    dsimp [paperTrunc]
    have hprod_nonneg : 0 ≤ ∏ i ∈ range N, paperFactor c ρ i := by
      exact Finset.prod_nonneg fun i hi => (paperFactor_pos hc hρpos i).le
    exact mul_nonneg (by positivity) hprod_nonneg
  exact by
    dsimp [paperTruncSq]
    nlinarith

theorem paperTruncSq_le_anchorQ
    {c lo hi : ℚ}
    {ρ : ℝ}
    (hc : 0 < (c : ℝ))
    (hclo : c ≤ lo)
    (hhi1 : hi ≤ 1)
    (hρ : ρ ∈ Icc (lo : ℝ) (hi : ℝ))
    (N : Nat := defaultTerms)
    (hbox : 0 ≤ logDerivSqBoxLower (c : ℝ) (tLoQ c lo hi) (tHiQ c lo hi) N) :
    paperTruncSq (c : ℝ) ρ N ≤ paperTruncSq (c : ℝ) (anchorQ c lo hi : ℝ) N := by
  have hlohi : (lo : ℝ) ≤ hi := le_trans hρ.1 hρ.2
  have hloPos : 0 < (lo : ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hclo)
  have hAnchorPos : 0 < (anchorQ c lo hi : ℝ) := by
    by_cases h : rhoToTQ c lo ≤ rhoToTQ c hi
    · have hhiPos : 0 < (hi : ℝ) := lt_of_lt_of_le hloPos hlohi
      simpa [anchorQ, h] using hhiPos
    · simpa [anchorQ, h] using hloPos
  have hloMem : (lo : ℝ) ∈ Icc (lo : ℝ) (hi : ℝ) := ⟨le_rfl, hlohi⟩
  have htLoNonneg : 0 ≤ (tLoQ c lo hi : ℝ) := by
    have htLoNonnegQ : 0 ≤ tLoQ c lo hi := by
      have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
      have hlohiQ : lo ≤ hi := by exact_mod_cast hlohi
      exact tLoQ_nonneg hcQ hclo hlohiQ
    exact_mod_cast htLoNonnegQ
  have htLoHi : (tLoQ c lo hi : ℝ) ≤ (tHiQ c lo hi : ℝ) := by
    exact le_trans (tLoQ_le_rhoToT hc hclo hloMem) (rhoToT_le_tHiQ hc hclo hloMem)
  have hρt :
      rhoToT (c : ℝ) ρ ∈ Icc (tLoQ c lo hi : ℝ) (tHiQ c lo hi : ℝ) := by
    exact ⟨tLoQ_le_rhoToT hc hclo hρ, rhoToT_le_tHiQ hc hclo hρ⟩
  have hmono := normTruncSq_monotoneOn hc.le htLoNonneg htLoHi N hbox
  have hnorm :
      normTruncSq (c : ℝ) (rhoToT (c : ℝ) ρ) N ≤
        normTruncSq (c : ℝ) (tHiQ c lo hi : ℝ) N := by
    exact hmono hρt ⟨htLoHi, le_rfl⟩ hρt.2
  have hconstNonneg : 0 ≤ truncConst (c : ℝ) N := by
    dsimp [truncConst]
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.prod_nonneg ?_
      intro i hi
      positivity
  calc
    paperTruncSq (c : ℝ) ρ N =
        truncConst (c : ℝ) N * normTruncSq (c : ℝ) (rhoToT (c : ℝ) ρ) N := by
          rw [paperTruncSq_eq_truncConst_mul_normTruncSq hc (lt_of_lt_of_le hc (le_trans (by exact_mod_cast hclo) hρ.1)) N]
    _ ≤ truncConst (c : ℝ) N * normTruncSq (c : ℝ) (tHiQ c lo hi : ℝ) N := by
          exact mul_le_mul_of_nonneg_left hnorm hconstNonneg
    _ = paperTruncSq (c : ℝ) (anchorQ c lo hi : ℝ) N := by
          rw [paperTruncSq_eq_truncConst_mul_normTruncSq hc hAnchorPos N, rhoToT_anchor_eq_tHiQ]

theorem paperKsq_le_of_boxKernelValidQ
    {K : ℝ → ℝ → ℝ}
    {c lo hi kSqUpper : ℚ}
    {ρ : ℝ}
    (hPaper : PaperKFormula K (c : ℝ))
    (hc : 0 < (c : ℝ))
    (hc1 : (c : ℝ) < 1)
    (hclo : c ≤ lo)
    (hhi1 : hi ≤ 1)
    (hρ : ρ ∈ Icc (lo : ℝ) (hi : ℝ))
    (N : Nat := defaultTerms)
    (hbox : boxKernelValidQ c lo hi kSqUpper N) :
    (K (c : ℝ) ρ) ^ 2 ≤ (kSqUpper : ℝ) := by
  rcases hbox with ⟨hlogQ, hanchorQ⟩
  have hρPaper : ρ ∈ Icc (c : ℝ) 1 := by
    exact ⟨le_trans (by exact_mod_cast hclo) hρ.1, le_trans hρ.2 (by exact_mod_cast hhi1)⟩
  have hpaper : (K (c : ℝ) ρ) ^ 2 ≤ paperTruncSq (c : ℝ) ρ N := by
    exact paperKsq_le_truncSq hPaper hc hc1 hρPaper N
  have hlog : 0 ≤ logDerivSqBoxLower (c : ℝ) (tLoQ c lo hi) (tHiQ c lo hi) N := by
    have hlogR : (0 : ℝ) < logDerivSqBoxLower (c : ℝ) (tLoQ c lo hi) (tHiQ c lo hi) N := by
      have hlogRQ : (0 : ℝ) < ((logDerivSqBoxLowerQ c lo hi N : ℚ) : ℝ) := by
        exact_mod_cast hlogQ
      simpa [logDerivSqBoxLowerQ_cast] using hlogRQ
    linarith
  have htrunc :
      paperTruncSq (c : ℝ) ρ N ≤ paperTruncSq (c : ℝ) (anchorQ c lo hi : ℝ) N := by
    exact paperTruncSq_le_anchorQ hc hclo hhi1 hρ N hlog
  have hanchor :
      paperTruncSq (c : ℝ) (anchorQ c lo hi : ℝ) N ≤ (kSqUpper : ℝ) := by
    have hanchorR :
        ((paperTruncSqQ c (anchorQ c lo hi) N : ℚ) : ℝ) ≤ (kSqUpper : ℝ) := by
      exact_mod_cast hanchorQ
    simpa [paperTruncSqQ_cast] using hanchorR
  exact hpaper.trans (htrunc.trans hanchor)

end WangKernelExact

end KorenblumPaper
