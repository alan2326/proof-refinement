import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge

/-!
# Sprint 083 / V64 — `Real.sqrt`-pinned τ-window endpoints

This file is a per-candidate derived-theorem file (per
`AGENT_BRIEF.md` lines 154–204) shipping the sqrt-pinned τ-window
endpoints required by V64's `h_witness` construction at
`c = 35646/100000` for the
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer.

Contents are `def`s (the two endpoints, parametric in `c`) plus
`theorem`s discharging:

  * the four τ-bound polynomial inequalities of the `h_witness`
    predicate at the canonical breakpoints `tau(1) = 3/4` and
    `tau(2) = 8/9`,
  * the geometric ordering `c < ρStart₁ ≤ ρStop₁` and a
    `c`-specific upper bound `ρ_meet_sqrt c < 999999/1000000`
    at the candidate's exact `c = 35646/100000`.

No `axiom`s, no `sorry`s, no `Section2Assumptions` field
extensions. Every theorem is a self-contained Lean derivation
using `Real.sq_sqrt`, `Real.sqrt_lt_sqrt`, and rational
arithmetic.
-/

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

open KorenblumPaper

/-! ## Endpoint definitions -/

/-- The lower endpoint of window 1: `c · sqrt(9/8)`. Pinned so that
`ρStart₁² = 9 c² / 8`, which gives `c² / ρStart₁² = 8/9 = tau(2)`. -/
def ρStart₁_sqrt (c : ℝ) : ℝ := c * Real.sqrt (9 / 8)

/-- The shared meeting point of the two windows:
`c · sqrt(4/3)`. Pinned so that `ρ_meet_sqrt² = 4 c² / 3`, which
gives `c² / ρ_meet_sqrt² = 3/4 = tau(1)`. Both `ρStop₁` and
`ρStart₂` equal this value via the adjacency constraint. -/
def ρ_meet_sqrt (c : ℝ) : ℝ := c * Real.sqrt (4 / 3)

/-! ## Square-root squaring lemmas (private helpers) -/

/-- `(c · sqrt(9/8))² = c² · 9/8`. -/
theorem ρStart₁_sqrt_sq (c : ℝ) :
    (ρStart₁_sqrt c) ^ 2 = c ^ 2 * (9 / 8) := by
  unfold ρStart₁_sqrt
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 8)]

/-- `(c · sqrt(4/3))² = c² · 4/3`. -/
theorem ρ_meet_sqrt_sq (c : ℝ) :
    (ρ_meet_sqrt c) ^ 2 = c ^ 2 * (4 / 3) := by
  unfold ρ_meet_sqrt
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3)]

/-! ## τ-bound polynomial discharges at sqrt endpoints -/

/-- `tau 1 ≤ c² / ρ_meet_sqrt² c` — actually equality, since
`ρ_meet_sqrt c² = c² · 4/3` and `tau 1 = 3/4`. Side condition
`0 < c` ensures `c² ≠ 0`. -/
theorem tau_one_le_c_sq_div_meet_sq_sqrt {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 1 ≤ c ^ 2 / (ρ_meet_sqrt c) ^ 2 := by
  rw [ρ_meet_sqrt_sq]
  -- Now goal: tau 1 ≤ c² / (c² · 4/3) = 3/4 = tau 1
  have hc_sq_pos : 0 < c ^ 2 := by positivity
  have hc_sq_ne : c ^ 2 ≠ 0 := ne_of_gt hc_sq_pos
  have heq : c ^ 2 / (c ^ 2 * (4 / 3)) = 3 / 4 := by
    field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- `c² / ρStart₁_sqrt² c ≤ tau 2` — actually equality, since
`ρStart₁_sqrt c² = c² · 9/8` and `tau 2 = 8/9`. -/
theorem c_sq_div_start1_sq_le_tau_two_sqrt {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (ρStart₁_sqrt c) ^ 2 ≤ OneModeTail.tau 2 := by
  rw [ρStart₁_sqrt_sq]
  have hc_sq_pos : 0 < c ^ 2 := by positivity
  have hc_sq_ne : c ^ 2 ≠ 0 := ne_of_gt hc_sq_pos
  have heq : c ^ 2 / (c ^ 2 * (9 / 8)) = 8 / 9 := by
    field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- `c² / ρ_meet_sqrt² c ≤ tau 1` — equality at the
canonical breakpoint, used as the j₂=1 window's upper τ-bound
(at `ρStart₂ = ρ_meet_sqrt c` via adjacency). -/
theorem c_sq_div_meet_sq_le_tau_one_sqrt {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (ρ_meet_sqrt c) ^ 2 ≤ OneModeTail.tau 1 := by
  rw [ρ_meet_sqrt_sq]
  have hc_sq_pos : 0 < c ^ 2 := by positivity
  have hc_sq_ne : c ^ 2 ≠ 0 := ne_of_gt hc_sq_pos
  have heq : c ^ 2 / (c ^ 2 * (4 / 3)) = 3 / 4 := by
    field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- `tau 0 = 0 ≤ c² / ρStop₂²` for any `0 ≤ ρStop₂`. -/
theorem tau_zero_le_c_sq_div_stop2_sq {c ρStop₂ : ℝ}
    (hc : 0 ≤ c) :
    OneModeTail.tau 0 ≤ c ^ 2 / ρStop₂ ^ 2 := by
  unfold OneModeTail.tau
  have hzero : ((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 2) / (((0 : ℕ) : ℝ) + 1) ^ 2 = 0 := by
    norm_num
  rw [hzero]
  positivity

/-! ## Ordering lemmas at the sqrt endpoints -/

/-- `1 < Real.sqrt (9/8)`: takes `1 = sqrt 1 < sqrt (9/8)` via
`Real.sqrt_lt_sqrt`. -/
theorem one_lt_sqrt_nine_eighths : (1 : ℝ) < Real.sqrt (9 / 8) := by
  have h : Real.sqrt 1 < Real.sqrt (9 / 8) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa [Real.sqrt_one] using h

/-- `Real.sqrt (9/8) ≤ Real.sqrt (4/3)` from `9/8 ≤ 4/3` via
`Real.sqrt_le_sqrt`. -/
theorem sqrt_nine_eighths_le_sqrt_four_thirds :
    Real.sqrt (9 / 8) ≤ Real.sqrt (4 / 3) :=
  Real.sqrt_le_sqrt (by norm_num)

/-- For `0 < c`, `c < ρStart₁_sqrt c` since `1 < sqrt(9/8)`. -/
theorem c_lt_ρStart₁_sqrt {c : ℝ} (hc : 0 < c) :
    c < ρStart₁_sqrt c := by
  unfold ρStart₁_sqrt
  have : c * 1 < c * Real.sqrt (9 / 8) :=
    mul_lt_mul_of_pos_left one_lt_sqrt_nine_eighths hc
  simpa using this

/-- For `0 ≤ c`, `ρStart₁_sqrt c ≤ ρ_meet_sqrt c`. -/
theorem ρStart₁_sqrt_le_ρ_meet_sqrt {c : ℝ} (hc : 0 ≤ c) :
    ρStart₁_sqrt c ≤ ρ_meet_sqrt c := by
  unfold ρStart₁_sqrt ρ_meet_sqrt
  exact mul_le_mul_of_nonneg_left sqrt_nine_eighths_le_sqrt_four_thirds hc

/-! ## c-specific upper bound on `ρ_meet_sqrt c` at `c = 35646/100000` -/

/-- `Real.sqrt (4/3) ≤ 1156/1000`: a clean rational upper bound,
since `4/3 = 1333333.../1000000 < 1336336/1000000 = (1156/1000)²`. -/
theorem sqrt_four_thirds_le_rational : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
  have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
  -- Compare `4/3 ≤ (1156/1000)²` and apply `Real.sqrt_le_sqrt`
  -- followed by `Real.sqrt_sq`.
  have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
  have hsqrt_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
    Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hpos] at hsqrt_le

/-- For the candidate's exact `c = 35646/100000`,
`ρ_meet_sqrt c < 999999/1000000`. Proof: `c · sqrt(4/3) ≤ c · 1156/1000`
plus `(35646/100000) · (1156/1000) < 999999/1000000` by rational
arithmetic. -/
theorem ρ_meet_sqrt_lt_one_for_target_c :
    ρ_meet_sqrt (35646 / 100000) < (999999 / 1000000 : ℝ) := by
  unfold ρ_meet_sqrt
  have hc_pos : (0 : ℝ) < 35646 / 100000 := by norm_num
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 :=
    sqrt_four_thirds_le_rational
  have h1 : (35646 / 100000 : ℝ) * Real.sqrt (4 / 3) ≤
      (35646 / 100000 : ℝ) * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hc_pos)
  have h2 : (35646 / 100000 : ℝ) * (1156 / 1000) < 999999 / 1000000 := by
    norm_num
  linarith

/-! ## Mode index facts -/

theorem one_le_two : (1 : ℕ) ≤ 2 := by decide

theorem one_le_one : (1 : ℕ) ≤ 1 := le_refl 1

end ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints
