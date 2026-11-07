-- Sprint 088 / V66 — sqrt-pinned seven-window endpoint properties.
--
-- Per-candidate derived-theorem file (`AGENT_BRIEF.md` lines 154-204) shipping
-- the τ-bound and ordering theorems required by V66's `h_witness` construction
-- at `c = v66CValue = 356562/1000000` for the
-- `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` reducer
-- (sprint 086) instantiated at `n = 6` (i.e. `Fin 7` windows).
--
-- The seven windows are split into three Branch.one fallback boxes
-- (`i ∈ {0, 1, 2}`) and four per-mode tail windows (`i ∈ {3, 4, 5, 6}` for
-- j = 4, 3, 2, 1) by `v66SevenWindowKind` (defined in
-- `Proof/Reduction.lean`). The endpoints are pinned at sqrt-rationals
-- `c · sqrt(50/49), c · sqrt(36/35), c · sqrt(25/24), c · sqrt(16/15),
-- c · sqrt(9/8), c · sqrt(4/3)` plus the boxA1 lower offset
-- `c · (1 + 1e-6)` and the mode1 upper limit `999999/1000000`.
--
-- Contents (no `axiom`s, no `sorry`s):
--
--   1. τ-bound polynomial discharges at the four mode endpoints, mirroring
--      V64/TauWindowEndpoints. Each pair is `field_simp + norm_num` under
--      `Real.sq_sqrt`:
--        - mode4 window  (i = 3, j = 4):
--          `tau 3 ≤ c²/ρStop² = 15/16 = tau 3`
--          `c²/ρStart² = 24/25 = tau 4`
--        - mode3 window  (i = 4, j = 3):
--          `tau 2 ≤ c²/ρStop² = 8/9 = tau 2`
--          `c²/ρStart² = 15/16 = tau 3`
--        - mode2 window  (i = 5, j = 2):
--          `tau 1 ≤ c²/ρStop² = 3/4 = tau 1`
--          `c²/ρStart² = 8/9 = tau 2`
--        - mode1 window  (i = 6, j = 1):
--          `tau 0 ≤ c²/ρStop²` (positivity)
--          `c²/ρStart² = 3/4 = tau 1`
--   2. Geometric ordering at `c = v66CValue`. Adjacency is by definitional
--      `rfl`, the seven-way ordering chains through `Real.sqrt`-monotonicity,
--      and `c < ρStart 0` plus `ρStop 6 < 1` are by rational arithmetic.
--   3. `branchSplit` constraints for the three Branch.one windows: each
--      `ρStop i ≤ branchSplit c = c · sqrt(4/3)` for `i ∈ {0, 1, 2}` is a
--      `mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) c_nonneg` invocation.
--   4. The boxA0 lower bound `c · (1 + 1e-6) > c` plus the cross-window
--      bounds needed by V66.lean (e.g. `c ≤ ρStart i` for any `i`).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints

open KorenblumPaper
open ProofRefinement.Korenblum

/-! ## v66CValue arithmetic facts -/

theorem v66CValue_pos : (0 : ℝ) < v66CValue := by
  unfold v66CValue; norm_num

theorem v66CValue_nonneg : (0 : ℝ) ≤ v66CValue := le_of_lt v66CValue_pos

theorem v66CValue_lt_one : v66CValue < (1 : ℝ) := by
  unfold v66CValue; norm_num

theorem v66CValue_sq_pos : (0 : ℝ) < v66CValue ^ 2 := by
  have h := v66CValue_pos; positivity

theorem v66CValue_sq_ne : v66CValue ^ 2 ≠ 0 := ne_of_gt v66CValue_sq_pos

/-! ## Square-root squaring lemmas -/

theorem sq_c_mul_sqrt {c r : ℝ} (hr : (0 : ℝ) ≤ r) :
    (c * Real.sqrt r) ^ 2 = c ^ 2 * r := by
  rw [mul_pow, Real.sq_sqrt hr]

/-! ## Mode endpoint τ-discharges (templated on V64/TauWindowEndpoints) -/

/-- mode4 window upper τ-bound:
`tau 3 ≤ c² / (c · sqrt(16/15))² = 15/16 = tau 3`. -/
theorem tau_three_le_c_sq_div_stop_mode4 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 3 ≤ c ^ 2 / (c * Real.sqrt (16 / 15)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 16 / 15)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (16 / 15)) = 15 / 16 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode4 window lower τ-bound:
`c² / (c · sqrt(25/24))² = 24/25 = tau 4 ≤ tau 4`. -/
theorem c_sq_div_start_mode4_le_tau_four {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (25 / 24)) ^ 2 ≤ OneModeTail.tau 4 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 25 / 24)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (25 / 24)) = 24 / 25 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode3 window upper τ-bound:
`tau 2 ≤ c² / (c · sqrt(9/8))² = 8/9 = tau 2`. -/
theorem tau_two_le_c_sq_div_stop_mode3 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 2 ≤ c ^ 2 / (c * Real.sqrt (9 / 8)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 8)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (9 / 8)) = 8 / 9 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode3 window lower τ-bound:
`c² / (c · sqrt(16/15))² = 15/16 = tau 3 ≤ tau 3`. -/
theorem c_sq_div_start_mode3_le_tau_three {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (16 / 15)) ^ 2 ≤ OneModeTail.tau 3 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 16 / 15)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (16 / 15)) = 15 / 16 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode2 window upper τ-bound:
`tau 1 ≤ c² / (c · sqrt(4/3))² = 3/4 = tau 1`. -/
theorem tau_one_le_c_sq_div_stop_mode2 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 1 ≤ c ^ 2 / (c * Real.sqrt (4 / 3)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (4 / 3)) = 3 / 4 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode2 window lower τ-bound:
`c² / (c · sqrt(9/8))² = 8/9 = tau 2 ≤ tau 2`. -/
theorem c_sq_div_start_mode2_le_tau_two {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (9 / 8)) ^ 2 ≤ OneModeTail.tau 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 8)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (9 / 8)) = 8 / 9 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode1 window upper τ-bound: `tau 0 = 0 ≤ c² / ρStop²` for any nonneg c
and any ρStop. -/
theorem tau_zero_le_c_sq_div_stop_mode1 {c ρStop : ℝ} :
    OneModeTail.tau 0 ≤ c ^ 2 / ρStop ^ 2 := by
  unfold OneModeTail.tau
  have hzero : ((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 2) / (((0 : ℕ) : ℝ) + 1) ^ 2 = 0 := by
    norm_num
  rw [hzero]
  positivity

/-- mode1 window lower τ-bound:
`c² / (c · sqrt(4/3))² = 3/4 = tau 1 ≤ tau 1`. -/
theorem c_sq_div_start_mode1_le_tau_one {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (4 / 3)) ^ 2 ≤ OneModeTail.tau 1 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (4 / 3)) = 3 / 4 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-! ## Sqrt monotonicity helpers (1 ≤ sqrt of a rational ≥ 1) -/

/-- `1 ≤ Real.sqrt r` whenever `1 ≤ r`. -/
theorem one_le_sqrt_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    (1 : ℝ) ≤ Real.sqrt r := by
  have h : Real.sqrt 1 ≤ Real.sqrt r := Real.sqrt_le_sqrt hr
  simpa [Real.sqrt_one] using h

/-- `Real.sqrt r ≤ Real.sqrt s` whenever `r ≤ s`. -/
theorem sqrt_le_sqrt_of_le {r s : ℝ} (hrs : r ≤ s) :
    Real.sqrt r ≤ Real.sqrt s := Real.sqrt_le_sqrt hrs

/-! ## Adjacency (definitional `rfl`) -/

/-- The six adjacency equations of the seven-window split: `ρStop i =
ρStart (i+1)` for `i ∈ {0, 1, 2, 3, 4, 5}`. By definitional `rfl` thanks
to sprint 087's choice of endpoints. -/
theorem v66_adj (i : Fin 6) :
    v66SevenWindowStop i.castSucc = v66SevenWindowStart i.succ := by
  fin_cases i <;> rfl

/-! ## Per-window start/stop ordering (`ρStart i ≤ ρStop i`) -/

/-- For each i, `ρStart i ≤ ρStop i`. By case analysis on `i`; each case
reduces to a sqrt-monotonicity step or a rational arithmetic check. -/
theorem v66_start_le_stop (i : Fin 7) :
    v66SevenWindowStart i ≤ v66SevenWindowStop i := by
  have hcnn := v66CValue_nonneg
  fin_cases i
  all_goals (unfold v66SevenWindowStart v66SevenWindowStop)
  · -- i = 0: c · (1 + 1/1e6) ≤ c · sqrt(50/49)
    apply mul_le_mul_of_nonneg_left _ hcnn
    -- 1 + 1/1e6 ≤ sqrt(50/49). Suffices (1+1/1e6)² ≤ 50/49.
    have hbase : (1 : ℝ) + 1/1000000 ≤ Real.sqrt (50/49) := by
      have hSq : ((1 : ℝ) + 1/1000000) ^ 2 ≤ 50/49 := by norm_num
      have hsnn : (0 : ℝ) ≤ (1 : ℝ) + 1/1000000 := by norm_num
      have hsq_le : Real.sqrt (((1 : ℝ) + 1/1000000) ^ 2) ≤ Real.sqrt (50/49) :=
        Real.sqrt_le_sqrt hSq
      rwa [Real.sqrt_sq hsnn] at hsq_le
    exact hbase
  · -- i = 1: c · sqrt(50/49) ≤ c · sqrt(36/35)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 2
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 3
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 4
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 5
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 6: c · sqrt(4/3) ≤ 999999/1000000
    -- v66CValue = 356562/1000000.
    -- c · sqrt(4/3) ≤ c · 1156/1000 ≤ (356562/1000000) · 1156/1000 ≤ 999999/1000000
    have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (4 / 3) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 999999 / 1000000 := by
      unfold v66CValue; norm_num
    linarith

/-! ## Window upper bound `ρStop i < 1` -/

/-- For each `i`, `ρStop i < 1`. -/
theorem v66_stop_lt_one (i : Fin 7) :
    v66SevenWindowStop i < (1 : ℝ) := by
  have hcnn := v66CValue_nonneg
  -- Claim: every ρStop i ≤ ρStop 6 = 999999/1000000 < 1.
  fin_cases i
  all_goals (unfold v66SevenWindowStop)
  · -- ρStop 0 = c · sqrt(50/49) < 1
    -- c < 1 and sqrt(50/49) ≤ sqrt(4/3), so c · sqrt(50/49) ≤ c · sqrt(4/3)
    -- ≤ c · 1156/1000, and (356562/1000000) · 1156/1000 < 1.
    have hsqrt_le : Real.sqrt (50 / 49) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (50 / 49 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (50 / 49) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (50 / 49) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 1 = c · sqrt(36/35) < 1
    have hsqrt_le : Real.sqrt (36 / 35) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (36 / 35 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (36 / 35) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (36 / 35) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 2 = c · sqrt(25/24) < 1
    have hsqrt_le : Real.sqrt (25 / 24) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (25 / 24 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (25 / 24) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (25 / 24) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 3 = c · sqrt(16/15) < 1
    have hsqrt_le : Real.sqrt (16 / 15) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (16 / 15 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (16 / 15) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (16 / 15) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 4 = c · sqrt(9/8) < 1
    have hsqrt_le : Real.sqrt (9 / 8) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (9 / 8 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (9 / 8) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (9 / 8) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 5 = c · sqrt(4/3) < 1
    have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v66CValue * Real.sqrt (4 / 3) ≤ v66CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
    linarith
  · -- ρStop 6 = 999999/1000000 < 1
    norm_num

/-! ## Lower bound `c < ρStart i` -/

/-- For each `i`, `v66CValue < ρStart i`. The base case `i = 0` has
`ρStart 0 = c · (1 + 1/1e6)`, strictly above `c`. The cases `i ≥ 1`
follow from `ρStart 0 ≤ ρStart i` (because the seven `ρStart`s are
non-decreasing from `c·(1+1e-6)` through `c·sqrt(4/3)`). -/
theorem v66_c_lt_start (i : Fin 7) :
    v66CValue < v66SevenWindowStart i := by
  have hc_pos := v66CValue_pos
  have hcnn := v66CValue_nonneg
  -- Prove `v66CValue < v66SevenWindowStart 0` first, then chain via sqrt.
  have h_base : v66CValue < v66SevenWindowStart 0 := by
    unfold v66SevenWindowStart
    have h1 : v66CValue * 1 < v66CValue * (1 + 1 / 1000000) := by
      have hpos : (0 : ℝ) < 1 / 1000000 := by norm_num
      have hgt : (1 : ℝ) < 1 + 1 / 1000000 := by linarith
      exact mul_lt_mul_of_pos_left hgt hc_pos
    simpa using h1
  -- Helper: c < c · sqrt(r) for r ≥ 50/49 (which is > 1).
  have h_c_lt_csqrt : ∀ r : ℝ, (50 / 49 : ℝ) ≤ r → v66CValue < v66CValue * Real.sqrt r := by
    intro r hr
    have h_one_lt_sqrt : (1 : ℝ) < Real.sqrt r := by
      have h_one_lt_50_49 : (1 : ℝ) < 50 / 49 := by norm_num
      have h_one_lt_r : (1 : ℝ) < r := lt_of_lt_of_le h_one_lt_50_49 hr
      have hr_nn : (0 : ℝ) ≤ r := by linarith
      have h : Real.sqrt 1 < Real.sqrt r := Real.sqrt_lt_sqrt (by norm_num) h_one_lt_r
      simpa [Real.sqrt_one] using h
    have h1 : v66CValue * 1 < v66CValue * Real.sqrt r :=
      mul_lt_mul_of_pos_left h_one_lt_sqrt hc_pos
    simpa using h1
  fin_cases i
  · exact h_base
  · -- ρStart 1 = c · sqrt(50/49)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (50/49) (le_refl _)
  · -- ρStart 2 = c · sqrt(36/35)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (36/35) (by norm_num)
  · -- ρStart 3 = c · sqrt(25/24)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (25/24) (by norm_num)
  · -- ρStart 4 = c · sqrt(16/15)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (16/15) (by norm_num)
  · -- ρStart 5 = c · sqrt(9/8)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (9/8) (by norm_num)
  · -- ρStart 6 = c · sqrt(4/3)
    unfold v66SevenWindowStart; exact h_c_lt_csqrt (4/3) (by norm_num)

/-! ## branchSplit constraints for the three Branch.one windows -/

/-- For `i ∈ {0, 1, 2}` (the Branch.one windows),
`ρStop i ≤ branchSplit v66CValue = v66CValue · sqrt(4/3)`.
Each is `c · sqrt(k/(k-1)) ≤ c · sqrt(4/3)` for the relevant `k/(k-1)`. -/
theorem v66_stop_le_branchSplit (i : Fin 7)
    (h : v66SevenWindowKind i = KernelKind.branch1) :
    v66SevenWindowStop i ≤ PaperAxioms.branchSplit v66CValue := by
  have hcnn := v66CValue_nonneg
  unfold PaperAxioms.branchSplit
  fin_cases i
  · -- i = 0: ρStop 0 = c · sqrt(50/49) ≤ c · sqrt(4/3)
    show v66CValue * Real.sqrt (50 / 49) ≤ v66CValue * Real.sqrt (4 / 3)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 1: ρStop 1 = c · sqrt(36/35) ≤ c · sqrt(4/3)
    show v66CValue * Real.sqrt (36 / 35) ≤ v66CValue * Real.sqrt (4 / 3)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 2: ρStop 2 = c · sqrt(25/24) ≤ c · sqrt(4/3)
    show v66CValue * Real.sqrt (25 / 24) ≤ v66CValue * Real.sqrt (4 / 3)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 3: kind = modeJ 4, contradiction with `h : kind i = branch1`.
    exfalso
    simp [v66SevenWindowKind] at h
  · -- i = 4: kind = modeJ 3, contradiction.
    exfalso
    simp [v66SevenWindowKind] at h
  · -- i = 5: kind = modeJ 2, contradiction.
    exfalso
    simp [v66SevenWindowKind] at h
  · -- i = 6: kind = modeJ 1, contradiction.
    exfalso
    simp [v66SevenWindowKind] at h

/-! ## branchSplit < 1 at v66CValue -/

/-- `branchSplit v66CValue < 1` (needed by the mixed reducer's
`hSplit_lt_one` premise). -/
theorem v66_branchSplit_lt_one : PaperAxioms.branchSplit v66CValue < 1 := by
  unfold PaperAxioms.branchSplit
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
    have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
    have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
    have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
      Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hpos] at hsq_le
  have hcnn := v66CValue_nonneg
  have h1 : v66CValue * Real.sqrt (4 / 3) ≤ v66CValue * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le hcnn
  have h2 : v66CValue * (1156 / 1000) < 1 := by unfold v66CValue; norm_num
  linarith

/-! ## Per-window mode index facts -/

/-- For `i = 3, 4, 5, 6`, when `kind i = modeJ j`, the value of `j`
matches the seven-window split: `j ∈ {4, 3, 2, 1}`. The witness is
extracted as `1 ≤ j` (which is the only fact the reducer needs). -/
theorem v66_modeJ_one_le_j (i : Fin 7) (j : ℕ)
    (h : v66SevenWindowKind i = KernelKind.modeJ j) : 1 ≤ j := by
  fin_cases i
  · -- i = 0: kind = branch1
    exfalso; simp [v66SevenWindowKind] at h
  · exfalso; simp [v66SevenWindowKind] at h
  · exfalso; simp [v66SevenWindowKind] at h
  · -- i = 3: kind = modeJ 4
    have : j = 4 := by
      have hh : KernelKind.modeJ 4 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 4: kind = modeJ 3
    have : j = 3 := by
      have hh : KernelKind.modeJ 3 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 5: kind = modeJ 2
    have : j = 2 := by
      have hh : KernelKind.modeJ 2 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 6: kind = modeJ 1
    have : j = 1 := by
      have hh : KernelKind.modeJ 1 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]

/-- The full mode-window τ-bound discharge bundled per `i ∈ {3, 4, 5, 6}`.
Returns `1 ≤ j`, the upper τ-bound `tau (j-1) ≤ c²/ρStop²`, and the lower
τ-bound `c²/ρStart² ≤ tau j`. -/
theorem v66_modeJ_tau_bounds (i : Fin 7) (j : ℕ)
    (h : v66SevenWindowKind i = KernelKind.modeJ j) :
    1 ≤ j ∧
    OneModeTail.tau (j - 1) ≤ v66CValue ^ 2 / v66SevenWindowStop i ^ 2 ∧
    v66CValue ^ 2 / v66SevenWindowStart i ^ 2 ≤ OneModeTail.tau j := by
  fin_cases i
  · exfalso; simp [v66SevenWindowKind] at h
  · exfalso; simp [v66SevenWindowKind] at h
  · exfalso; simp [v66SevenWindowKind] at h
  · -- i = 3: kind = modeJ 4
    have hj : j = 4 := by
      have hh : KernelKind.modeJ 4 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 3 ≤
          v66CValue ^ 2 / (v66CValue * Real.sqrt (16 / 15)) ^ 2
      exact tau_three_le_c_sq_div_stop_mode4 v66CValue_pos
    · show v66CValue ^ 2 / (v66CValue * Real.sqrt (25 / 24)) ^ 2 ≤
          OneModeTail.tau 4
      exact c_sq_div_start_mode4_le_tau_four v66CValue_pos
  · -- i = 4: kind = modeJ 3
    have hj : j = 3 := by
      have hh : KernelKind.modeJ 3 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 2 ≤
          v66CValue ^ 2 / (v66CValue * Real.sqrt (9 / 8)) ^ 2
      exact tau_two_le_c_sq_div_stop_mode3 v66CValue_pos
    · show v66CValue ^ 2 / (v66CValue * Real.sqrt (16 / 15)) ^ 2 ≤
          OneModeTail.tau 3
      exact c_sq_div_start_mode3_le_tau_three v66CValue_pos
  · -- i = 5: kind = modeJ 2
    have hj : j = 2 := by
      have hh : KernelKind.modeJ 2 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 1 ≤
          v66CValue ^ 2 / (v66CValue * Real.sqrt (4 / 3)) ^ 2
      exact tau_one_le_c_sq_div_stop_mode2 v66CValue_pos
    · show v66CValue ^ 2 / (v66CValue * Real.sqrt (9 / 8)) ^ 2 ≤
          OneModeTail.tau 2
      exact c_sq_div_start_mode2_le_tau_two v66CValue_pos
  · -- i = 6: kind = modeJ 1
    have hj : j = 1 := by
      have hh : KernelKind.modeJ 1 = KernelKind.modeJ j := by
        simpa [v66SevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨le_refl 1, ?_, ?_⟩
    · -- OneModeTail.tau 0 ≤ c² / ρStop 6 ²
      show OneModeTail.tau 0 ≤ v66CValue ^ 2 / ((999999 : ℝ) / 1000000) ^ 2
      exact tau_zero_le_c_sq_div_stop_mode1
    · show v66CValue ^ 2 / (v66CValue * Real.sqrt (4 / 3)) ^ 2 ≤
          OneModeTail.tau 1
      exact c_sq_div_start_mode1_le_tau_one v66CValue_pos

/-! ## Cross-window monotonic chain bounds (`c ≤ ρStart i`, `ρStop i ≤ 1`) -/

/-- For each `i`, `v66CValue ≤ v66SevenWindowStart i`. -/
theorem v66_c_le_start (i : Fin 7) :
    v66CValue ≤ v66SevenWindowStart i := le_of_lt (v66_c_lt_start i)

/-- For each `i`, `v66SevenWindowStop i ≤ 1`. -/
theorem v66_stop_le_one (i : Fin 7) :
    v66SevenWindowStop i ≤ (1 : ℝ) := le_of_lt (v66_stop_lt_one i)

/-- For each `i`, `v66CValue ≤ v66SevenWindowStop i` (chains via
`ρStart i ≤ ρStop i`). -/
theorem v66_c_le_stop (i : Fin 7) :
    v66CValue ≤ v66SevenWindowStop i :=
  le_trans (v66_c_le_start i) (v66_start_le_stop i)

end ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints
