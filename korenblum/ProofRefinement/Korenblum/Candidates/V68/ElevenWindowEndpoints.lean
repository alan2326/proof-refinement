-- Sprint 092 / V68 — sqrt-pinned eleven-window endpoint properties.
--
-- Per-candidate derived-theorem file (`AGENT_BRIEF.md` lines 154-204) shipping
-- the τ-bound and ordering theorems required by V68's `h_witness` construction
-- at `c = v68CValue = 71313/200000 = 356565/1000000` for the
-- `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` reducer
-- (sprint 086) instantiated at `n = 10` (i.e. `Fin 11` windows).
--
-- The eleven windows are split into one Branch.one residual fallback box
-- (`i = 0`) and ten per-mode tail windows (`i ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9,
-- 10}` for j = 10, 9, 8, 7, 6, 5, 4, 3, 2, 1) by `v68ElevenWindowKind`
-- (defined in `Proof/Reduction.lean`). The mode endpoints are sqrt-pinned at
-- the canonical τ-breakpoints `c · sqrt(121/120), c · sqrt(100/99),
-- c · sqrt(81/80), c · sqrt(64/63), c · sqrt(49/48), c · sqrt(36/35),
-- c · sqrt(25/24), c · sqrt(16/15), c · sqrt(9/8), c · sqrt(4/3)`; the box0
-- lower offset is `c · (1 + 1e-9)` and the mode1 upper limit is `1 - 1e-9`.
--
-- Contents (no `axiom`s, no `sorry`s):
--
--   1. τ-bound polynomial discharges at the ten mode endpoints, mirroring
--      V67/EightWindowEndpoints. Each pair is `field_simp + norm_num` under
--      `Real.sq_sqrt`.
--   2. Geometric ordering at `c = v68CValue`. Adjacency is by definitional
--      `rfl`, the eleven-way ordering chains through `Real.sqrt`-monotonicity,
--      and `c < ρStart 0` plus `ρStop 10 < 1` are by rational arithmetic.
--   3. `branchSplit` constraint for the single Branch.one window:
--      `ρStop 0 = c · sqrt(121/120) ≤ branchSplit c = c · sqrt(4/3)` is a
--      `mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) c_nonneg` invocation.
--   4. The box0 lower bound `c · (1 + 1e-9) > c` plus the cross-window
--      bounds needed by V68.lean (e.g. `c ≤ ρStart i` for any `i`).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints

open KorenblumPaper
open ProofRefinement.Korenblum

/-! ## v68CValue arithmetic facts -/

theorem v68CValue_pos : (0 : ℝ) < v68CValue := by
  unfold v68CValue; norm_num

theorem v68CValue_nonneg : (0 : ℝ) ≤ v68CValue := le_of_lt v68CValue_pos

theorem v68CValue_lt_one : v68CValue < (1 : ℝ) := by
  unfold v68CValue; norm_num

theorem v68CValue_sq_pos : (0 : ℝ) < v68CValue ^ 2 := by
  have h := v68CValue_pos; positivity

theorem v68CValue_sq_ne : v68CValue ^ 2 ≠ 0 := ne_of_gt v68CValue_sq_pos

/-! ## Square-root squaring lemmas -/

theorem sq_c_mul_sqrt {c r : ℝ} (hr : (0 : ℝ) ≤ r) :
    (c * Real.sqrt r) ^ 2 = c ^ 2 * r := by
  rw [mul_pow, Real.sq_sqrt hr]

/-! ## Mode endpoint τ-discharges -/

/-- mode10 window upper τ-bound:
`tau 9 ≤ c² / (c · sqrt(100/99))² = 99/100 = tau 9`. -/
theorem tau_nine_le_c_sq_div_stop_mode10 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 9 ≤ c ^ 2 / (c * Real.sqrt (100 / 99)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 100 / 99)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (100 / 99)) = 99 / 100 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode10 window lower τ-bound:
`c² / (c · sqrt(121/120))² = 120/121 = tau 10 ≤ tau 10`. -/
theorem c_sq_div_start_mode10_le_tau_ten {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (121 / 120)) ^ 2 ≤ OneModeTail.tau 10 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 121 / 120)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (121 / 120)) = 120 / 121 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode9 window upper τ-bound:
`tau 8 ≤ c² / (c · sqrt(81/80))² = 80/81 = tau 8`. -/
theorem tau_eight_le_c_sq_div_stop_mode9 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 8 ≤ c ^ 2 / (c * Real.sqrt (81 / 80)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 81 / 80)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (81 / 80)) = 80 / 81 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode9 window lower τ-bound:
`c² / (c · sqrt(100/99))² = 99/100 = tau 9 ≤ tau 9`. -/
theorem c_sq_div_start_mode9_le_tau_nine {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (100 / 99)) ^ 2 ≤ OneModeTail.tau 9 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 100 / 99)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (100 / 99)) = 99 / 100 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode8 window upper τ-bound:
`tau 7 ≤ c² / (c · sqrt(64/63))² = 63/64 = tau 7`. -/
theorem tau_seven_le_c_sq_div_stop_mode8 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 7 ≤ c ^ 2 / (c * Real.sqrt (64 / 63)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 64 / 63)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (64 / 63)) = 63 / 64 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode8 window lower τ-bound:
`c² / (c · sqrt(81/80))² = 80/81 = tau 8 ≤ tau 8`. -/
theorem c_sq_div_start_mode8_le_tau_eight {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (81 / 80)) ^ 2 ≤ OneModeTail.tau 8 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 81 / 80)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (81 / 80)) = 80 / 81 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode7 window upper τ-bound:
`tau 6 ≤ c² / (c · sqrt(49/48))² = 48/49 = tau 6`. -/
theorem tau_six_le_c_sq_div_stop_mode7 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 6 ≤ c ^ 2 / (c * Real.sqrt (49 / 48)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 49 / 48)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (49 / 48)) = 48 / 49 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode7 window lower τ-bound:
`c² / (c · sqrt(64/63))² = 63/64 = tau 7 ≤ tau 7`. -/
theorem c_sq_div_start_mode7_le_tau_seven {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (64 / 63)) ^ 2 ≤ OneModeTail.tau 7 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 64 / 63)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (64 / 63)) = 63 / 64 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode6 window upper τ-bound:
`tau 5 ≤ c² / (c · sqrt(36/35))² = 35/36 = tau 5`. -/
theorem tau_five_le_c_sq_div_stop_mode6 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 5 ≤ c ^ 2 / (c * Real.sqrt (36 / 35)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 36 / 35)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (36 / 35)) = 35 / 36 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode6 window lower τ-bound:
`c² / (c · sqrt(49/48))² = 48/49 = tau 6 ≤ tau 6`. -/
theorem c_sq_div_start_mode6_le_tau_six {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (49 / 48)) ^ 2 ≤ OneModeTail.tau 6 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 49 / 48)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (49 / 48)) = 48 / 49 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode5 window upper τ-bound:
`tau 4 ≤ c² / (c · sqrt(25/24))² = 24/25 = tau 4`. -/
theorem tau_four_le_c_sq_div_stop_mode5 {c : ℝ} (hc : 0 < c) :
    OneModeTail.tau 4 ≤ c ^ 2 / (c * Real.sqrt (25 / 24)) ^ 2 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 25 / 24)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (25 / 24)) = 24 / 25 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

/-- mode5 window lower τ-bound:
`c² / (c · sqrt(36/35))² = 35/36 = tau 5 ≤ tau 5`. -/
theorem c_sq_div_start_mode5_le_tau_five {c : ℝ} (hc : 0 < c) :
    c ^ 2 / (c * Real.sqrt (36 / 35)) ^ 2 ≤ OneModeTail.tau 5 := by
  rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 36 / 35)]
  have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have heq : c ^ 2 / (c ^ 2 * (36 / 35)) = 35 / 36 := by field_simp
  rw [heq]
  unfold OneModeTail.tau
  norm_num

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

/-- The ten adjacency equations of the eleven-window split: `ρStop i =
ρStart (i+1)` for `i ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}`. By definitional
`rfl` thanks to sprint 092's choice of endpoints. -/
theorem v68_adj (i : Fin 10) :
    v68ElevenWindowStop i.castSucc = v68ElevenWindowStart i.succ := by
  fin_cases i <;> rfl

/-! ## Per-window start/stop ordering (`ρStart i ≤ ρStop i`) -/

/-- For each i, `ρStart i ≤ ρStop i`. By case analysis on `i`; each case
reduces to a sqrt-monotonicity step or a rational arithmetic check. -/
theorem v68_start_le_stop (i : Fin 11) :
    v68ElevenWindowStart i ≤ v68ElevenWindowStop i := by
  have hcnn := v68CValue_nonneg
  fin_cases i
  all_goals (unfold v68ElevenWindowStart v68ElevenWindowStop)
  · -- i = 0: c · (1 + 1/1e9) ≤ c · sqrt(121/120)
    apply mul_le_mul_of_nonneg_left _ hcnn
    -- 1 + 1/1e9 ≤ sqrt(121/120). Suffices (1+1/1e9)² ≤ 121/120.
    have hbase : (1 : ℝ) + 1/1000000000 ≤ Real.sqrt (121/120) := by
      have hSq : ((1 : ℝ) + 1/1000000000) ^ 2 ≤ 121/120 := by norm_num
      have hsnn : (0 : ℝ) ≤ (1 : ℝ) + 1/1000000000 := by norm_num
      have hsq_le : Real.sqrt (((1 : ℝ) + 1/1000000000) ^ 2) ≤ Real.sqrt (121/120) :=
        Real.sqrt_le_sqrt hSq
      rwa [Real.sqrt_sq hsnn] at hsq_le
    exact hbase
  · -- i = 1: c · sqrt(121/120) ≤ c · sqrt(100/99)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 2: c · sqrt(100/99) ≤ c · sqrt(81/80)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 3: c · sqrt(81/80) ≤ c · sqrt(64/63)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 4: c · sqrt(64/63) ≤ c · sqrt(49/48)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 5: c · sqrt(49/48) ≤ c · sqrt(36/35)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 6: c · sqrt(36/35) ≤ c · sqrt(25/24)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 7: c · sqrt(25/24) ≤ c · sqrt(16/15)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 8: c · sqrt(16/15) ≤ c · sqrt(9/8)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 9: c · sqrt(9/8) ≤ c · sqrt(4/3)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 10: c · sqrt(4/3) ≤ 1 - 1/1000000000
    have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (4 / 3) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 - 1 / 1000000000 := by
      unfold v68CValue; norm_num
    linarith

/-! ## Window upper bound `ρStop i < 1` -/

/-- For each `i`, `ρStop i < 1`. -/
theorem v68_stop_lt_one (i : Fin 11) :
    v68ElevenWindowStop i < (1 : ℝ) := by
  have hcnn := v68CValue_nonneg
  fin_cases i
  all_goals (unfold v68ElevenWindowStop)
  · -- ρStop 0 = c · sqrt(121/120) < 1
    have hsqrt_le : Real.sqrt (121 / 120) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (121 / 120 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (121 / 120) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (121 / 120) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 1 = c · sqrt(100/99) < 1
    have hsqrt_le : Real.sqrt (100 / 99) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (100 / 99 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (100 / 99) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (100 / 99) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 2 = c · sqrt(81/80) < 1
    have hsqrt_le : Real.sqrt (81 / 80) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (81 / 80 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (81 / 80) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (81 / 80) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 3 = c · sqrt(64/63) < 1
    have hsqrt_le : Real.sqrt (64 / 63) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (64 / 63 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (64 / 63) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (64 / 63) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 4 = c · sqrt(49/48) < 1
    have hsqrt_le : Real.sqrt (49 / 48) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (49 / 48 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (49 / 48) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (49 / 48) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 5 = c · sqrt(36/35) < 1
    have hsqrt_le : Real.sqrt (36 / 35) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (36 / 35 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (36 / 35) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (36 / 35) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 6 = c · sqrt(25/24) < 1
    have hsqrt_le : Real.sqrt (25 / 24) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (25 / 24 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (25 / 24) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (25 / 24) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 7 = c · sqrt(16/15) < 1
    have hsqrt_le : Real.sqrt (16 / 15) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (16 / 15 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (16 / 15) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (16 / 15) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 8 = c · sqrt(9/8) < 1
    have hsqrt_le : Real.sqrt (9 / 8) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (9 / 8 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (9 / 8) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (9 / 8) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 9 = c · sqrt(4/3) < 1
    have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
      have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
      have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
      have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
        Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hpos] at hsq_le
    have h1 : v68CValue * Real.sqrt (4 / 3) ≤ v68CValue * (1156 / 1000) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcnn
    have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
    linarith
  · -- ρStop 10 = 1 - 1/1000000000 < 1
    norm_num

/-! ## Lower bound `c < ρStart i` -/

/-- For each `i`, `v68CValue < ρStart i`. The base case `i = 0` has
`ρStart 0 = c · (1 + 1/1e9)`, strictly above `c`. The cases `i ≥ 1`
follow from sqrt(r) > 1 for r > 1. -/
theorem v68_c_lt_start (i : Fin 11) :
    v68CValue < v68ElevenWindowStart i := by
  have hc_pos := v68CValue_pos
  have hcnn := v68CValue_nonneg
  -- Helper: c < c · sqrt(r) for r > 1.
  have h_c_lt_csqrt : ∀ r : ℝ, (121 / 120 : ℝ) ≤ r → v68CValue < v68CValue * Real.sqrt r := by
    intro r hr
    have h_one_lt_sqrt : (1 : ℝ) < Real.sqrt r := by
      have h_one_lt_121_120 : (1 : ℝ) < 121 / 120 := by norm_num
      have h_one_lt_r : (1 : ℝ) < r := lt_of_lt_of_le h_one_lt_121_120 hr
      have h : Real.sqrt 1 < Real.sqrt r := Real.sqrt_lt_sqrt (by norm_num) h_one_lt_r
      simpa [Real.sqrt_one] using h
    have h1 : v68CValue * 1 < v68CValue * Real.sqrt r :=
      mul_lt_mul_of_pos_left h_one_lt_sqrt hc_pos
    simpa using h1
  -- Base case `i = 0`: c · (1 + 1/1e9) > c.
  have h_base : v68CValue < v68ElevenWindowStart 0 := by
    unfold v68ElevenWindowStart
    have h1 : v68CValue * 1 < v68CValue * (1 + 1 / 1000000000) := by
      have hpos : (0 : ℝ) < 1 / 1000000000 := by norm_num
      have hgt : (1 : ℝ) < 1 + 1 / 1000000000 := by linarith
      exact mul_lt_mul_of_pos_left hgt hc_pos
    simpa using h1
  fin_cases i
  · exact h_base
  · -- ρStart 1 = c · sqrt(121/120)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (121/120) (le_refl _)
  · -- ρStart 2 = c · sqrt(100/99)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (100/99) (by norm_num)
  · -- ρStart 3 = c · sqrt(81/80)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (81/80) (by norm_num)
  · -- ρStart 4 = c · sqrt(64/63)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (64/63) (by norm_num)
  · -- ρStart 5 = c · sqrt(49/48)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (49/48) (by norm_num)
  · -- ρStart 6 = c · sqrt(36/35)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (36/35) (by norm_num)
  · -- ρStart 7 = c · sqrt(25/24)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (25/24) (by norm_num)
  · -- ρStart 8 = c · sqrt(16/15)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (16/15) (by norm_num)
  · -- ρStart 9 = c · sqrt(9/8)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (9/8) (by norm_num)
  · -- ρStart 10 = c · sqrt(4/3)
    unfold v68ElevenWindowStart; exact h_c_lt_csqrt (4/3) (by norm_num)

/-! ## branchSplit constraint for the single Branch.one window -/

/-- For `i = 0` (the single Branch.one window),
`ρStop 0 = c · sqrt(121/120) ≤ branchSplit v68CValue = v68CValue · sqrt(4/3)`. -/
theorem v68_stop_le_branchSplit (i : Fin 11)
    (h : v68ElevenWindowKind i = KernelKind.branch1) :
    v68ElevenWindowStop i ≤ PaperAxioms.branchSplit v68CValue := by
  have hcnn := v68CValue_nonneg
  unfold PaperAxioms.branchSplit
  fin_cases i
  · -- i = 0: ρStop 0 = c · sqrt(121/120) ≤ c · sqrt(4/3)
    show v68CValue * Real.sqrt (121 / 120) ≤ v68CValue * Real.sqrt (4 / 3)
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt_of_le (by norm_num)) hcnn
  · -- i = 1: kind = modeJ 10, contradiction with `h : kind i = branch1`.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 2: kind = modeJ 9, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 3: kind = modeJ 8, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 4: kind = modeJ 7, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 5: kind = modeJ 6, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 6: kind = modeJ 5, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 7: kind = modeJ 4, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 8: kind = modeJ 3, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 9: kind = modeJ 2, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h
  · -- i = 10: kind = modeJ 1, contradiction.
    exfalso
    simp [v68ElevenWindowKind] at h

/-! ## branchSplit < 1 at v68CValue -/

/-- `branchSplit v68CValue < 1` (needed by the mixed reducer's
`hSplit_lt_one` premise). -/
theorem v68_branchSplit_lt_one : PaperAxioms.branchSplit v68CValue < 1 := by
  unfold PaperAxioms.branchSplit
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 := by
    have hpos : (0 : ℝ) ≤ 1156 / 1000 := by norm_num
    have hle : (4 / 3 : ℝ) ≤ (1156 / 1000) ^ 2 := by norm_num
    have hsq_le : Real.sqrt (4 / 3) ≤ Real.sqrt ((1156 / 1000) ^ 2) :=
      Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hpos] at hsq_le
  have hcnn := v68CValue_nonneg
  have h1 : v68CValue * Real.sqrt (4 / 3) ≤ v68CValue * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le hcnn
  have h2 : v68CValue * (1156 / 1000) < 1 := by unfold v68CValue; norm_num
  linarith

/-! ## Per-window mode index facts -/

/-- For `i = 1, 2, …, 10`, when `kind i = modeJ j`, the value of `j`
matches the eleven-window split: `j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}`.
The witness is extracted as `1 ≤ j` (which is the only fact the reducer
needs). -/
theorem v68_modeJ_one_le_j (i : Fin 11) (j : ℕ)
    (h : v68ElevenWindowKind i = KernelKind.modeJ j) : 1 ≤ j := by
  fin_cases i
  · -- i = 0: kind = branch1
    exfalso; simp [v68ElevenWindowKind] at h
  · -- i = 1: kind = modeJ 10
    have : j = 10 := by
      have hh : KernelKind.modeJ 10 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 2: kind = modeJ 9
    have : j = 9 := by
      have hh : KernelKind.modeJ 9 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 3: kind = modeJ 8
    have : j = 8 := by
      have hh : KernelKind.modeJ 8 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 4: kind = modeJ 7
    have : j = 7 := by
      have hh : KernelKind.modeJ 7 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 5: kind = modeJ 6
    have : j = 6 := by
      have hh : KernelKind.modeJ 6 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 6: kind = modeJ 5
    have : j = 5 := by
      have hh : KernelKind.modeJ 5 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 7: kind = modeJ 4
    have : j = 4 := by
      have hh : KernelKind.modeJ 4 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 8: kind = modeJ 3
    have : j = 3 := by
      have hh : KernelKind.modeJ 3 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 9: kind = modeJ 2
    have : j = 2 := by
      have hh : KernelKind.modeJ 2 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]; decide
  · -- i = 10: kind = modeJ 1
    have : j = 1 := by
      have hh : KernelKind.modeJ 1 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj; exact hj.symm
    rw [this]

/-- The full mode-window τ-bound discharge bundled per `i ∈ {1, …, 10}`.
Returns `1 ≤ j`, the upper τ-bound `tau (j-1) ≤ c²/ρStop²`, and the lower
τ-bound `c²/ρStart² ≤ tau j`. -/
theorem v68_modeJ_tau_bounds (i : Fin 11) (j : ℕ)
    (h : v68ElevenWindowKind i = KernelKind.modeJ j) :
    1 ≤ j ∧
    OneModeTail.tau (j - 1) ≤ v68CValue ^ 2 / v68ElevenWindowStop i ^ 2 ∧
    v68CValue ^ 2 / v68ElevenWindowStart i ^ 2 ≤ OneModeTail.tau j := by
  fin_cases i
  · exfalso; simp [v68ElevenWindowKind] at h
  · -- i = 1: kind = modeJ 10
    have hj : j = 10 := by
      have hh : KernelKind.modeJ 10 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 9 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (100 / 99)) ^ 2
      exact tau_nine_le_c_sq_div_stop_mode10 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (121 / 120)) ^ 2 ≤
          OneModeTail.tau 10
      exact c_sq_div_start_mode10_le_tau_ten v68CValue_pos
  · -- i = 2: kind = modeJ 9
    have hj : j = 9 := by
      have hh : KernelKind.modeJ 9 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 8 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (81 / 80)) ^ 2
      exact tau_eight_le_c_sq_div_stop_mode9 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (100 / 99)) ^ 2 ≤
          OneModeTail.tau 9
      exact c_sq_div_start_mode9_le_tau_nine v68CValue_pos
  · -- i = 3: kind = modeJ 8
    have hj : j = 8 := by
      have hh : KernelKind.modeJ 8 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 7 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (64 / 63)) ^ 2
      exact tau_seven_le_c_sq_div_stop_mode8 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (81 / 80)) ^ 2 ≤
          OneModeTail.tau 8
      exact c_sq_div_start_mode8_le_tau_eight v68CValue_pos
  · -- i = 4: kind = modeJ 7
    have hj : j = 7 := by
      have hh : KernelKind.modeJ 7 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 6 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (49 / 48)) ^ 2
      exact tau_six_le_c_sq_div_stop_mode7 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (64 / 63)) ^ 2 ≤
          OneModeTail.tau 7
      exact c_sq_div_start_mode7_le_tau_seven v68CValue_pos
  · -- i = 5: kind = modeJ 6
    have hj : j = 6 := by
      have hh : KernelKind.modeJ 6 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 5 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (36 / 35)) ^ 2
      exact tau_five_le_c_sq_div_stop_mode6 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (49 / 48)) ^ 2 ≤
          OneModeTail.tau 6
      exact c_sq_div_start_mode6_le_tau_six v68CValue_pos
  · -- i = 6: kind = modeJ 5
    have hj : j = 5 := by
      have hh : KernelKind.modeJ 5 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 4 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (25 / 24)) ^ 2
      exact tau_four_le_c_sq_div_stop_mode5 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (36 / 35)) ^ 2 ≤
          OneModeTail.tau 5
      exact c_sq_div_start_mode5_le_tau_five v68CValue_pos
  · -- i = 7: kind = modeJ 4
    have hj : j = 4 := by
      have hh : KernelKind.modeJ 4 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 3 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (16 / 15)) ^ 2
      exact tau_three_le_c_sq_div_stop_mode4 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (25 / 24)) ^ 2 ≤
          OneModeTail.tau 4
      exact c_sq_div_start_mode4_le_tau_four v68CValue_pos
  · -- i = 8: kind = modeJ 3
    have hj : j = 3 := by
      have hh : KernelKind.modeJ 3 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 2 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (9 / 8)) ^ 2
      exact tau_two_le_c_sq_div_stop_mode3 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (16 / 15)) ^ 2 ≤
          OneModeTail.tau 3
      exact c_sq_div_start_mode3_le_tau_three v68CValue_pos
  · -- i = 9: kind = modeJ 2
    have hj : j = 2 := by
      have hh : KernelKind.modeJ 2 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨by decide, ?_, ?_⟩
    · show OneModeTail.tau 1 ≤
          v68CValue ^ 2 / (v68CValue * Real.sqrt (4 / 3)) ^ 2
      exact tau_one_le_c_sq_div_stop_mode2 v68CValue_pos
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (9 / 8)) ^ 2 ≤
          OneModeTail.tau 2
      exact c_sq_div_start_mode2_le_tau_two v68CValue_pos
  · -- i = 10: kind = modeJ 1
    have hj : j = 1 := by
      have hh : KernelKind.modeJ 1 = KernelKind.modeJ j := by
        simpa [v68ElevenWindowKind] using h
      injection hh with hj'; exact hj'.symm
    subst hj
    refine ⟨le_refl 1, ?_, ?_⟩
    · -- OneModeTail.tau 0 ≤ c² / ρStop 10 ²
      show OneModeTail.tau 0 ≤ v68CValue ^ 2 / ((1 : ℝ) - 1 / 1000000000) ^ 2
      exact tau_zero_le_c_sq_div_stop_mode1
    · show v68CValue ^ 2 / (v68CValue * Real.sqrt (4 / 3)) ^ 2 ≤
          OneModeTail.tau 1
      exact c_sq_div_start_mode1_le_tau_one v68CValue_pos

/-! ## Cross-window monotonic chain bounds (`c ≤ ρStart i`, `ρStop i ≤ 1`) -/

/-- For each `i`, `v68CValue ≤ v68ElevenWindowStart i`. -/
theorem v68_c_le_start (i : Fin 11) :
    v68CValue ≤ v68ElevenWindowStart i := le_of_lt (v68_c_lt_start i)

/-- For each `i`, `v68ElevenWindowStop i ≤ 1`. -/
theorem v68_stop_le_one (i : Fin 11) :
    v68ElevenWindowStop i ≤ (1 : ℝ) := le_of_lt (v68_stop_lt_one i)

/-- For each `i`, `v68CValue ≤ v68ElevenWindowStop i` (chains via
`ρStart i ≤ ρStop i`). -/
theorem v68_c_le_stop (i : Fin 11) :
    v68CValue ≤ v68ElevenWindowStop i :=
  le_trans (v68_c_le_start i) (v68_start_le_stop i)

end ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints
