/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Strip and Disk Domains

We define the vertical strip `S = {z ∈ ℂ : |Re z| < 1}` and establish basic properties.
The open disk `rD` is just `Metric.ball 0 r` in Mathlib.
-/

open Complex Set Metric

noncomputable section

namespace Braverman

/-- The open vertical strip `S = {z ∈ ℂ | |Re z| < 1}`. -/
def S : Set ℂ := {z : ℂ | |z.re| < 1}

/-- The open disk of radius `r` centered at the origin. -/
def disk (r : ℝ) : Set ℂ := Metric.ball (0 : ℂ) r

/-- The open rectangle `Ω(δ, B) = {z ∈ ℂ : |Re z| < 1 - δ ∧ |Im z| < B}`. -/
def Omega (delta B : ℝ) : Set ℂ :=
  {z : ℂ | |z.re| < 1 - delta ∧ |z.im| < B}

theorem mem_S_iff (z : ℂ) : z ∈ S ↔ |z.re| < 1 := Iff.rfl

theorem mem_Omega_iff (z : ℂ) (delta B : ℝ) :
    z ∈ Omega delta B ↔ |z.re| < 1 - delta ∧ |z.im| < B := Iff.rfl

theorem mem_disk_iff (z : ℂ) (r : ℝ) : z ∈ disk r ↔ ‖z‖ < r := by
  simp [disk, Metric.mem_ball, dist_zero_right]

theorem S_isOpen : IsOpen S := by
  have : S = {z : ℂ | z.re < 1} ∩ {z : ℂ | -1 < z.re} := by
    ext z
    simp [S, abs_lt, and_comm]
  rw [this]
  exact IsOpen.inter
    (isOpen_lt (continuous_re) continuous_const)
    (isOpen_lt continuous_const continuous_re)

theorem disk_isOpen (r : ℝ) : IsOpen (disk r) := Metric.isOpen_ball

theorem Omega_subset_S (delta B : ℝ) (hdelta : 0 < delta) :
    Omega delta B ⊆ S := by
  intro z hz
  rw [mem_Omega_iff] at hz
  rw [mem_S_iff]
  exact lt_of_lt_of_le hz.1 (by linarith)

theorem disk_subset_S (r : ℝ) (hr : r < 1) : disk r ⊆ S := by
  intro z hz
  rw [mem_S_iff]
  rw [mem_disk_iff] at hz
  calc |z.re| ≤ ‖z‖ := abs_re_le_norm z
    _ < r := hz
    _ < 1 := hr

theorem zero_mem_S : (0 : ℂ) ∈ S := by
  simp [S]

theorem zero_mem_disk (r : ℝ) (hr : 0 < r) : (0 : ℂ) ∈ disk r := by
  simp [disk, Metric.mem_ball, hr]

end Braverman
