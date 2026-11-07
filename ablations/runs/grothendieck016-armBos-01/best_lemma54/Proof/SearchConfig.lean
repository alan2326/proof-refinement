/-
  SearchConfig: Fixed parameters for Lemma 5.4 proof search.

  The evolutionary search agent imports this file but CANNOT edit it.
  This locks eta and r to specific values across all search candidates.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

noncomputable section

namespace Braverman.SearchConfig

def eta : ℝ := 1 / 100
def r : ℝ := 23 / 25

theorem r_pos : (0 : ℝ) < r := by unfold r; norm_num
theorem r_lt_one : r < 1 := by unfold r; norm_num
theorem eta_pos : (0 : ℝ) < eta := by unfold eta; norm_num

end Braverman.SearchConfig
