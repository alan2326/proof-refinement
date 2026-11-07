import Mathlib

noncomputable section

namespace KorenblumProofSearch3.SearchConfig

/-- First serious improvement target above `0.3564`. -/
def cTarget : ℝ := 713 / 2000

theorem cTarget_pos : (0 : ℝ) < cTarget := by
  norm_num [cTarget]

theorem cTarget_lt_one : cTarget < (1 : ℝ) := by
  norm_num [cTarget]

end KorenblumProofSearch3.SearchConfig
