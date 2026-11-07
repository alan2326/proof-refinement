-- @parent V0
import ProofRefinement.Lemma54.Proof.KrivineNumeric

noncomputable section

namespace ProofRefinement.Lemma54.Candidates.V1

open ProofRefinement.Lemma54

/-- Krivine's bound `π / (2 log (1 + √2)) ≈ 1.7822139781`, rationalized up to
`1.78221398`.  This strictly improves the seed's `1782214/1000000`.

Unlike `V0` this is *proved*, not axiomatized: `Proof/KrivineRounding.lean`
derives `GrothendieckIneq K` from `π ≤ 2 · arsinh 1 · K` (Krivine's embedding
plus Gaussian sign rounding plus derandomisation), and
`Proof/KrivineNumeric.lean` certifies that numeric hypothesis at this `K`. -/
def K_val : ℝ := 178221398 / 100000000

theorem K_val_pos : (0 : ℝ) < K_val := by
  norm_num [K_val]

/-- The Grothendieck inequality at `K = 1.78221398`, with no external input. -/
theorem grothendieck_bound_search : GrothendieckIneq K_val :=
  grothendieckIneq_of_pi_le K_val_pos
    (by simpa [K_val] using pi_le_two_krivineConst_mul)

end ProofRefinement.Lemma54.Candidates.V1
