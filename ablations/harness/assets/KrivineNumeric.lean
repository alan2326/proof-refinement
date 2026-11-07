/-
# Brick F: the numeric certificate for Krivine's constant

`Proof/KrivineRounding.lean` reduces the Grothendieck inequality at `K` to the
purely numeric hypothesis `π ≤ 2 · krivineConst · K` with
`krivineConst = arsinh 1 = log (1 + √2)`.  This file certifies that hypothesis
at the rational `K = 178221398/100000000 = 1.78221398`, which is strictly below
the seed's `1782214/1000000 = 1.782214`.

The certificate chain is entirely elementary:

* `√2 ≥ 1.414213562373` by `Real.le_sqrt_of_sq_le`;
* `log (1 + √2) ≥ 0.881373587` by `Real.le_log_iff_exp_le` plus the degree-12
  Taylor bound `Real.exp_bound'`;
* `π < 3.14159265358979323847` by `Real.pi_lt_d20`, and
  `2 · 0.881373587 · 1.78221398 = 3.14159265671... ` exceeds it.
-/
import ProofRefinement.Lemma54.Proof.KrivineRounding

noncomputable section

namespace ProofRefinement.Lemma54

open Real

set_option linter.unusedSectionVars false

/-- A rational lower bound for `√2`, accurate to `2.7e-13`. -/
theorem sqrt_two_ge : (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 :=
  Real.le_sqrt_of_sq_le (by norm_num)

/-- `krivineConst` is the logarithm of `1 + √2`. -/
theorem krivineConst_eq_log : krivineConst = Real.log (1 + Real.sqrt 2) := by
  unfold krivineConst Real.arsinh
  norm_num

/-- A rational lower bound for `krivineConst = arsinh 1 = log (1 + √2)`,
accurate to `2.0e-11`.  The exponential is bounded by its degree-12 Taylor
polynomial plus the tail estimate of `Real.exp_bound'`. -/
theorem le_krivineConst : (881373587 / 1000000000 : ℝ) ≤ krivineConst := by
  have hs : (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 := sqrt_two_ge
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2
    linarith
  rw [krivineConst_eq_log, Real.le_log_iff_exp_le hpos]
  have hb := Real.exp_bound' (x := (881373587 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
    (n := 12) (by norm_num)
  refine hb.trans ?_
  have htail : (∑ m ∈ Finset.range 12, (881373587 / 1000000000 : ℝ) ^ m / m.factorial) +
      (881373587 / 1000000000 : ℝ) ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℝ) * 12)
        ≤ 1 + 1414213562373 / 1000000000000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine htail.trans ?_
  linarith

/-- **Brick F.**  The numeric hypothesis of `grothendieckIneq_of_pi_le` holds at
`K = 178221398/100000000`, with margin `3.1e-9`. -/
theorem pi_le_two_krivineConst_mul :
    π ≤ 2 * krivineConst * (178221398 / 100000000 : ℝ) := by
  have hpi : π < 3.14159265358979323847 := Real.pi_lt_d20
  have hnum : (3.14159265358979323847 : ℝ)
      ≤ 2 * (881373587 / 1000000000 : ℝ) * (178221398 / 100000000 : ℝ) := by
    norm_num
  have hmono : 2 * (881373587 / 1000000000 : ℝ) * (178221398 / 100000000 : ℝ)
      ≤ 2 * krivineConst * (178221398 / 100000000 : ℝ) := by
    linarith [le_krivineConst]
  linarith

end ProofRefinement.Lemma54
