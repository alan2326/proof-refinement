/-
Candidate contract for Arm C (partial formalization ablated) of the
Grothendieck ablation study.

States the constant of record -- the Grothendieck constant K_G -- in Mathlib
terms only. `GrothendieckIneq` and `KrivineBound` are verbatim copies of the
production definitions; they are restated standalone because this workspace
carries no production formalization to import.
-/
import Mathlib

open Real Set

noncomputable section

namespace ProofRefinement.Lemma54

/-- A constant K satisfies the Grothendieck inequality if for all finite
    bilinear forms defined by signs, the SDP relaxation ratio is at most K.

    Formally: for all n, m, matrix A, and unit vectors x, y in any
    real Hilbert space H,
      max_{eps,del in {+-1}^n x m} sum_ij a_ij eps_i del_j
        >= (1/K) * sum_ij a_ij <x_i, y_j> -/
def GrothendieckIneq (K : ℝ) : Prop :=
  0 < K ∧
  ∀ (n m : ℕ) (A : Fin n → Fin m → ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (_ : ∀ i, ‖x i‖ = 1) (_ : ∀ j, ‖y j‖ = 1),
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * ε i * δ j ≥
        (1 / K) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j)

/-- The Krivine bound: pi/(2*log(1+sqrt 2)) ~= 1.7822139781.
    The previous state of the art for K_G. -/
def KrivineBound : ℝ := Real.pi / (2 * Real.log (1 + Real.sqrt 2))

private theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos_of_pos (by norm_num)

theorem log_one_add_sqrt_two_pos : (0 : ℝ) < Real.log (1 + Real.sqrt 2) :=
  Real.log_pos (by linarith [sqrt_two_pos])

theorem KrivineBound_pos : 0 < KrivineBound := by
  unfold KrivineBound
  exact div_pos Real.pi_pos (mul_pos (by norm_num) log_one_add_sqrt_two_pos)

end ProofRefinement.Lemma54
