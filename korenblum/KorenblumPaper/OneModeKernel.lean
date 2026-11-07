import KorenblumPaper.PaperAxioms

open scoped BigOperators

noncomputable section

namespace KorenblumPaper

namespace OneModeKernel

/--
The coefficient weight `(j/(j+1)) c^(2j+2)` from the one-mode argument.

The analytic use is on positive integers, but we keep the definition on all
`ℕ` so it can be reused on arbitrary finite mode sets without extra coercions.
-/
def weight (c : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) / (j + 1)) * c ^ (2 * j + 2)

/--
The pointwise kernel contribution of the `j`th negative mode at radius `ρ`.
-/
def term (c ρ : ℝ) (j : ℕ) : ℝ :=
  weight c j / ρ ^ (2 * j)

/--
Finite one-mode kernel over a nonempty finite set of positive modes.

The full analytic candidate uses the supremum over all positive integers, but
the first Lean formalization works with explicit finite mode sets so the linear
optimization argument can be compiled and reused without introducing an
infinite-order wrapper yet.
-/
def kernelOn (c ρ : ℝ) (s : Finset ℕ) (hs : s.Nonempty) : ℝ :=
  s.sup' hs (term c ρ)

theorem term_one_eq_branch2 (c ρ : ℝ) :
    term c ρ 1 = PaperAxioms.branch2SigmaKernel c ρ := by
  by_cases hρ : ρ = 0
  · simp [term, weight, PaperAxioms.branch2SigmaKernel, hρ]
  · have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
    unfold term weight PaperAxioms.branch2SigmaKernel
    field_simp [hρ2]
    ring

theorem term_le_kernelOn
    (c ρ : ℝ)
    (s : Finset ℕ)
    (hs : s.Nonempty)
    {j : ℕ}
    (hj : j ∈ s) :
    term c ρ j ≤ kernelOn c ρ s hs := by
  exact Finset.le_sup' (s := s) (f := term c ρ) hj

theorem weight_eq_term_mul_pow
    (c ρ : ℝ)
    (j : ℕ)
    (hρ : ρ ≠ 0) :
    weight c j = term c ρ j * ρ ^ (2 * j) := by
  have hpow : ρ ^ (2 * j) ≠ 0 := pow_ne_zero _ hρ
  unfold term
  field_simp [hpow]

theorem weight_le_kernelOn_mul_pow
    (c ρ : ℝ)
    (s : Finset ℕ)
    (hs : s.Nonempty)
    {j : ℕ}
    (hj : j ∈ s)
    (hρ : ρ ≠ 0) :
    weight c j ≤ kernelOn c ρ s hs * ρ ^ (2 * j) := by
  have hpow0 : 0 ≤ ρ ^ (2 * j) := by
    simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using sq_nonneg (ρ ^ j)
  have hterm : term c ρ j ≤ kernelOn c ρ s hs := term_le_kernelOn c ρ s hs hj
  have hscaled := mul_le_mul_of_nonneg_right hterm hpow0
  calc
    weight c j = term c ρ j * ρ ^ (2 * j) := by
      exact weight_eq_term_mul_pow c ρ j hρ
    _ ≤ kernelOn c ρ s hs * ρ ^ (2 * j) := hscaled

theorem weighted_sum_le_of_termwise
    (c ρ M : ℝ)
    (s : Finset ℕ)
    (η : ℕ → ℝ)
    (hη : ∀ j ∈ s, 0 ≤ η j)
    (hbound : ∀ j ∈ s, weight c j ≤ M * ρ ^ (2 * j)) :
    Finset.sum s (fun j => η j * weight c j) ≤
      M * Finset.sum s (fun j => η j * ρ ^ (2 * j)) := by
  classical
  revert hη hbound
  refine Finset.induction_on s ?_ ?_
  · intro hη hbound
    simp
  · intro a s ha ih hη hbound
    have hηa : 0 ≤ η a := hη a (Finset.mem_insert_self a s)
    have hηs : ∀ j ∈ s, 0 ≤ η j := by
      intro j hj
      exact hη j (Finset.mem_insert_of_mem hj)
    have hbounda : weight c a ≤ M * ρ ^ (2 * a) :=
      hbound a (Finset.mem_insert_self a s)
    have hbounds : ∀ j ∈ s, weight c j ≤ M * ρ ^ (2 * j) := by
      intro j hj
      exact hbound j (Finset.mem_insert_of_mem hj)
    have ih' := ih hηs hbounds
    have hhead :
        η a * weight c a ≤ η a * (M * ρ ^ (2 * a)) := by
      exact mul_le_mul_of_nonneg_left hbounda hηa
    calc
      Finset.sum (insert a s) (fun j => η j * weight c j)
          = η a * weight c a + Finset.sum s (fun j => η j * weight c j) := by
              simp [ha]
      _ ≤ η a * (M * ρ ^ (2 * a)) + M * Finset.sum s (fun j => η j * ρ ^ (2 * j)) := by
            exact add_le_add hhead ih'
      _ = M * (η a * ρ ^ (2 * a) + Finset.sum s (fun j => η j * ρ ^ (2 * j))) := by ring
      _ = M * Finset.sum (insert a s) (fun j => η j * ρ ^ (2 * j)) := by
            simp [ha, mul_add]

theorem weighted_sum_le_kernelOn_mul
    (c ρ : ℝ)
    (s : Finset ℕ)
    (hs : s.Nonempty)
    (η : ℕ → ℝ)
    (hρ : ρ ≠ 0)
    (hη : ∀ j ∈ s, 0 ≤ η j) :
    Finset.sum s (fun j => η j * weight c j) ≤
      kernelOn c ρ s hs * Finset.sum s (fun j => η j * ρ ^ (2 * j)) := by
  apply weighted_sum_le_of_termwise c ρ (kernelOn c ρ s hs) s η hη
  intro j hj
  exact weight_le_kernelOn_mul_pow c ρ s hs hj hρ

end OneModeKernel

end KorenblumPaper
