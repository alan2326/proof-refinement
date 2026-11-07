import KorenblumProofSearch3.ModeBridge
import KorenblumProofSearch3.CertificateCore

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace AffineBoxQ

/--
Primitive for the mode-`j` lower integrand with affine lower envelope
`alpha + beta * ρ` for `1 / Λ(ρ)`.
-/
def modePrimitiveQ (j : ℕ) (c : ℚ) (b : AffineBoxQ) (x : ℚ) : ℚ :=
  b.alpha * x ^ (2 * j + 2) / (j * c ^ (2 * j + 2)) +
    b.beta * (((2 : ℚ) * (j + 1)) / (j * (2 * j + 3))) * x ^ (2 * j + 3) / c ^ (2 * j + 2)

def modeMassQ (j : ℕ) (c : ℚ) (b : AffineBoxQ) : ℚ :=
  modePrimitiveQ j c b b.hi - modePrimitiveQ j c b b.lo

def modeMassR (j : ℕ) (c : ℚ) (b : AffineBoxQ) : ℝ :=
  b.alphaR * ((b.hiR ^ (2 * j + 2) - b.loR ^ (2 * j + 2)) / ((j : ℝ) * (c : ℝ) ^ (2 * j + 2))) +
    b.betaR * ((((2 : ℝ) * (j + 1)) / ((j : ℝ) * (2 * j + 3))) *
      (b.hiR ^ (2 * j + 3) - b.loR ^ (2 * j + 3)) / (c : ℝ) ^ (2 * j + 2))

def modeLowerIntegrand (j : ℕ) (c : ℚ) (b : AffineBoxQ) (ρ : ℝ) : ℝ :=
  ((((2 : ℝ) * (j + 1)) / j) * ρ ^ (2 * j + 1) / (c : ℝ) ^ (2 * j + 2)) * b.lowerAffine ρ

theorem modeMassQ_cast_eq_modeMassR
    (j : ℕ) (c : ℚ) (b : AffineBoxQ) :
    ((modeMassQ j c b : ℚ) : ℝ) = modeMassR j c b := by
  unfold modeMassQ modePrimitiveQ modeMassR loR hiR alphaR betaR
  norm_num
  ring

theorem integral_modeLowerIntegrand_eq_modeMassR
    {j : ℕ}
    (hj : 0 < j)
    (c : ℚ) (b : AffineBoxQ) (hc0 : (c : ℝ) ≠ 0) :
    ∫ ρ in b.loR..b.hiR, modeLowerIntegrand j c b ρ = modeMassR j c b := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hcPow : ((c : ℝ) ^ (2 * j + 2)) ≠ 0 := pow_ne_zero _ hc0
  let F : ℝ → ℝ := fun x =>
    b.alphaR * (x ^ (2 * j + 2) / ((j : ℝ) * (c : ℝ) ^ (2 * j + 2))) +
      b.betaR * ((((2 : ℝ) * (j + 1)) / ((j : ℝ) * (2 * j + 3))) * x ^ (2 * j + 3) /
        (c : ℝ) ^ (2 * j + 2))
  have hFDeriv : ∀ x ∈ uIcc b.loR b.hiR, HasDerivAt F (modeLowerIntegrand j c b x) x := by
    intro x hx
    dsimp [F]
    have hxA : HasDerivAt (fun y : ℝ => y ^ (2 * j + 2)) ((2 * j + 2 : ℕ) * x ^ (2 * j + 1)) x := by
      simpa using (hasDerivAt_id x).pow (2 * j + 2)
    have hxB : HasDerivAt (fun y : ℝ => y ^ (2 * j + 3)) ((2 * j + 3 : ℕ) * x ^ (2 * j + 2)) x := by
      simpa using (hasDerivAt_id x).pow (2 * j + 3)
    have hA : HasDerivAt
        (fun y : ℝ => b.alphaR * (y ^ (2 * j + 2) / ((j : ℝ) * (c : ℝ) ^ (2 * j + 2))))
        (b.alphaR * ((((2 : ℝ) * (j + 1)) / j) * x ^ (2 * j + 1) / (c : ℝ) ^ (2 * j + 2))) x := by
      convert ((hxA.div_const ((j : ℝ) * (c : ℝ) ^ (2 * j + 2))).const_mul b.alphaR) using 1
      field_simp [hjR, hcPow]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring_nf
    have hB : HasDerivAt
        (fun y : ℝ => b.betaR * ((((2 : ℝ) * (j + 1)) / ((j : ℝ) * (2 * j + 3))) * y ^ (2 * j + 3) /
          (c : ℝ) ^ (2 * j + 2)))
        (b.betaR * ((((2 : ℝ) * (j + 1)) / j) * x ^ (2 * j + 2) / (c : ℝ) ^ (2 * j + 2))) x := by
      convert ((((hxB.const_mul (((2 : ℝ) * (j + 1)) / ((j : ℝ) * (2 * j + 3)))).div_const
        ((c : ℝ) ^ (2 * j + 2))).const_mul b.betaR)) using 1
      field_simp [hjR, hcPow]
      norm_num [Nat.cast_add, Nat.cast_mul]
    have h := hA.add hB
    convert h using 1
    unfold modeLowerIntegrand lowerAffine
    ring
  have hFInt : IntervalIntegrable (fun x => modeLowerIntegrand j c b x) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    dsimp [modeLowerIntegrand, lowerAffine]
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFDeriv hFInt]
  unfold F modeMassR loR hiR alphaR betaR
  ring

theorem modeLowerIntegrand_le_scalarIntegrand
    {j : ℕ}
    (hj : 0 < j)
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : (c : ℝ) ≤ b.loR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    ∀ ρ ∈ Icc b.loR b.hiR, modeLowerIntegrand j c b ρ ≤ ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ := by
  intro ρ hρ
  have hρnonneg : 0 ≤ ρ := le_trans hc.le (le_trans hlo hρ.1)
  have hρpos : 0 < ρ := lt_of_lt_of_le hc (le_trans hlo hρ.1)
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hScaleNonneg :
      0 ≤ (((2 : ℝ) * (j + 1)) / j) * ρ ^ (2 * j + 1) / (c : ℝ) ^ (2 * j + 2) := by
    positivity
  by_cases hΛ : Λ ρ = 0
  · have hUpperZero : b.lowerAffine ρ ≤ 0 := by simpa [hΛ] using hAffine ρ hρ
    have hLeft : modeLowerIntegrand j c b ρ ≤ 0 := by
      unfold modeLowerIntegrand
      exact mul_nonpos_of_nonneg_of_nonpos hScaleNonneg hUpperZero
    simpa [ModeBridge.scalarIntegrand, hΛ] using hLeft
  · have hmul := mul_le_mul_of_nonneg_left (hAffine ρ hρ) hScaleNonneg
    have hEq :
        ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ =
          ((((2 : ℝ) * (j + 1)) / j) * ρ ^ (2 * j + 1) / (c : ℝ) ^ (2 * j + 2)) * (Λ ρ)⁻¹ := by
      have hEq' := ModeBridge.scalarIntegrand_eq (c := (c : ℝ)) hj Λ hc hρne hΛ
      rw [hEq']
      field_simp [hΛ]
    simpa [modeLowerIntegrand, lowerAffine, hEq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem modeMassR_le_intervalIntegral
    {j : ℕ}
    (hj : 0 < j)
    (c : ℚ) (b : AffineBoxQ) (Λ : ℝ → ℝ)
    (hc : 0 < (c : ℝ))
    (hlo : (c : ℝ) ≤ b.loR)
    (hlohi : b.loR ≤ b.hiR)
    (hInt : IntervalIntegrable (fun ρ => ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ) volume b.loR b.hiR)
    (hAffine : ∀ ρ ∈ Icc b.loR b.hiR, b.lowerAffine ρ ≤ (Λ ρ)⁻¹) :
    modeMassR j c b ≤ ∫ ρ in b.loR..b.hiR, ModeBridge.scalarIntegrand (c : ℝ) j Λ ρ := by
  have hLowerInt : IntervalIntegrable (fun ρ => modeLowerIntegrand j c b ρ) volume b.loR b.hiR := by
    apply Continuous.intervalIntegrable
    dsimp [modeLowerIntegrand, lowerAffine]
    continuity
  rw [← integral_modeLowerIntegrand_eq_modeMassR hj c b (by exact_mod_cast hc.ne')]
  exact intervalIntegral.integral_mono_on hlohi hLowerInt hInt
    (modeLowerIntegrand_le_scalarIntegrand hj c b Λ hc hlo hAffine)

end AffineBoxQ

end KorenblumProofSearch3
