/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Defs.Strip
import LeanProof.Defs.Partition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The kernel functions H_η, H₀, and F_p

We define:
- `H_η(z)` — the 4-dimensional Gaussian integral (equation 41)
- `H₀(z)` — specialization at η = 0
- `F_p(z) = (1-p) H₀(z) + p H_η(z)` — the interpolating family
- `ψ(z) = (z - (H_η(sin z) - H₀(sin z))) · cos z` — the first-order correction

These are the core objects needed for Lemmas 5.3 and 5.4.
-/

open Complex MeasureTheory Set Metric Real

noncomputable section

namespace Braverman

/-!
## The kernel integral H_η

The paper defines (eq 41):
  H_η(z) = (1/(2π)) ∫∫_{ℝ²×ℝ²} f_η(x) f_η(y) ·
    exp(-(‖x‖² + ‖y‖² - 2z⟨x,y⟩) / (2(1-z²))) / (2π(1-z²)) dx dy

For the formalization, we work with a simplified but equivalent form.
The key properties we need are:
1. H_η is analytic on S (Lemma 4.2)
2. H₀ = arcsin (Lemma 4.3)
3. H_η is odd
4. The bound (43)
-/

/-- The bilinear form kernel used in the Gaussian integral defining H_η.
    For x, y ∈ ℝ² and z ∈ ℂ with |Re z| < 1, this is the exponent in
    the 4D Gaussian integral. -/
def kernel_exponent (x₁ x₂ y₁ y₂ : ℝ) (z : ℂ) : ℂ :=
  -(((x₁ ^ 2 + x₂ ^ 2 : ℝ) + (y₁ ^ 2 + y₂ ^ 2 : ℝ) -
    2 * z * (x₁ * y₁ + x₂ * y₂ : ℝ)) / (1 - z ^ 2))

/-- `H_η(z)` defined as the 4D integral over ℝ⁴.
    This is the generating kernel for the rounding scheme. -/
def H_eta (η : ℝ) (z : ℂ) : ℂ :=
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      ↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))

/-- `H₀` is the kernel at η = 0 (i.e., using f₀(x) = sign(x₂)). -/
def H0 (z : ℂ) : ℂ := H_eta 0 z

/-- The interpolating family `F_p = (1-p) H₀ + p H_η`. -/
def F_p (η : ℝ) (p : ℝ) (z : ℂ) : ℂ :=
  (1 - ↑p) * H0 z + ↑p * H_eta η z

/-- The perturbation `φ = H_η - H₀`. -/
def phi (η : ℝ) (z : ℂ) : ℂ := H_eta η z - H0 z

/-- The first-order correction term `ψ(z) = (z - φ(sin z)) · cos z`
    appearing in Lemma 5.4, where φ = H_η - H₀. -/
def psi (η : ℝ) (z : ℂ) : ℂ :=
  (z - phi η (Complex.sin z)) * Complex.cos z

-- Basic properties of F_p

theorem F_p_at_zero (η : ℝ) (z : ℂ) : F_p η 0 z = H0 z := by
  simp [F_p]

theorem F_p_at_one (η : ℝ) (z : ℂ) : F_p η 1 z = H_eta η z := by
  simp [F_p]

/-- F_p is affine in p. -/
theorem F_p_eq (η : ℝ) (p : ℝ) (z : ℂ) :
    F_p η p z = H0 z + ↑p * phi η z := by
  simp [F_p, phi]
  ring

end Braverman
