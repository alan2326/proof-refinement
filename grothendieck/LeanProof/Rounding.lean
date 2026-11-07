/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem51
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Rounding: Hilbert embedding and Gaussian projection

We define the Hilbert space embedding that converts the analytic inverse F_p⁻¹
into a rounding scheme for the Grothendieck inequality.

## Main constructions

1. The Hilbert space K = ⊕_{k≥1} H^{⊗k} (as an ℓ² direct sum)
2. The embedding maps L_p(x), R_p(y) using coefficients aₖ(p) and scaling γ^{k/2}
3. The inner product identity ⟨L_p(x), R_p(y)⟩ = F_p⁻¹(γ⟨x,y⟩)
4. The Gaussian expectation identity for the rounding scheme

## Key identities

For unit vectors x, y in a Hilbert space H:
- ⟨x⊗ᵏ, y⊗ᵏ⟩ = ⟨x,y⟩ᵏ (tensor power inner product)
- ‖L_p(x)‖ = 1 (unit norm from ∑|aₖ|γᵏ = 1)
- E[f_η(Gx/√2) · f_η(Gy/√2)] = (2/π) · H_η(⟨x,y⟩) (Gaussian projection)
-/

open Complex Set Metric Real MeasureTheory

noncomputable section

namespace Braverman


/-! ### Rounding scheme produces Grothendieck inequality

The full rounding argument proving GrothendieckIneq (π/(2γ)).

**Proof outline** (Braverman-Makarychev-Makarychev-Naor, 2011, Section 5):

Given unit vectors x₁,...,xₙ, y₁,...,yₘ in a Hilbert space H, the rounding
scheme works as follows:

1. **Gaussian projection**: Sample g₁, g₂ i.i.d. standard Gaussian vectors
   in H. For each i, set εᵢ = f_η(⟨g₁,xᵢ⟩, ⟨g₂,xᵢ⟩) ∈ {±1},
   and similarly δⱼ = f_η(⟨g₁,yⱼ⟩, ⟨g₂,yⱼ⟩) ∈ {±1}.

2. **Expectation identity**: E[εᵢ δⱼ] = (2/π) · H_η(⟨xᵢ,yⱼ⟩).
   This follows from the fact that (⟨g₁,x⟩,⟨g₂,x⟩,⟨g₁,y⟩,⟨g₂,y⟩) is a
   4D Gaussian with correlation structure determined by ⟨x,y⟩, and by
   rotation invariance the expectation reduces to the integral defining H_η.

3. **Analytic inverse identity**: For unit vectors, |⟨xᵢ,yⱼ⟩| ≤ 1 < γ,
   so γ⟨xᵢ,yⱼ⟩ ∈ disk(γ). The composition gives:
   (2/π) · H_η(⟨xᵢ,yⱼ⟩) ≥ (2γ/π) · ⟨xᵢ,yⱼ⟩
   This is the key inequality that uses F_p(F_inv(z)) = z and the
   monotonicity properties of H_η.

4. **Linearity of expectation**: E[∑ᵢⱼ aᵢⱼ εᵢ δⱼ] = ∑ᵢⱼ aᵢⱼ E[εᵢ δⱼ]
   ≥ (2γ/π) · ∑ᵢⱼ aᵢⱼ ⟨xᵢ,yⱼ⟩ = (1/K) · ∑ᵢⱼ aᵢⱼ ⟨xᵢ,yⱼ⟩
   where K = π/(2γ).

5. **Probabilistic method**: Since the expectation satisfies the bound,
   there exist specific sign vectors ε*, δ* achieving at least the
   expected value.

The deepest steps (Gaussian projection expectation identity, the pointwise
inequality relating H_η to the linear function) require substantial
measure theory. We decompose `rounding_core_inequality` into sub-lemmas. -/

/-! ### Sub-lemma 1: Inner products of unit vectors are bounded -/

/-- For unit vectors x, y, we have |⟨x, y⟩| ≤ 1. -/
theorem abs_inner_le_one_of_unit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |@inner ℝ H _ x y| ≤ 1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy] at h
  linarith

/-! ### Sub-lemma 2: Pointwise inequality from the analytic inverse

The key analytic step: for t ∈ [-1, 1], using that F_p has an analytic
inverse on disk(γ) with γ > 1, we derive:

  (2/π) · Re(H_η(t)) ≥ (2γ/π) · t

This uses the identity F_p(F_inv(γt)) = γt together with the expansion
F_p = (1-p)H₀ + pH_η, the known fact that H₀(w) = (2/π)arcsin(w)
for w ∈ S, and the monotonicity of arcsin.

**Detailed argument**: For t ∈ [-1, 1]:
- Since |t| ≤ 1 < γ, we have |γt| ≤ γ (and < γ for |t| < 1)
- Let w = F_inv(γt). Then w ∈ S and F_p(w) = γt.
- Expanding: (1-p) · H₀(w) + p · H_η(w) = γt
- Since H₀ = (2/π)·arcsin and for real w with |w| < 1,
  H₀(w) = (2/π)·arcsin(w), we have |H₀(w)| ≤ 1.
- Solving for H_η: p · H_η(w) = γt - (1-p) · H₀(w)
- The relationship between H_η(w) and H_η(t) comes from the
  composition: H_η(t) is what we ultimately evaluate after
  the full rounding construction.
-/

/-! ## Composition identity helper lemmas -/

/-- γ * t is in disk(γ) when |t| < 1. -/
theorem gamma_mul_mem_disk (hγ_pos : γ > 0) {t : ℝ} (ht : |t| < 1) :
    ↑(γ * t) ∈ disk γ := by
  simp only [disk, Metric.mem_ball, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos hγ_pos]
  nlinarith

/-- The composition identity: F_p(F_inv(γt)) = γt for |t| < 1.
    This is the key identity connecting the analytic inverse to the rounding bound. -/
theorem F_p_F_inv_composition
    (γ : ℝ) (hγ_pos : γ > 0)
    (η p : ℝ) (F_inv : ℂ → ℂ)
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    {t : ℝ} (ht : |t| < 1) :
    F_p η p (F_inv ↑(γ * t)) = ↑(γ * t) :=
  hFi _ (gamma_mul_mem_disk hγ_pos ht)

/-! ## Tensor embedding lemma

For an analytic function with summable Taylor coefficients, unit vectors in a Hilbert space
can be embedded into a finite-dimensional Euclidean space preserving a transformed inner
product. This is the key embedding used in the Grothendieck rounding scheme. -/

/-- **Tensor embedding existence**: Given unit vectors in a Hilbert space H and an
    analytic function F_inv with summability condition ∑|aₖ|γᵏ = 1 and composition
    identity F_p(F_inv(γt)) = γt, there exist unit vectors in some ℝ^d whose inner
    products satisfy the F_p composition identity.

    The proof constructs vectors in the ℓ² direct sum of tensor powers:
    u_i = (√|bₖ| · x_i^{⊗k})_k,  v_j = (sign(bₖ)√|bₖ| · y_j^{⊗k})_k
    where bₖ = aₖγᵏ. The summability condition ensures ‖u_i‖ = ‖v_j‖ = 1,
    and the inner product identity gives ⟨u_i,v_j⟩ = F_inv(γ⟨x_i,y_j⟩). -/
theorem tensor_embedding_with_composition
    (γ : ℝ) (hγ_pos : γ > 0) (hγ_lt_one : γ < 1)
    (η p : ℝ) (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk γ))
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk γ, F_inv z ∈ S)
    (hSummable : summability_condition (taylor_coeff F_inv) γ)
    (n m : ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    ∃ (d : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d))
      (v : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖ = 1) ∧ (∀ j, ‖v j‖ = 1) ∧
      ∀ i j, (F_p η p
        (↑(@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (u i) (v j)))).re =
        γ * @inner ℝ H _ (x i) (y j) := by
  sorry

/-! ## Mixed Gaussian rounding lemma -/

/-- **Mixed Gaussian rounding**: For unit vectors in ℝ^d, the mixed Gaussian rounding
    scheme (probability 1-p for sign rounding, probability p for f_η rounding) produces
    a probability space with ±1 random signs whose expected pairwise products equal
    (2/π) · F_p(⟨u_i, v_j⟩).

    The proof constructs Ω = ℝ^d × ℝ^d × Bool with the product of standard Gaussian
    measures and a Bernoulli(p) coin flip. The sign rounding component gives
    (2/π)H₀(⟨u,v⟩) = (2/π)arcsin(⟨u,v⟩) by Sheppard's formula, and the f_η rounding
    gives (2/π)H_η(⟨u,v⟩) by the integral definition. The mixture with weights
    (1-p, p) yields (2/π)F_p(⟨u,v⟩). -/
theorem mixed_gaussian_rounding
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (d n m : ℕ)
    (u : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
        (_ : MeasureTheory.IsProbabilityMeasure μ)
        (ε' : Ω → Fin n → ℝ) (δ' : Ω → Fin m → ℝ),
        (∀ ω i, ε' ω i = 1 ∨ ε' ω i = -1) ∧
        (∀ ω j, δ' ω j = 1 ∨ δ' ω j = -1) ∧
        (∀ i j, MeasureTheory.Integrable (fun ω => ε' ω i * δ' ω j) μ) ∧
        ∀ i j, ∫ ω, ε' ω i * δ' ω j ∂μ =
          (2 / Real.pi) * (F_p η p
            (↑(@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (u i) (v j)))).re := by
  sorry

/-! ## Sorry-free probabilistic method

The sorry-free version takes a probability space with random sign functions as input,
rather than asserting existence from a vacuous hypothesis. This is the correct
formulation of the probabilistic method step. -/

/-- If the expected value of f is at least B under a probability measure,
    then some outcome achieves at least B. -/
theorem exists_sample_ge_of_integral_ge'
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) {B : ℝ}
    (hB : B ≤ ∫ ω, f ω ∂μ) :
    ∃ ω, B ≤ f ω :=
  (exists_integral_le hf).imp (fun ω hω => le_trans hB hω)

/-- **Probabilistic method for rounding** (abstract version):
    Given a probability space with random sign functions whose expected score
    is at least c · ∑ A(i,j) ⟨x_i, y_j⟩, deterministic signs achieving that bound exist. -/
theorem gaussian_rounding_existence_abstract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (A : Fin n → Fin m → ℝ) (c : ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (ε : Ω → Fin n → ℝ) (δ : Ω → Fin m → ℝ)
    (hε : ∀ ω i, ε ω i = 1 ∨ ε ω i = -1)
    (hδ : ∀ ω j, δ ω j = 1 ∨ δ ω j = -1)
    (hInt : Integrable (fun ω => ∑ i, ∑ j, A i j * ε ω i * δ ω j) μ)
    (hScore :
      c * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) ≤
        ∫ ω, ∑ i, ∑ j, A i j * ε ω i * δ ω j ∂μ) :
    ∃ (ε0 : Fin n → ℝ) (δ0 : Fin m → ℝ),
      (∀ i, ε0 i = 1 ∨ ε0 i = -1) ∧
      (∀ j, δ0 j = 1 ∨ δ0 j = -1) ∧
      ∑ i, ∑ j, A i j * ε0 i * δ0 j ≥
        c * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) := by
  obtain ⟨ω₀, hω₀⟩ := exists_sample_ge_of_integral_ge' μ hInt hScore
  exact ⟨ε ω₀, δ ω₀, hε ω₀, hδ ω₀, hω₀⟩

/-! ### Gaussian rounding with analytic inverse

The paper's rounding scheme (Section 5) uses the analytic inverse F_p⁻¹ to construct
an embedding where the Gaussian projection directly yields the (2γ/π) ratio.

The key insight: instead of proving a pointwise bound Re(H_η(t)) ≥ γt (which the
paper never needs), we use the identity F_p(F_inv(γ⟨x,y⟩)) = γ⟨x,y⟩ inside the
Gaussian projection. The mixed rounding strategy (probability 1-p for f₀, probability
p for f_η) gives:
  E[ε_i δ_j] = (2/π) · F_p(F_inv(γ⟨x_i,y_j⟩)) = (2γ/π) · ⟨x_i,y_j⟩

This combines the Gaussian projection identity (eq. 67) with the analytic inverse
property into a single step, eliminating the need for a separate pointwise bound. -/

/-- **Gaussian mixed rounding construction** (Braverman et al. 2011, Section 5):
    For the analytic inverse parameters and unit vectors, constructs a probability space
    with random ±1 signs whose pairwise expected products equal (2γ/π) · ⟨xᵢ, yⱼ⟩.

    Proof requires: (1) tensor embedding via F_inv Taylor coefficients, producing unit
    vectors with inner products F_inv(γ⟨x,y⟩); (2) mixed Gaussian rounding giving
    E[εδ] = (2/π)F_p(inner product); (3) composition F_p(F_inv(γt)) = γt. -/
theorem rounding_probability_space_construction
    (γ : ℝ) (hγ_pos : γ > 0) (hγ_lt_one : γ < 1)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk γ))
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk γ, F_inv z ∈ S)
    (hSummable : summability_condition (taylor_coeff F_inv) γ)
    (n m : ℕ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
        (_ : MeasureTheory.IsProbabilityMeasure μ)
        (ε' : Ω → Fin n → ℝ) (δ' : Ω → Fin m → ℝ),
        (∀ ω i, ε' ω i = 1 ∨ ε' ω i = -1) ∧
        (∀ ω j, δ' ω j = 1 ∨ δ' ω j = -1) ∧
        (∀ i j, MeasureTheory.Integrable (fun ω => ε' ω i * δ' ω j) μ) ∧
        (∀ i j, ∫ ω, ε' ω i * δ' ω j ∂μ =
          (2 * γ / Real.pi) * @inner ℝ H _ (x i) (y j)) := by
  -- Step 1: Tensor embedding — produce unit vectors with the right inner products.
  -- From hSummable (∑|aₖ|γᵏ = 1) and the power series of F_inv, there exist
  -- unit vectors u_i, v_j in some ℝ^d with ⟨u_i,v_j⟩ = (F_inv(↑(γ⟨x_i,y_j⟩))).re.
  have hembed : ∃ (d : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d))
      (v : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖ = 1) ∧ (∀ j, ‖v j‖ = 1) ∧
      ∀ i j, (F_p η p
        (↑(@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (u i) (v j)))).re =
        γ * @inner ℝ H _ (x i) (y j) := by
    exact tensor_embedding_with_composition γ hγ_pos hγ_lt_one η p F_inv
      hFa hFi hFS hSummable n m H x y hx hy
  obtain ⟨d, u, v, hu_norm, hv_norm, hident⟩ := hembed
  -- Step 2: Mixed Gaussian rounding — construct probability space with the right
  -- expectations for the embedded unit vectors.
  have hgauss : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
      (_ : MeasureTheory.IsProbabilityMeasure μ)
      (ε' : Ω → Fin n → ℝ) (δ' : Ω → Fin m → ℝ),
      (∀ ω i, ε' ω i = 1 ∨ ε' ω i = -1) ∧
      (∀ ω j, δ' ω j = 1 ∨ δ' ω j = -1) ∧
      (∀ i j, MeasureTheory.Integrable (fun ω => ε' ω i * δ' ω j) μ) ∧
      ∀ i j, ∫ ω, ε' ω i * δ' ω j ∂μ =
        (2 / Real.pi) * (F_p η p
          (↑(@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (u i) (v j)))).re := by
    exact mixed_gaussian_rounding η p hη hp d n m u v hu_norm hv_norm
  obtain ⟨Ω, mΩ, μ, hμ, ε', δ', hε_sign, hδ_sign, hPairInt, hExpect⟩ := hgauss
  -- Step 3: Assembly — combine embedding identity with rounding expectations.
  exact ⟨Ω, mΩ, μ, hμ, ε', δ', hε_sign, hδ_sign, hPairInt,
    fun i j => by
      rw [hExpect i j]
      -- Goal: (2/π) * (F_p η p ↑⟨u_i,v_j⟩).re = (2γ/π) * ⟨x_i,y_j⟩
      rw [hident i j]
      ring⟩

/-- **Gaussian rounding with analytic inverse**:
    Given the analytic inverse parameters (γ, η, p, F_inv) from Theorem 5.1,
    unit vectors x, y, and a matrix A, the Gaussian rounding scheme produces
    deterministic signs ε ∈ {±1}ⁿ, δ ∈ {±1}ᵐ such that
      ∑ A(i,j) ε_i δ_j ≥ (2γ/π) · ∑ A(i,j) ⟨x_i, y_j⟩

    **sorry**: This requires constructing a Gaussian measure on Hilbert spaces
    and proving the Gaussian projection identity (eq. 67 in the paper):
      E[f_η(Gu/√2) · f_η(Gv/√2)] = (2/π) · H_η(⟨u,v⟩) -/
theorem gaussian_rounding_with_inverse
    (γ : ℝ) (hγ_pos : γ > 0) (hγ_lt_one : γ < 1)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk γ))
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk γ, F_inv z ∈ S)
    (hSummable : summability_condition (taylor_coeff F_inv) γ)
    (n m : ℕ) (A : Fin n → Fin m → ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * ε i * δ j ≥
        (2 * γ / Real.pi) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) := by
  -- Proof by the probabilistic method (Section 5 of Braverman et al. 2011).
  --
  -- Step 1: Construct a probability space with random signs whose expected
  -- bilinear form is exactly (2γ/π) times the inner product form.
  -- This uses: (a) embedding via F_inv Taylor coefficients into tensor space K,
  -- (b) mixed Gaussian rounding (prob 1-p for sign, prob p for f_η),
  -- (c) the identity E[rounding] = (2/π)F_p(⟨L,R⟩) = (2/π)F_p(F_inv(γt)) = (2γ/π)t.
  --
  -- Step 2: Apply the probabilistic method (gaussian_rounding_existence_v2).
  --
  -- Case split: is the RHS non-positive?
  by_cases hRHS : (2 * γ / Real.pi) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) ≤ 0
  · -- Easy case: RHS ≤ 0. We produce signs with score ≥ 0 ≥ RHS.
    -- Either (ε=1, δ=1) gives ∑A ≥ 0, or (ε=1, δ=-1) gives -∑A ≥ 0.
    by_cases hNonneg : 0 ≤ ∑ i, ∑ j, A i j
    · refine ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
      simp only [mul_one]; linarith
    · push_neg at hNonneg
      refine ⟨fun _ => 1, fun _ => -1, fun _ => Or.inl rfl, fun _ => Or.inr rfl, ?_⟩
      simp only [mul_neg, mul_one, Finset.sum_neg_distrib]; linarith
  · -- Hard case: RHS > 0. This is the core of the Grothendieck inequality.
    push_neg at hRHS
    -- We reduce to the probabilistic method (gaussian_rounding_existence_v2):
    -- it suffices to construct a probability space with random ±1 signs
    -- whose expected score is at least (2γ/π) · ∑ A·t.
    suffices ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
        (_ : MeasureTheory.IsProbabilityMeasure μ)
        (ε' : Ω → Fin n → ℝ) (δ' : Ω → Fin m → ℝ),
        (∀ ω i, ε' ω i = 1 ∨ ε' ω i = -1) ∧
        (∀ ω j, δ' ω j = 1 ∨ δ' ω j = -1) ∧
        MeasureTheory.Integrable (fun ω => ∑ i, ∑ j, A i j * ε' ω i * δ' ω j) μ ∧
        (2 * γ / Real.pi) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) ≤
          ∫ ω, ∑ i, ∑ j, A i j * ε' ω i * δ' ω j ∂μ by
      obtain ⟨Ω, mΩ, μ, hμ, ε', δ', hε', hδ', hInt, hScore⟩ := this
      exact gaussian_rounding_existence_abstract μ n m A
        (2 * γ / Real.pi) H x y ε' δ' hε' hδ' hInt hScore
    -- Apply the pairwise rounding construction
    obtain ⟨Ω', mΩ', μ', hμ', ε'', δ'', hε_sign, hδ_sign, hPairInt, hExpect⟩ :=
      rounding_probability_space_construction γ hγ_pos hγ_lt_one η p hη hp
        F_inv hFa hFi hFS hSummable n m H x y hx hy
    refine ⟨Ω', mΩ', μ', hμ', ε'', δ'', hε_sign, hδ_sign, ?_, ?_⟩
    · -- Integrability: finite sum of integrable functions
      apply integrable_finset_sum Finset.univ
      intro i _
      apply integrable_finset_sum Finset.univ
      intro j _
      change Integrable (fun ω => A i j * ε'' ω i * δ'' ω j) μ'
      have heq : (fun ω => A i j * ε'' ω i * δ'' ω j) = (fun ω => A i j * (ε'' ω i * δ'' ω j)) := by
        ext ω; ring
      rw [heq]
      exact Integrable.const_mul (hPairInt i j) (A i j)
    · -- Expected value bound (holds with equality by linearity)
      apply le_of_eq
      have hInt_outer : ∀ i ∈ Finset.univ,
          Integrable (fun ω => ∑ j, A i j * ε'' ω i * δ'' ω j) μ' := by
        intro i _; apply integrable_finset_sum Finset.univ; intro j _
        have : (fun ω => A i j * ε'' ω i * δ'' ω j) =
            (fun ω => A i j * (ε'' ω i * δ'' ω j)) := by ext ω; ring
        rw [this]; exact Integrable.const_mul (hPairInt i j) (A i j)
      have hInt_inner : ∀ (i : Fin n), ∀ j ∈ Finset.univ,
          Integrable (fun ω => A i j * ε'' ω i * δ'' ω j) μ' := by
        intro i j _
        have : (fun ω => A i j * ε'' ω i * δ'' ω j) =
            (fun ω => A i j * (ε'' ω i * δ'' ω j)) := by ext ω; ring
        rw [this]; exact Integrable.const_mul (hPairInt i j) (A i j)
      rw [integral_finset_sum Finset.univ hInt_outer]
      simp_rw [integral_finset_sum Finset.univ (hInt_inner _)]
      simp_rw [show ∀ (i : Fin n) (j : Fin m),
          (fun ω => A i j * ε'' ω i * δ'' ω j) =
          (fun ω => A i j * (ε'' ω i * δ'' ω j)) from fun i j => by ext ω; ring]
      simp_rw [integral_const_mul, hExpect]
      rw [Finset.mul_sum]; congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j; ring

/-! ### Main theorem assembly -/

/-- **Core rounding inequality**:

    For any n×m real matrix A and unit vectors x, y in a real inner product
    space, the parameters (γ, η, p, F_inv) from Theorem 5.1 yield signs
    ε ∈ {±1}ⁿ, δ ∈ {±1}ᵐ such that
      ∑ᵢⱼ aᵢⱼ εᵢ δⱼ ≥ (2γ/π) · ∑ᵢⱼ aᵢⱼ ⟨xᵢ, yⱼ⟩

    Delegates directly to `gaussian_rounding_with_inverse`. -/
theorem rounding_core_inequality
    (γ : ℝ) (hγ_pos : γ > 0) (hγ_lt_one : γ < 1)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk γ))
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk γ, F_inv z ∈ S)
    (hSummable : summability_condition (taylor_coeff F_inv) γ)
    (n m : ℕ) (A : Fin n → Fin m → ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * ε i * δ j ≥
        (2 * γ / Real.pi) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) :=
  gaussian_rounding_with_inverse γ hγ_pos hγ_lt_one η p hη hp
    F_inv hFa hFi hFS hSummable n m A H x y hx hy

/-! ## Sorry-free probabilistic method (from Rounding_attempt2)

The sorry-free version takes a probability space with random sign functions as input,
rather than asserting existence from a vacuous hypothesis. This is the correct
formulation of the probabilistic method step. -/

/-- If the expected value of f is at least B under a probability measure,
    then some outcome achieves at least B. -/
theorem exists_sample_ge_of_integral_ge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) {B : ℝ}
    (hB : B ≤ ∫ ω, f ω ∂μ) :
    ∃ ω, B ≤ f ω := by
  exact (exists_integral_le hf).imp (fun ω hω => le_trans hB hω)

/-- **Corrected Gaussian rounding existence** (abstract probabilistic-method version):
    Given a probability space with random sign functions whose expected score
    is at least c · ∑ A(i,j) ⟨x_i, y_j⟩, deterministic signs achieving that bound exist. -/
theorem gaussian_rounding_existence_v2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (A : Fin n → Fin m → ℝ) (c : ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (ε : Ω → Fin n → ℝ) (δ : Ω → Fin m → ℝ)
    (hε : ∀ ω i, ε ω i = 1 ∨ ε ω i = -1)
    (hδ : ∀ ω j, δ ω j = 1 ∨ δ ω j = -1)
    (hInt : Integrable (fun ω => ∑ i, ∑ j, A i j * ε ω i * δ ω j) μ)
    (hScore :
      c * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) ≤
        ∫ ω, ∑ i, ∑ j, A i j * ε ω i * δ ω j ∂μ) :
    ∃ (ε0 : Fin n → ℝ) (δ0 : Fin m → ℝ),
      (∀ i, ε0 i = 1 ∨ ε0 i = -1) ∧
      (∀ j, δ0 j = 1 ∨ δ0 j = -1) ∧
      ∑ i, ∑ j, A i j * ε0 i * δ0 j ≥
        c * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) := by
  obtain ⟨ω₀, hω₀⟩ := exists_sample_ge_of_integral_ge μ hInt hScore
  exact ⟨ε ω₀, δ ω₀, hε ω₀, hδ ω₀, hω₀⟩

end Braverman
