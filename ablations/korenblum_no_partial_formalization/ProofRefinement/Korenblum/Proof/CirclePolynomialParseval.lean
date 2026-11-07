import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct

/-!
# Polynomial Bergman-Parseval circle-mean identity

This file is the **direct consumer** of `Proof.CircleExpBridge` (sprint 006,
diagonal monomial seeds) and `Proof.CircleInnerProduct` (sprint 007,
off-diagonal `circleMeanInner` orthogonality plus its diagonal companion). It
exposes the polynomial-level Bergman-Parseval identity:

* `circleMeanInner_add_left`, `circleMeanInner_add_right` — additivity of
  the `ℂ`-valued circle inner product in each slot, with the appropriate
  per-summand integrability hypothesis on the conjugate-product integrand.
* `circleMeanInner_smul_left` — conjugate-linearity in the left slot
  (pulls `(starRingEnd ℂ) c` out). No integrability hypothesis needed:
  `MeasureTheory.integral_const_mul` returns `0 = 0` when the integrand is
  not integrable.
* `circleMeanInner_smul_right` — linearity in the right slot (pulls `c`
  out). Same comment on integrability.
* `circleMeanInner_finset_sum_monomial_left` — Finset-sum-shape consumer
  in the left slot, specialised to monomial coefficients
  `(fun z => ∑ k ∈ s, a k * z ^ k)`.
* `circleMeanInner_finset_sum_monomial_right` — the right-slot dual.
* `circleMeanInner_polynomial_self` — the diagonal polynomial Parseval
  identity for `circleMeanInner`:
  `circleMeanInner (∑ a_k z^k) (∑ a_k z^k) r = ∑ k, ((2π · r^(2k) : ℝ) : ℂ) * ‖a k‖²`.
* `circleMeanSq_polynomial` — the headline real-valued polynomial Parseval
  identity:
  `circleMeanSq (∑ a_k z^k) r = ∑ k, (2π · r^(2k)) * ‖a k‖²`.

Together these pin, in Lean, the algebraic equation at the heart of every
honest Korenblum proof: the `A²` circle-mean of a polynomial is a
coefficient-level termwise sum.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## (1) Sesquilinearity of `circleMeanInner`. -/

/-- Additivity in the left slot. -/
theorem circleMeanInner_add_left
    (f₁ f₂ g : ℂ → ℂ) (r : ℝ)
    (hf₁ : IntegrableOn (fun θ =>
        (starRingEnd ℂ) (f₁ (Complex.polarCoord.symm (r, θ)))
          * g (Complex.polarCoord.symm (r, θ)))
      (Set.Ioo (-Real.pi) Real.pi) volume)
    (hf₂ : IntegrableOn (fun θ =>
        (starRingEnd ℂ) (f₂ (Complex.polarCoord.symm (r, θ)))
          * g (Complex.polarCoord.symm (r, θ)))
      (Set.Ioo (-Real.pi) Real.pi) volume) :
    circleMeanInner (fun z => f₁ z + f₂ z) g r
      = circleMeanInner f₁ g r + circleMeanInner f₂ g r := by
  unfold circleMeanInner
  -- Pointwise: conj(f₁ + f₂) * g = conj f₁ * g + conj f₂ * g.
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ)
              (f₁ (Complex.polarCoord.symm (r, θ))
                + f₂ (Complex.polarCoord.symm (r, θ)))
            * g (Complex.polarCoord.symm (r, θ)))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((starRingEnd ℂ) (f₁ (Complex.polarCoord.symm (r, θ)))
                  * g (Complex.polarCoord.symm (r, θ)))
              + ((starRingEnd ℂ) (f₂ (Complex.polarCoord.symm (r, θ)))
                    * g (Complex.polarCoord.symm (r, θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [map_add, add_mul]
  rw [hpt]
  rw [integral_add hf₁ hf₂]

/-- Additivity in the right slot. -/
theorem circleMeanInner_add_right
    (f g₁ g₂ : ℂ → ℂ) (r : ℝ)
    (hg₁ : IntegrableOn (fun θ =>
        (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
          * g₁ (Complex.polarCoord.symm (r, θ)))
      (Set.Ioo (-Real.pi) Real.pi) volume)
    (hg₂ : IntegrableOn (fun θ =>
        (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
          * g₂ (Complex.polarCoord.symm (r, θ)))
      (Set.Ioo (-Real.pi) Real.pi) volume) :
    circleMeanInner f (fun z => g₁ z + g₂ z) r
      = circleMeanInner f g₁ r + circleMeanInner f g₂ r := by
  unfold circleMeanInner
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
            * (g₁ (Complex.polarCoord.symm (r, θ))
                + g₂ (Complex.polarCoord.symm (r, θ))))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
                  * g₁ (Complex.polarCoord.symm (r, θ)))
              + ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
                    * g₂ (Complex.polarCoord.symm (r, θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [mul_add]
  rw [hpt]
  rw [integral_add hg₁ hg₂]

/-- Conjugate-linearity in the left slot: pulling `c` out of
`circleMeanInner (c · f) g r` yields `(starRingEnd ℂ) c · circleMeanInner f g r`. -/
theorem circleMeanInner_smul_left
    (c : ℂ) (f g : ℂ → ℂ) (r : ℝ) :
    circleMeanInner (fun z => c * f z) g r
      = (starRingEnd ℂ) c * circleMeanInner f g r := by
  unfold circleMeanInner
  -- Pointwise: conj(c * f(...)) * g(...) = conj c * (conj(f(...)) * g(...)).
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) (c * f (Complex.polarCoord.symm (r, θ)))
            * g (Complex.polarCoord.symm (r, θ)))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            (starRingEnd ℂ) c
              * ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
                  * g (Complex.polarCoord.symm (r, θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [map_mul]
    ring
  rw [hpt]
  rw [integral_const_mul]

/-- Linearity in the right slot: `circleMeanInner f (c · g) r = c · circleMeanInner f g r`. -/
theorem circleMeanInner_smul_right
    (c : ℂ) (f g : ℂ → ℂ) (r : ℝ) :
    circleMeanInner f (fun z => c * g z) r
      = c * circleMeanInner f g r := by
  unfold circleMeanInner
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
            * (c * g (Complex.polarCoord.symm (r, θ))))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            c * ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
                  * g (Complex.polarCoord.symm (r, θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    ring
  rw [hpt]
  rw [integral_const_mul]

/-! ## (2) Finset-sum consumers (monomial coefficients). -/

/-- Finset-sum expansion in the left slot, specialised to monomial
coefficients. The integrand `θ ↦ conj((polarCoord.symm (r,θ))^k) * g (...)`
is assumed integrable for each `k ∈ s`. -/
theorem circleMeanInner_finset_sum_monomial_left
    (s : Finset ℕ) (a : ℕ → ℂ) (g : ℂ → ℂ) (r : ℝ)
    (hint : ∀ k ∈ s, IntegrableOn (fun θ =>
        (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
          * g (Complex.polarCoord.symm (r, θ)))
      (Set.Ioo (-Real.pi) Real.pi) volume) :
    circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k) g r
      = ∑ k ∈ s,
          (starRingEnd ℂ) (a k)
            * circleMeanInner (fun z => z ^ k) g r := by
  unfold circleMeanInner
  -- Pointwise rewrite:
  --   conj(∑ k ∈ s, a k * P^k) * g(P)
  --   = ∑ k ∈ s, conj(a k) * (conj(P^k) * g(P))
  -- where P := polarCoord.symm (r, θ).
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ)
              (∑ k ∈ s, a k * (Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
            * g (Complex.polarCoord.symm (r, θ)))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ∑ k ∈ s,
              (starRingEnd ℂ) (a k)
                * ((starRingEnd ℂ)
                      ((Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
                    * g (Complex.polarCoord.symm (r, θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul]
    ring
  rw [hpt]
  -- Swap ∫ and ∑ via integral_finset_sum.
  have hint' : ∀ k ∈ s, Integrable
      (fun θ => (starRingEnd ℂ) (a k)
          * ((starRingEnd ℂ)
                ((Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
              * g (Complex.polarCoord.symm (r, θ))))
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    intro k hk
    exact (hint k hk).const_mul ((starRingEnd ℂ) (a k))
  rw [integral_finset_sum s hint']
  -- Pull conj(a k) out of each individual integral.
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul]

/-- Finset-sum expansion in the right slot, specialised to monomial
coefficients. -/
theorem circleMeanInner_finset_sum_monomial_right
    (s : Finset ℕ) (b : ℕ → ℂ) (f : ℂ → ℂ) (r : ℝ)
    (hint : ∀ k ∈ s, IntegrableOn (fun θ =>
        (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
          * (Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
      (Set.Ioo (-Real.pi) Real.pi) volume) :
    circleMeanInner f (fun z => ∑ k ∈ s, b k * z ^ k) r
      = ∑ k ∈ s,
          b k * circleMeanInner f (fun z => z ^ k) r := by
  unfold circleMeanInner
  -- Pointwise rewrite:
  --   conj(f(P)) * (∑ k ∈ s, b k * P^k)
  --   = ∑ k ∈ s, b k * (conj(f(P)) * P^k)
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
            * ∑ k ∈ s, b k * (Complex.polarCoord.symm (r, θ) : ℂ) ^ k)
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ∑ k ∈ s,
              b k
                * ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
                    * (Complex.polarCoord.symm (r, θ) : ℂ) ^ k) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hpt]
  have hint' : ∀ k ∈ s, Integrable
      (fun θ => b k
          * ((starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
              * (Complex.polarCoord.symm (r, θ) : ℂ) ^ k))
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    intro k hk
    exact (hint k hk).const_mul (b k)
  rw [integral_finset_sum s hint']
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul]

/-! ## (3) Polynomial Parseval at the `ℂ`-valued inner-product level. -/

/-- The integrand `θ ↦ conj((P(r,θ))^m) * (P(r,θ))^n` is integrable on
`Ioo (-π) π`. Used as the per-summand integrability hypothesis when threading
the polynomial expansion through `circleMeanInner_finset_sum_monomial_*`. -/
private lemma continuous_polarCoord_pt (r : ℝ) :
    Continuous (fun θ : ℝ => (Complex.polarCoord.symm (r, θ) : ℂ)) := by
  -- Bridge to `r * exp (θ * I)` via `polarCoord_symm_eq_exp`.
  refine Continuous.congr (f := fun θ : ℝ =>
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ?_ ?_
  · exact continuous_const.mul
      (((Complex.continuous_ofReal).mul continuous_const).cexp)
  · intro θ
    exact (polarCoord_symm_eq_exp r θ).symm

private lemma integrableOn_monomial_pair (r : ℝ) (m n : ℕ) :
    IntegrableOn (fun θ =>
        (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ m)
          * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n)
      (Set.Ioo (-Real.pi) Real.pi) volume := by
  -- The integrand is continuous on ℝ, hence integrable on the bounded
  -- measurable set `Ioo (-π) π` via `Continuous.integrableOn_Ioc`
  -- plus `IntegrableOn.mono_set` with `Ioo_subset_Ioc_self`.
  have hcont : Continuous (fun θ : ℝ =>
      (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ m)
        * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n) := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_conj.comp ((continuous_polarCoord_pt r).pow m)
    · exact (continuous_polarCoord_pt r).pow n
  exact (hcont.integrableOn_Ioc).mono_set Ioo_subset_Ioc_self

/-- The integrand `θ ↦ conj((P(r,θ))^m) * (∑ n ∈ s, b n * (P(r,θ))^n)` is
integrable on `Ioo (-π) π`. -/
private lemma integrableOn_monomial_polynomial (r : ℝ) (m : ℕ)
    (s : Finset ℕ) (b : ℕ → ℂ) :
    IntegrableOn (fun θ =>
        (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ m)
          * ∑ n ∈ s, b n * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n)
      (Set.Ioo (-Real.pi) Real.pi) volume := by
  have hcont : Continuous (fun θ : ℝ =>
      (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ m)
        * ∑ n ∈ s, b n * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n) := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_conj.comp ((continuous_polarCoord_pt r).pow m)
    · refine continuous_finset_sum s (fun n _ => ?_)
      exact continuous_const.mul ((continuous_polarCoord_pt r).pow n)
  exact (hcont.integrableOn_Ioc).mono_set Ioo_subset_Ioc_self

/-- Diagonal polynomial Parseval at the `ℂ`-valued inner-product level. -/
theorem circleMeanInner_polynomial_self
    (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k)
                    (fun z => ∑ k ∈ s, a k * z ^ k) r
      = ∑ k ∈ s, ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ) * ‖a k‖ ^ 2 := by
  -- Step 1: expand the left slot via _finset_sum_monomial_left.
  rw [circleMeanInner_finset_sum_monomial_left s a
        (fun z => ∑ k ∈ s, a k * z ^ k) r
        (fun k _ => integrableOn_monomial_polynomial r k s a)]
  -- Step 2: expand the right slot inside each circleMeanInner (z^k) (∑ a_n z^n) r.
  have hexpand : ∀ k ∈ s,
      circleMeanInner (fun z => z ^ k) (fun z => ∑ n ∈ s, a n * z ^ n) r
        = ∑ n ∈ s, a n * circleMeanInner (fun z => z ^ k) (fun z => z ^ n) r := by
    intro k _
    refine circleMeanInner_finset_sum_monomial_right s a (fun z => z ^ k) r
      (fun n _ => integrableOn_monomial_pair r k n)
  -- Apply hexpand inside the outer sum.
  have hstep2 :
      (∑ k ∈ s, (starRingEnd ℂ) (a k)
          * circleMeanInner (fun z => z ^ k)
              (fun z => ∑ n ∈ s, a n * z ^ n) r)
        = ∑ k ∈ s, (starRingEnd ℂ) (a k)
            * ∑ n ∈ s, a n * circleMeanInner (fun z => z ^ k)
                                  (fun z => z ^ n) r := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hexpand k hk]
  rw [hstep2]
  -- Step 3: distribute conj(a k) into the inner sum so each term is
  --   conj(a k) * a n * circleMeanInner (z^k) (z^n) r.
  have hstep3 :
      (∑ k ∈ s, (starRingEnd ℂ) (a k)
          * ∑ n ∈ s, a n * circleMeanInner (fun z => z ^ k)
                                (fun z => z ^ n) r)
        = ∑ k ∈ s, ∑ n ∈ s, (starRingEnd ℂ) (a k) * a n
            * circleMeanInner (fun z => z ^ k) (fun z => z ^ n) r := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  rw [hstep3]
  -- Step 4: replace each circleMeanInner (z^k) (z^n) r with the value
  --   if n = k then ((2π r^(2k) : ℝ) : ℂ) else 0,
  -- so the inner-sum integrand becomes
  --   if n = k then conj(a k) * a k * ((2π r^(2k) : ℝ) : ℂ) else 0.
  have hdiag : ∀ k ∈ s, ∀ n ∈ s,
      (starRingEnd ℂ) (a k) * a n
          * circleMeanInner (fun z => z ^ k) (fun z => z ^ n) r
        = if n = k then
            (starRingEnd ℂ) (a k) * a k * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ)
          else 0 := by
    intro k _ n _
    by_cases h : n = k
    · subst h
      rw [circleMeanInner_monomial_same n hr]
      rw [if_pos rfl]
    · rw [circleMeanInner_monomial_diff k n (Ne.symm h) r]
      rw [if_neg h]
      ring
  -- Apply hdiag inside the double sum.
  have hstep4 :
      (∑ k ∈ s, ∑ n ∈ s, (starRingEnd ℂ) (a k) * a n
          * circleMeanInner (fun z => z ^ k) (fun z => z ^ n) r)
        = ∑ k ∈ s, ∑ n ∈ s,
            if n = k then
              (starRingEnd ℂ) (a k) * a k
                * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ)
            else 0 := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    refine Finset.sum_congr rfl (fun n hn => ?_)
    exact hdiag k hk n hn
  rw [hstep4]
  -- Step 5: collapse each inner sum via Finset.sum_ite_eq'. The `b` argument
  -- is a constant function (the diagonal value depends only on `k`).
  have hstep5 :
      (∑ k ∈ s, ∑ n ∈ s,
          if n = k then
            (starRingEnd ℂ) (a k) * a k
              * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ)
          else 0)
        = ∑ k ∈ s,
            (starRingEnd ℂ) (a k) * a k
              * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    -- ∑ n ∈ s, (if n = k then C else 0) = C when k ∈ s.
    -- Rewrite the constant body as `(fun _ => C) n` to match `Finset.sum_ite_eq'`.
    have : (∑ n ∈ s,
              if n = k then
                (starRingEnd ℂ) (a k) * a k
                  * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ)
              else 0)
            = ∑ n ∈ s,
                if n = k then
                  (fun _ : ℕ =>
                    (starRingEnd ℂ) (a k) * a k
                      * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ)) n
                else 0 := rfl
    rw [this, Finset.sum_ite_eq' s k
        (fun _ : ℕ =>
          (starRingEnd ℂ) (a k) * a k
            * ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ))]
    rw [if_pos hk]
  rw [hstep5]
  -- Step 6: rewrite each diagonal term as ((2π r^(2k) : ℝ) : ℂ) * ‖a k‖²
  -- using conj(a k) * a k = (‖a k‖² : ℝ) coerced.
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Goal: conj(a k) * a k * ((2π r^(2k) : ℝ) : ℂ) = ((2π r^(2k) : ℝ) : ℂ) * ‖a k‖²
  have hconj : (starRingEnd ℂ) (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
  rw [hconj]
  -- ((‖a k‖² : ℝ) : ℂ) * ((2π r^(2k) : ℝ) : ℂ) = ((2π r^(2k) : ℝ) : ℂ) * (‖a k‖² : ℂ)
  push_cast
  ring

/-! ## (4) The headline real-valued polynomial Parseval. -/

/-- Polynomial Parseval at the `ℝ`-valued circle-mean level. -/
theorem circleMeanSq_polynomial
    (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    circleMeanSq (fun z => ∑ k ∈ s, a k * z ^ k) r
      = ∑ k ∈ s, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
  -- Step 1: bridge to circleMeanInner via circleMeanSq_eq_re_circleMeanInner_self.
  rw [circleMeanSq_eq_re_circleMeanInner_self]
  -- Step 2: evaluate the inner via circleMeanInner_polynomial_self.
  rw [circleMeanInner_polynomial_self s a hr]
  -- Step 3: take .re of the finite ℂ-sum, distributing through Finset.sum_re,
  -- and pull out the real coercion of each term.
  -- Each term is `((2π r^(2k) : ℝ) : ℂ) * ‖a k‖² = (((2π r^(2k)) * ‖a k‖²) : ℝ → ℂ)`.
  -- Using Complex.re_sum and Complex.ofReal_re.
  have hterm : ∀ k ∈ s,
      (((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ) * (‖a k‖ ^ 2 : ℂ)).re
        = (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
    intro k _
    -- Cast ‖a k‖² : ℂ = ((‖a k‖² : ℝ) : ℂ).
    rw [show (‖a k‖ ^ 2 : ℂ) = ((‖a k‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_mul]
    rw [Complex.ofReal_re]
  -- Apply termwise re extraction across the sum.
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  exact hterm k hk

end ProofRefinement.Korenblum
