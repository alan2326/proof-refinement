/-
# Gaussian sign rounding of Krivine's embedding, and the parametric bound

Bricks **D** (rounding/derandomisation) and **E** (assembly) of a from-scratch
Krivine formalization of the Grothendieck inequality.

Brick B (`Proof/KrivineEmbedding.lean`) produces unit vectors with
`⟪x' i, y' j⟫ = sin (c ⟪x i, y j⟫)`, `c = krivineConst = arsinh 1`.
Brick C-b (`Proof/GaussianRoundingPi.lean`) evaluates the Gaussian average of a
product of rounding signs as `(2/π) arcsin ⟪u, v⟫`.  This file composes them:

* *padding* — brick C-b needs `2 ≤ Fintype.card ι`, brick B may land in a
  zero-dimensional space, so vectors are pushed along the inner-product
  preserving inclusion `EuclideanSpace ℝ ι → EuclideanSpace ℝ (ι ⊕ Fin 2)`;
* *linearity* — the Gaussian average of the rounded bilinear form is
  `∑ᵢ∑ⱼ Aᵢⱼ (2/π) arcsin ⟪uᵢ, vⱼ⟫`;
* *derandomisation* — one Gaussian sample does at least as well as the average
  (`exists_ge_integral_gaussDensity` from `Proof/GaussianMean.lean`);
* *assembly* — `arcsin (sin (c t)) = c t` since `|c t| ≤ c ≤ 1 < π/2`, so the
  average is `(2c/π) S` with `S` the SDP value, and the sign flip
  `ε ↦ -ε` closes the branch `S < 0`.

The main results are

* `padVec`, `inner_padVec`, `norm_padVec` -- the padding embedding;
* `roundingSum` -- the rounded bilinear form at a Gaussian sample;
* `integral_roundingSum` -- its Gaussian average;
* `exists_signs_ge` -- **brick D**;
* `grothendieckIneq_of_pi_le` -- **brick E**.
-/
import ProofRefinement.Lemma54.Proof.KrivineEmbedding
import ProofRefinement.Lemma54.Proof.GaussianMean
import ProofRefinement.Lemma54.Proof.CandidateContract

noncomputable section

namespace ProofRefinement.Lemma54

open Real MeasureTheory Set

set_option linter.unusedSectionVars false

/-! ### Padding: `EuclideanSpace ℝ ι → EuclideanSpace ℝ (ι ⊕ Fin 2)` -/

/-- Pad a Euclidean vector with two extra zero coordinates.  This is the
inner-product-preserving inclusion that lets brick C-b (which needs ambient
dimension `≥ 2`) be applied to the output of brick B (which may be
zero-dimensional). -/
def padVec {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ Fin 2) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0)

@[simp] theorem padVec_apply_inl {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (i : ι) :
    padVec x (Sum.inl i) = x i := rfl

@[simp] theorem padVec_apply_inr {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (k : Fin 2) :
    padVec x (Sum.inr k) = 0 := rfl

/-- Padding preserves inner products. -/
theorem inner_padVec {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    (inner ℝ (padVec x) (padVec y) : ℝ) = inner ℝ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp [RCLike.inner_apply]

/-- Padding preserves norms. -/
theorem norm_padVec {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖padVec x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_padVec]

/-- The padded index type always has at least two elements. -/
theorem two_le_card_sum_fin_two (ι : Type*) [Fintype ι] : 2 ≤ Fintype.card (ι ⊕ Fin 2) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.le_add_left 2 _

/-! ### The rounding functional -/

/-- The bilinear form `A` evaluated at the sign vectors obtained by rounding the
families `u`, `v` against the sample `x`. -/
def roundingSum {n m : ℕ} {ι : Type*} [Fintype ι] (A : Fin n → Fin m → ℝ)
    (u : Fin n → EuclideanSpace ℝ ι) (v : Fin m → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, A i j * (signOne (inner ℝ (u i) x) * signOne (inner ℝ (v j) x))

theorem measurable_signOne_inner {ι : Type*} [Fintype ι] (u : EuclideanSpace ℝ ι) :
    Measurable (fun x : EuclideanSpace ℝ ι => signOne (inner ℝ u x)) := by
  refine measurable_signOne.comp (Continuous.measurable ?_)
  exact continuous_const.inner (continuous_id : Continuous fun x : EuclideanSpace ℝ ι => x)

theorem measurable_roundingSum {n m : ℕ} {ι : Type*} [Fintype ι] (A : Fin n → Fin m → ℝ)
    (u : Fin n → EuclideanSpace ℝ ι) (v : Fin m → EuclideanSpace ℝ ι) :
    Measurable (roundingSum A u v) := by
  unfold roundingSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact measurable_const.mul ((measurable_signOne_inner (u i)).mul (measurable_signOne_inner (v j)))

theorem abs_roundingSum_le {n m : ℕ} {ι : Type*} [Fintype ι] (A : Fin n → Fin m → ℝ)
    (u : Fin n → EuclideanSpace ℝ ι) (v : Fin m → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : |roundingSum A u v x| ≤ ∑ i, ∑ j, |A i j| := by
  unfold roundingSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_signOne, abs_signOne, one_mul, mul_one]

/-! ### The Gaussian average (brick D core) -/

/-- **The Gaussian average of the rounded bilinear form.**  Termwise this is
brick C-b; the only work is pushing the density inside the double sum and
pulling the constants `A i j` out of the integrals. -/
theorem integral_roundingSum {ι : Type*} [Fintype ι] (h2 : 2 ≤ Fintype.card ι) {n m : ℕ}
    (A : Fin n → Fin m → ℝ) {u : Fin n → EuclideanSpace ℝ ι} {v : Fin m → EuclideanSpace ℝ ι}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    ∫ x : EuclideanSpace ℝ ι, gaussDensity x * roundingSum A u v x
      = ∑ i, ∑ j, A i j * (2 / π * Real.arcsin (inner ℝ (u i) (v j))) := by
  have hmeas : ∀ (i : Fin n) (j : Fin m),
      Measurable (fun x : EuclideanSpace ℝ ι =>
        signOne (inner ℝ (u i) x) * signOne (inner ℝ (v j) x)) :=
    fun i j => (measurable_signOne_inner (u i)).mul (measurable_signOne_inner (v j))
  have hbdd : ∀ (i : Fin n) (j : Fin m) (x : EuclideanSpace ℝ ι),
      |signOne (inner ℝ (u i) x) * signOne (inner ℝ (v j) x)| ≤ 1 := by
    intro i j x
    rw [abs_mul, abs_signOne, abs_signOne, one_mul]
  have hint : ∀ (i : Fin n) (j : Fin m),
      Integrable (fun x : EuclideanSpace ℝ ι => A i j * (gaussDensity x *
        (signOne (inner ℝ (u i) x) * signOne (inner ℝ (v j) x)))) :=
    fun i j => (integrable_gaussDensity_mul (hmeas i j) (hbdd i j)).const_mul _
  have hpt : ∀ x : EuclideanSpace ℝ ι, gaussDensity x * roundingSum A u v x
      = ∑ i, ∑ j, A i j * (gaussDensity x *
          (signOne (inner ℝ (u i) x) * signOne (inner ℝ (v j) x))) := by
    intro x
    unfold roundingSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_gauss_signOne h2 (u i) (v j) (hu i) (hv j)]

/-! ### Derandomisation (brick D) -/

/-- **Brick D.**  Some single pair of sign vectors does at least as well as the
Gaussian average `∑ᵢ∑ⱼ Aᵢⱼ (2/π) arcsin ⟪uᵢ, vⱼ⟫`. -/
theorem exists_signs_ge {ι : Type*} [Fintype ι] (h2 : 2 ≤ Fintype.card ι) {n m : ℕ}
    (A : Fin n → Fin m → ℝ) {u : Fin n → EuclideanSpace ℝ ι} {v : Fin m → EuclideanSpace ℝ ι}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * (2 / π * Real.arcsin (inner ℝ (u i) (v j))) ≤
        ∑ i, ∑ j, A i j * ε i * δ j := by
  obtain ⟨x₀, hx₀⟩ := exists_ge_integral_gaussDensity (F := roundingSum A u v)
    (measurable_roundingSum A u v) (abs_roundingSum_le A u v)
  rw [integral_roundingSum h2 A hu hv] at hx₀
  refine ⟨fun i => signOne (inner ℝ (u i) x₀), fun j => signOne (inner ℝ (v j) x₀),
    fun i => signOne_eq_one_or_neg_one _, fun j => signOne_eq_one_or_neg_one _, ?_⟩
  refine hx₀.trans_eq ?_
  unfold roundingSum
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

/-! ### `krivineConst ≤ 1` -/

/-- `arsinh 1 ≤ 1`, because `1 < sinh 1`. -/
theorem krivineConst_le_one : krivineConst ≤ 1 := by
  have h1 : (1 : ℝ) < Real.sinh 1 := Real.self_lt_sinh_iff.mpr one_pos
  have h2 : Real.arsinh 1 ≤ Real.arsinh (Real.sinh 1) := Real.arsinh_le_arsinh.mpr h1.le
  rwa [Real.arsinh_sinh] at h2

/-! ### Assembly (brick E) -/

/-- **Brick E: the parametric Grothendieck bound.**  Every `K > 0` with
`π ≤ 2 · arsinh 1 · K` satisfies the Grothendieck inequality.

The hypothesis `hpi` is used only on the branch where the SDP value is
nonnegative; when it is negative the sign flip `ε ↦ -ε` already gives a
nonnegative rounded value. -/
theorem grothendieckIneq_of_pi_le {K : ℝ} (hK : 0 < K) (hpi : π ≤ 2 * krivineConst * K) :
    GrothendieckIneq K := by
  refine ⟨hK, ?_⟩
  intro n m A H _ _ x y hx hy
  obtain ⟨x', y', hx'1, hy'1, hxy'⟩ := exists_krivine_embedding x y hx hy
  set S : ℝ := ∑ i, ∑ j, A i j * (inner ℝ (x i) (y j) : ℝ) with hS
  -- pad the Krivine vectors so that the ambient dimension is at least two
  set u : Fin n → EuclideanSpace ℝ ((Fin n ⊕ Fin m) ⊕ Fin 2) := fun i => padVec (x' i) with hudef
  set v : Fin m → EuclideanSpace ℝ ((Fin n ⊕ Fin m) ⊕ Fin 2) := fun j => padVec (y' j) with hvdef
  have hu : ∀ i, ‖u i‖ = 1 := fun i => by rw [hudef, norm_padVec]; exact hx'1 i
  have hv : ∀ j, ‖v j‖ = 1 := fun j => by rw [hvdef, norm_padVec]; exact hy'1 j
  obtain ⟨ε, δ, hε, hδ, hle⟩ :=
    exists_signs_ge (two_le_card_sum_fin_two (Fin n ⊕ Fin m)) A hu hv
  -- the average is exactly `(2 c / π) S`
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have harc : ∀ (i : Fin n) (j : Fin m),
      Real.arcsin (inner ℝ (u i) (v j)) = krivineConst * (inner ℝ (x i) (y j) : ℝ) := by
    intro i j
    have hinner : (inner ℝ (u i) (v j) : ℝ)
        = Real.sin (krivineConst * (inner ℝ (x i) (y j) : ℝ)) := by
      rw [hudef, hvdef, inner_padVec]
      exact hxy' i j
    rw [hinner]
    have habs : |(inner ℝ (x i) (y j) : ℝ)| ≤ 1 := by
      have h := abs_real_inner_le_norm (x i) (y j)
      rwa [hx i, hy j, mul_one] at h
    have hb : |krivineConst * (inner ℝ (x i) (y j) : ℝ)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg krivineConst_nonneg]
      calc krivineConst * |(inner ℝ (x i) (y j) : ℝ)| ≤ krivineConst * 1 := by
            exact mul_le_mul_of_nonneg_left habs krivineConst_nonneg
        _ ≤ 1 := by rw [mul_one]; exact krivineConst_le_one
    have hhalf : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
    rw [abs_le] at hb
    exact Real.arcsin_sin (by linarith [hb.1]) (by linarith [hb.2])
  have havg : ∑ i, ∑ j, A i j * (2 / π * Real.arcsin (inner ℝ (u i) (v j)))
      = (2 * krivineConst / π) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [harc i j]
    field_simp
  rw [havg] at hle
  -- close by the sign of `S`
  rcases le_or_gt 0 S with hSnn | hSneg
  · refine ⟨ε, δ, hε, hδ, ?_⟩
    have hcoef : 1 / K ≤ 2 * krivineConst / π := by
      rw [div_le_div_iff₀ hK hpi_pos]
      linarith [hpi]
    have hmono : (1 / K) * S ≤ (2 * krivineConst / π) * S :=
      mul_le_mul_of_nonneg_right hcoef hSnn
    exact le_trans hmono hle
  · have hneg : (1 / K) * S < 0 := mul_neg_of_pos_of_neg (by positivity) hSneg
    rcases le_or_gt 0 (∑ i, ∑ j, A i j * ε i * δ j) with hpos | hlt
    · exact ⟨ε, δ, hε, hδ, by linarith⟩
    · have hflip : ∑ i, ∑ j, A i j * (-ε i) * δ j = -∑ i, ∑ j, A i j * ε i * δ j := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      refine ⟨fun i => -ε i, δ, ?_, hδ, ?_⟩
      · intro i
        change -ε i = 1 ∨ -ε i = -1
        rcases hε i with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h]; norm_num)
      · change (1 / K) * S ≤ ∑ i, ∑ j, A i j * (-ε i) * δ j
        rw [hflip]
        linarith

end ProofRefinement.Lemma54
