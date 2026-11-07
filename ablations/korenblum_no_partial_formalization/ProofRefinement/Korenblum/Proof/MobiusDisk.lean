import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract

/-!
# Möbius unit-disk automorphism: the algebraic / analytic primitive

This file pins the four-plus-one core theorems for the Möbius automorphism
`φ_a : ℂ → ℂ` on the unit disk, defined by

```
φ_a(z) := (a - z) / (1 - conj(a) * z)
```

against the workspace's set-level `UnitDisk : Set ℂ`. The exposed surface is:

* `mobiusDisk_denom_ne_zero` — denominator non-vanishing on the closed unit
  disk for an interior `a`,
* `mobiusDisk_one_sub_normSq` — the Schwarz–Pick algebraic identity
  `1 - ‖φ_a z‖² = (1 - ‖a‖²)(1 - ‖z‖²) / ‖1 - conj(a)·z‖²`,
* `mobiusDisk_mapsTo` — `φ_a` is a self-map of `UnitDisk`,
* `mobiusDisk_involution` — `φ_a ∘ φ_a = id` on `UnitDisk`,
* `mobiusDisk_analyticOn` — `φ_a` is analytic on `UnitDisk`.

These are the algebraic / analytic primitives every downstream Schwarz–Pick,
pseudohyperbolic-distance, or Bergman-A² conformal-invariance argument
factors through. The whole file is self-contained against Mathlib plus
`Proof.CandidateContract` (only for the `UnitDisk` definition).
-/

open Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- The Möbius unit-disk automorphism centered at `a ∈ UnitDisk`:
`φ_a(z) = (a - z) / (1 - conj(a) * z)`. Self-inverse, holomorphic
on `UnitDisk`, sends `UnitDisk` to `UnitDisk`. -/
noncomputable def mobiusDisk (a z : ℂ) : ℂ :=
  (a - z) / (1 - (starRingEnd ℂ) a * z)

/-- Membership bridge between `UnitDisk` and `‖z‖ < 1`.
(Re-derived inline; the version in `Proof/InnerRadialReduction.lean` is
`private` to that file.) -/
private theorem mem_unitDisk_iff_norm_lt_one {z : ℂ} :
    z ∈ UnitDisk ↔ ‖z‖ < 1 := by
  unfold UnitDisk
  rw [Metric.mem_ball, dist_zero_right]

/-- **(1) Denominator non-vanishing.**

For `a ∈ UnitDisk` (so `‖a‖ < 1`) and any `z` with `‖z‖ ≤ 1`, the Möbius
denominator `1 - conj(a) · z` is non-zero. The argument is the reverse
triangle inequality: `‖conj(a) · z‖ ≤ ‖a‖ < 1`, so `1 - conj(a) z` cannot
be zero (else its norm would be 1). -/
theorem mobiusDisk_denom_ne_zero
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  have ha_lt : ‖a‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp ha
  have h_norm_lt : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖
        ≤ ‖a‖ * 1 := by
          apply mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = ‖a‖ := mul_one _
      _ < 1 := ha_lt
  intro h
  -- h : 1 - conj(a)*z = 0  ⇒  conj(a)*z = 1  ⇒  ‖conj(a)*z‖ = 1
  have h_eq : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have h_norm_eq : ‖(starRingEnd ℂ) a * z‖ = 1 := by
    rw [h_eq, norm_one]
  linarith

/-- **(2) The Schwarz–Pick algebraic identity.**

For `a ∈ UnitDisk` (so `‖a‖ < 1`) and any `z` with `‖z‖ < 1`,

`1 - ‖φ_a z‖² = (1 - ‖a‖²)(1 - ‖z‖²) / ‖1 - conj(a)·z‖²`.

This is the load-bearing algebraic identity at the heart of every Möbius /
pseudohyperbolic argument on the unit disk. Proof is direct: expand
`normSq` of `(a - z)` and `(1 - conj(a) z)` via `Complex.normSq_sub`, then
subtract and simplify with `field_simp` / `ring`. -/
theorem mobiusDisk_one_sub_normSq
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    1 - ‖mobiusDisk a z‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
  -- Set up the denominator and its non-vanishing.
  set D : ℂ := 1 - (starRingEnd ℂ) a * z with hD_def
  have hz_le : ‖z‖ ≤ 1 := le_of_lt hz
  have hD_ne : D ≠ 0 := mobiusDisk_denom_ne_zero ha hz_le
  have hD_normSq_pos : 0 < normSq D := normSq_pos.mpr hD_ne
  have hD_normSq_ne : normSq D ≠ 0 := ne_of_gt hD_normSq_pos
  -- Reduce ‖·‖² to normSq via Complex.sq_norm.
  have h_sq_phi : ‖mobiusDisk a z‖ ^ 2 = normSq (mobiusDisk a z) :=
    Complex.sq_norm _
  have h_sq_a : ‖a‖ ^ 2 = normSq a := Complex.sq_norm _
  have h_sq_z : ‖z‖ ^ 2 = normSq z := Complex.sq_norm _
  have h_sq_D : ‖D‖ ^ 2 = normSq D := Complex.sq_norm _
  -- ‖φ_a z‖² = normSq(a - z) / normSq(D).
  have h_phi : mobiusDisk a z = (a - z) / D := rfl
  have h_phi_sq : normSq (mobiusDisk a z) = normSq (a - z) / normSq D := by
    rw [h_phi, normSq_div]
  -- Normalize each side via Complex.normSq_sub.
  have h_normSq_az :
      normSq (a - z)
        = normSq a + normSq z - 2 * (a * (starRingEnd ℂ) z).re :=
    Complex.normSq_sub a z
  have h_normSq_D_raw :
      normSq (1 - (starRingEnd ℂ) a * z)
        = normSq (1 : ℂ) + normSq ((starRingEnd ℂ) a * z)
            - 2 * ((1 : ℂ) * (starRingEnd ℂ) ((starRingEnd ℂ) a * z)).re :=
    Complex.normSq_sub (1 : ℂ) ((starRingEnd ℂ) a * z)
  -- normSq(conj(a) * z) = normSq(a) * normSq(z).
  have h_normSq_conj_mul :
      normSq ((starRingEnd ℂ) a * z) = normSq a * normSq z := by
    rw [Complex.normSq_mul, Complex.normSq_conj]
  -- (1 * conj(conj(a) * z)).re = (a * conj z).re.
  have h_re_eq :
      ((1 : ℂ) * (starRingEnd ℂ) ((starRingEnd ℂ) a * z)).re
        = (a * (starRingEnd ℂ) z).re := by
    have h_simp :
        (1 : ℂ) * (starRingEnd ℂ) ((starRingEnd ℂ) a * z)
          = a * (starRingEnd ℂ) z := by
      rw [one_mul, map_mul, Complex.conj_conj]
    rw [h_simp]
  -- Combine into the form for D = 1 - conj(a)*z.
  have h_normSq_D :
      normSq D = 1 + normSq a * normSq z - 2 * (a * (starRingEnd ℂ) z).re := by
    change normSq (1 - (starRingEnd ℂ) a * z) = _
    rw [h_normSq_D_raw, Complex.normSq_one, h_normSq_conj_mul, h_re_eq]
  -- Non-vanishing of normSq D (in expanded form, for field_simp).
  have h_expanded_ne :
      (1 + normSq a * normSq z - 2 * (a * (starRingEnd ℂ) z).re) ≠ 0 := by
    rw [← h_normSq_D]; exact hD_normSq_ne
  -- Goal becomes: 1 - normSq(a-z)/normSq(D) = (1 - normSq a)(1 - normSq z) / normSq(D)
  -- (with the ‖·‖² ↔ normSq translation taking care of all the squared norms).
  rw [h_sq_phi, h_sq_a, h_sq_z, h_sq_D, h_phi_sq]
  -- Algebraic finish: clear denominators with field_simp, then `ring`
  -- using h_normSq_az and h_normSq_D. We first rewrite away the `normSq D`
  -- on both sides via h_normSq_D so field_simp/ring can do the algebra
  -- entirely over the already-expanded forms.
  rw [h_normSq_az, h_normSq_D]
  field_simp
  ring

/-- **(3) `φ_a` maps `UnitDisk` into `UnitDisk`.**

Direct consequence of (2): for `a, z ∈ UnitDisk`, the RHS of the Schwarz–Pick
identity is positive (positive numerator over positive denominator), so
`1 - ‖φ_a z‖² > 0`, hence `‖φ_a z‖ < 1`. -/
theorem mobiusDisk_mapsTo
    {a : ℂ} (ha : a ∈ UnitDisk) :
    Set.MapsTo (mobiusDisk a) UnitDisk UnitDisk := by
  intro z hz
  have ha_lt : ‖a‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp ha
  have hz_lt : ‖z‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp hz
  have hz_le : ‖z‖ ≤ 1 := le_of_lt hz_lt
  have hD_ne : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    mobiusDisk_denom_ne_zero ha hz_le
  have hD_norm_pos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := norm_pos_iff.mpr hD_ne
  have hD_normSq_pos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by positivity
  have h_a_sq_lt : ‖a‖ ^ 2 < 1 := by
    have : ‖a‖ ^ 2 < 1 ^ 2 := by
      apply sq_lt_sq' <;> [linarith [norm_nonneg a]; exact ha_lt]
    simpa using this
  have h_z_sq_lt : ‖z‖ ^ 2 < 1 := by
    have : ‖z‖ ^ 2 < 1 ^ 2 := by
      apply sq_lt_sq' <;> [linarith [norm_nonneg z]; exact hz_lt]
    simpa using this
  -- 1 - ‖a‖² > 0  and  1 - ‖z‖² > 0  ⇒  RHS > 0  ⇒  1 - ‖φ_a z‖² > 0.
  have h_num_pos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> linarith
  have h_RHS_pos :
      0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)
            / ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
    exact div_pos h_num_pos hD_normSq_pos
  have h_id := mobiusDisk_one_sub_normSq ha hz_lt
  have h_phi_sq_lt : ‖mobiusDisk a z‖ ^ 2 < 1 := by linarith
  -- Conclude ‖φ_a z‖ < 1.
  have h_phi_lt : ‖mobiusDisk a z‖ < 1 := by
    have h_nonneg : 0 ≤ ‖mobiusDisk a z‖ := norm_nonneg _
    nlinarith [h_phi_sq_lt, h_nonneg]
  exact mem_unitDisk_iff_norm_lt_one.mpr h_phi_lt

/-- **(4) Involution.** `φ_a (φ_a z) = z` for `z ∈ UnitDisk`.

This is the involution property that makes `φ_a` an automorphism (specifically
self-inverse) of the unit disk. Proof is direct algebra: expand
`φ_a(φ_a z) = (a - φ_a z) / (1 - conj(a) · φ_a z)`, then `field_simp` and
`ring` clear out the inner `(1 - conj(a) z)` denominator. The two
non-vanishing conditions come from (1). -/
theorem mobiusDisk_involution
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : z ∈ UnitDisk) :
    mobiusDisk a (mobiusDisk a z) = z := by
  have ha_lt : ‖a‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp ha
  have hz_lt : ‖z‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp hz
  have hz_le : ‖z‖ ≤ 1 := le_of_lt hz_lt
  -- Inner-denominator non-vanishing: 1 - conj(a) z ≠ 0.
  have hD_ne : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    mobiusDisk_denom_ne_zero ha hz_le
  -- The image φ_a z is in UnitDisk (so its norm is < 1, and ≤ 1).
  have hphi_mem : mobiusDisk a z ∈ UnitDisk :=
    mobiusDisk_mapsTo ha hz
  have hphi_lt : ‖mobiusDisk a z‖ < 1 :=
    mem_unitDisk_iff_norm_lt_one.mp hphi_mem
  have hphi_le : ‖mobiusDisk a z‖ ≤ 1 := le_of_lt hphi_lt
  -- Outer-denominator non-vanishing: 1 - conj(a) (φ_a z) ≠ 0.
  have hD2_ne :
      1 - (starRingEnd ℂ) a * (mobiusDisk a z) ≠ 0 :=
    mobiusDisk_denom_ne_zero ha hphi_le
  -- After clearing the inner denominator, the outer denominator equals
  -- 1 - a · conj(a) (this is the algebraic identity that drives the involution).
  -- We need 1 - a · conj(a) ≠ 0 to clear it via field_simp.
  have hone_sub_acaa_ne : (1 : ℂ) - a * (starRingEnd ℂ) a ≠ 0 := by
    -- a * conj(a) = (normSq a : ℂ) and normSq a < 1.
    have h_ac : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) := by
      rw [mul_comm]
      exact_mod_cast Complex.normSq_eq_conj_mul_self.symm
    rw [h_ac]
    have ha_sq : ‖a‖ ^ 2 < 1 := by
      have : ‖a‖ ^ 2 < 1 ^ 2 := by
        apply sq_lt_sq' <;> [linarith [norm_nonneg a]; exact ha_lt]
      simpa using this
    have h_normSq_lt : Complex.normSq a < 1 := by
      rw [← Complex.sq_norm a]; exact ha_sq
    intro h
    have h_real : (Complex.normSq a : ℂ) = 1 := by linear_combination -h
    have h_eq : Complex.normSq a = 1 := by exact_mod_cast h_real
    linarith
  -- Algebraic finish. The strategy: simplify outer denominator first, then
  -- multiply through by the inner denominator D = 1 - conj(a) z.
  -- We will show:
  --   φ_a(φ_a z) = (a - φ_a z) / (1 - conj(a) · φ_a z)
  --              = ((aD - (a-z))/D) / ((D - conj(a)(a-z))/D)
  --              = (aD - (a-z)) / (D - conj(a)(a-z))
  -- where the key identities are
  --   aD - (a-z) = a(1 - conj(a) z) - a + z = z - a · conj(a) · z = z (1 - a conj(a))
  --   D - conj(a)(a-z) = (1 - conj(a) z) - conj(a) a + conj(a) z = 1 - a · conj(a)
  -- So φ_a(φ_a z) = z (1 - a conj(a)) / (1 - a conj(a)) = z.
  change (a - mobiusDisk a z) / (1 - (starRingEnd ℂ) a * mobiusDisk a z) = z
  -- Substitute φ_a z = (a - z) / D.
  have h_phi_eq : mobiusDisk a z = (a - z) / (1 - (starRingEnd ℂ) a * z) := rfl
  rw [h_phi_eq]
  -- Rewrite numerator and denominator as fractions over D.
  set D : ℂ := 1 - (starRingEnd ℂ) a * z with hD_def
  -- Numerator: a - (a - z) / D = (a · D - (a - z)) / D.
  -- Denominator: 1 - conj(a) · (a - z) / D = (D - conj(a) (a - z)) / D.
  have h_num : a - (a - z) / D = (a * D - (a - z)) / D := by
    field_simp
  have h_den :
      1 - (starRingEnd ℂ) a * ((a - z) / D)
        = (D - (starRingEnd ℂ) a * (a - z)) / D := by
    field_simp
  rw [h_num, h_den]
  -- (a · D - (a - z)) / D ÷ ((D - conj(a)(a - z)) / D)
  --   = (a · D - (a - z)) / (D - conj(a)(a - z))    (cancel the D's)
  rw [div_div_div_cancel_right₀ hD_ne]
  -- Now compute: aD - (a-z) = z - a·conj(a)·z = z (1 - a·conj(a))
  -- and D - conj(a)(a-z) = 1 - a·conj(a).
  have hD_unfold : D = 1 - (starRingEnd ℂ) a * z := hD_def
  have h_num_eq :
      a * D - (a - z) = z * (1 - a * (starRingEnd ℂ) a) := by
    rw [hD_unfold]; ring
  have h_den_eq :
      D - (starRingEnd ℂ) a * (a - z) = 1 - a * (starRingEnd ℂ) a := by
    rw [hD_unfold]; ring
  rw [h_num_eq, h_den_eq]
  -- z · (1 - a · conj(a)) / (1 - a · conj(a)) = z.
  exact mul_div_cancel_right₀ z hone_sub_acaa_ne

/-- **(5) Analyticity.** `φ_a` is analytic on `UnitDisk` for `a ∈ UnitDisk`.

`mobiusDisk a` is a rational function; numerator `a - z` and denominator
`1 - conj(a) z` are entire, and the denominator is non-vanishing on
`UnitDisk` by (1) (since `UnitDisk ⊆ closed unit disk`). Apply
`AnalyticOn.div`. -/
theorem mobiusDisk_analyticOn
    {a : ℂ} (ha : a ∈ UnitDisk) :
    AnalyticOn ℂ (mobiusDisk a) UnitDisk := by
  -- Numerator: z ↦ a - z.
  have h_num : AnalyticOn ℂ (fun z : ℂ => a - z) UnitDisk :=
    analyticOn_const.sub analyticOn_id
  -- Denominator: z ↦ 1 - conj(a) * z.
  have h_den : AnalyticOn ℂ (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) UnitDisk :=
    analyticOn_const.sub (analyticOn_const.mul analyticOn_id)
  -- Denominator non-vanishing on UnitDisk.
  have h_den_ne : ∀ z ∈ UnitDisk, (1 - (starRingEnd ℂ) a * z) ≠ 0 := by
    intro z hz
    have hz_lt : ‖z‖ < 1 := mem_unitDisk_iff_norm_lt_one.mp hz
    exact mobiusDisk_denom_ne_zero ha (le_of_lt hz_lt)
  -- Combine via AnalyticOn.div.
  have h_div :
      AnalyticOn ℂ (fun z : ℂ => (a - z) / (1 - (starRingEnd ℂ) a * z))
        UnitDisk :=
    h_num.div h_den h_den_ne
  -- The function `mobiusDisk a` is definitionally this.
  exact h_div

end ProofRefinement.Korenblum
