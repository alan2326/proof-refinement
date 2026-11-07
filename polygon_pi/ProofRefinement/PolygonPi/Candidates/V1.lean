-- @parent V0
import ProofRefinement.PolygonPi.Proof.Main

/-!
# V1 — tight fourth-order Taylor cubic

`kappa = 2/3`, `lambda = 0`, score `2/3`.

Replaces V0's cubic estimator `sin x > x - x^3/4` (from `Real.sin_gt_sub_cube`)
with the tight Taylor lower bound `sin x > x - x^3/6` for `x > 0`, proved here
via `strictMonoOn_of_deriv_pos` on `f x = sin x - x + x^3/6`. The derivative
`cos x - 1 + x^2/2` is positive for `x > 0` by `Real.one_sub_sq_div_two_lt_cos`.

At `x = π / 2^(n+2)` and multiplied by `2^(n+2)`, this yields
`π - polygonLower n < π^3 / (96 * 4^n)`; combined with the same `π ≤ 4` bound
V0 uses (giving `π^3 ≤ 64`), we obtain
`π - polygonLower n < (2/3) / 4^n`, so `kappa = 2/3` closes the contract.

The lower conjunct is unchanged from V0: `lambda = 0` reduces it to
`polygonLower_lt_pi`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V1

open ProofRefinement.PolygonPi PolygonCore

/-- Lower error coefficient. Unchanged from V0. -/
def lambda : ℝ := 0

/-- Upper error coefficient, driven down by the tight cubic Taylor bound. -/
def kappa : ℝ := 2 / 3

/-- The tight fourth-order Taylor lower bound: `x - x^3/6 < sin x` for all
`x > 0`.

Proof: let `f x = sin x - x + x^3/6`. Then `f 0 = 0` and
`f'(x) = cos x - 1 + x^2/2 > 0` for `x > 0` by
`Real.one_sub_sq_div_two_lt_cos`. Apply `strictMonoOn_of_deriv_pos` on
`Set.Ici 0`, whose interior is `Set.Ioi 0`. -/
lemma sin_gt_sub_cube_div_six {x : ℝ} (hx : 0 < x) :
    x - x ^ 3 / 6 < Real.sin x := by
  set f : ℝ → ℝ := fun t => Real.sin t - t + t ^ 3 / 6 with hf_def
  -- f is continuous on Ici 0 (indeed everywhere), handled by `fun_prop`.
  have hcont : ContinuousOn f (Set.Ici (0 : ℝ)) := by
    change ContinuousOn (fun t => Real.sin t - t + t ^ 3 / 6) (Set.Ici (0 : ℝ))
    fun_prop
  -- Derivative of f at every point.
  have hderiv : ∀ t : ℝ, HasDerivAt f (Real.cos t - 1 + t ^ 2 / 2) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos t) t :=
      Real.hasDerivAt_sin t
    have h2 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) ((3 : ℕ) * t ^ (3 - 1)) t :=
      hasDerivAt_pow 3 t
    have h3' : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (3 * t ^ 2 / 6) t := by
      have := h3.div_const (6 : ℝ)
      -- rewrite `(3 : ℕ) * t^(3-1)` to `3 * t^2`
      simpa using this
    have hcombined :
        HasDerivAt f ((Real.cos t - 1) + 3 * t ^ 2 / 6) t := by
      exact (h1.sub h2).add h3'
    -- Match the stated derivative form.
    have hrw : (Real.cos t - 1) + 3 * t ^ 2 / 6 = Real.cos t - 1 + t ^ 2 / 2 := by
      ring
    rw [hrw] at hcombined
    exact hcombined
  -- Derivative is positive on the interior of Ici 0, which is Ioi 0.
  have hderiv_pos : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv f t := by
    intro t ht
    rw [interior_Ici] at ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hcos := Real.one_sub_sq_div_two_lt_cos htne
    -- deriv f t = cos t - 1 + t^2/2
    have hdt : deriv f t = Real.cos t - 1 + t ^ 2 / 2 := (hderiv t).deriv
    rw [hdt]
    linarith
  -- Assemble the strict monotonicity.
  have hmono : StrictMonoOn f (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv_pos
  have hzero : f 0 = 0 := by simp [f]
  have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hxmem : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hx.le
  have hfx : f 0 < f x := hmono h0mem hxmem hx
  rw [hzero] at hfx
  -- 0 < f x = sin x - x + x^3/6, i.e. x - x^3/6 < sin x.
  have : (0 : ℝ) < Real.sin x - x + x ^ 3 / 6 := hfx
  linarith

theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := by
  refine ⟨by norm_num [lambda], by norm_num [kappa], fun n => ⟨?_, ?_⟩⟩
  · -- Lower conjunct: `lambda = 0` reduces this to the trusted bound.
    simpa [lambda] using polygonLower_lt_pi n
  · -- Upper conjunct.
    have hN : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hx : 0 < Real.pi / 2 ^ (n + 2) := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hpow : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    -- The tight cubic estimate, scaled by the number of sides. No `x ≤ 1`
    -- side condition needed with the `/6` bound.
    have hcube := sin_gt_sub_cube_div_six hx
    have key : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6)
        < polygonLower n := by
      rw [polygonLower_eq_mul_sin]
      exact mul_lt_mul_of_pos_left hcube hN
    -- Collapse the left-hand side to `π - π^3 / (96 * 4^n)`.
    have h4n : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hid : 2 ^ (n + 2) *
        (Real.pi / 2 ^ (n + 2) - (Real.pi / 2 ^ (n + 2)) ^ 3 / 6)
        = Real.pi - Real.pi ^ 3 / (96 * 4 ^ n) := by
      rw [hpow, h4n]; field_simp; ring
    rw [hid] at key
    -- Same `π ≤ 4` factor V0 uses: `π^3 ≤ 64`.
    have h4npos : (0 : ℝ) < 4 ^ n := by positivity
    have hpi3 : Real.pi ^ 3 ≤ 64 := by
      have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3
      norm_num at h
      exact h
    have hbound : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (2 / 3) / 4 ^ n := by
      have h1 : Real.pi ^ 3 / (96 * 4 ^ n) ≤ 64 / (96 * 4 ^ n) := by gcongr
      have h2 : (64 : ℝ) / (96 * 4 ^ n) = (2 / 3) / 4 ^ n := by
        field_simp
        ring
      linarith
    simp only [kappa]
    linarith

end ProofRefinement.PolygonPi.Candidates.V1
