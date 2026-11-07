import ProofRefinement.PolygonPi.Proof.Main

/-!
# V5 — derived Taylor bounds around `sin`

Restated verbatim from V4's `Taylor.lean` (candidates never import each other).

* `sin_gt_sub_cube_div_six`: `x - x^3/6 < sin x` for `x > 0`. Proved via
  `strictMonoOn_of_deriv_pos` on `f t = sin t - t + t^3/6`, whose derivative
  `cos t - 1 + t^2/2` is positive for `t > 0` by
  `Real.one_sub_sq_div_two_lt_cos`.
* `sin_lt_taylor5`: `sin x < x - x^3/6 + x^5/120` for `x > 0`. Nested
  monotonicity: inner `h t = 1 - t^2/2 + t^4/24 - cos t` has derivative
  `sin t - (t - t^3/6)`, positive by `sin_gt_sub_cube_div_six`; outer
  `g t = t - t^3/6 + t^5/120 - sin t` has derivative `h t`, positive for
  `t > 0`.

No `axiom`, `opaque`, `native_decide`, or `sorry`.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open ProofRefinement.PolygonPi PolygonCore

/-- The tight fourth-order Taylor lower bound: `x - x^3/6 < sin x` for all
`x > 0`.

Restated from V1/V2/V3/V4 verbatim; candidates never import each other. -/
lemma sin_gt_sub_cube_div_six {x : ℝ} (hx : 0 < x) :
    x - x ^ 3 / 6 < Real.sin x := by
  set f : ℝ → ℝ := fun t => Real.sin t - t + t ^ 3 / 6 with hf_def
  have hcont : ContinuousOn f (Set.Ici (0 : ℝ)) := by
    change ContinuousOn (fun t => Real.sin t - t + t ^ 3 / 6) (Set.Ici (0 : ℝ))
    fun_prop
  have hderiv : ∀ t : ℝ, HasDerivAt f (Real.cos t - 1 + t ^ 2 / 2) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos t) t :=
      Real.hasDerivAt_sin t
    have h2 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) ((3 : ℕ) * t ^ (3 - 1)) t :=
      hasDerivAt_pow 3 t
    have h3' : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (3 * t ^ 2 / 6) t := by
      have := h3.div_const (6 : ℝ)
      simpa using this
    have hcombined :
        HasDerivAt f ((Real.cos t - 1) + 3 * t ^ 2 / 6) t := by
      exact (h1.sub h2).add h3'
    have hrw : (Real.cos t - 1) + 3 * t ^ 2 / 6 = Real.cos t - 1 + t ^ 2 / 2 := by
      ring
    rw [hrw] at hcombined
    exact hcombined
  have hderiv_pos : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv f t := by
    intro t ht
    rw [interior_Ici] at ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hcos := Real.one_sub_sq_div_two_lt_cos htne
    have hdt : deriv f t = Real.cos t - 1 + t ^ 2 / 2 := (hderiv t).deriv
    rw [hdt]
    linarith
  have hmono : StrictMonoOn f (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv_pos
  have hzero : f 0 = 0 := by simp [f]
  have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hxmem : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hx.le
  have hfx : f 0 < f x := hmono h0mem hxmem hx
  rw [hzero] at hfx
  have : (0 : ℝ) < Real.sin x - x + x ^ 3 / 6 := hfx
  linarith

/-- The fifth-order Taylor upper bound: `sin x < x - x^3/6 + x^5/120` for
all `x > 0`.

Restated from V2/V3/V4 verbatim. -/
lemma sin_lt_taylor5 {x : ℝ} (hx : 0 < x) :
    Real.sin x < x - x ^ 3 / 6 + x ^ 5 / 120 := by
  set h : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t with hh_def
  have hcont_h : ContinuousOn h (Set.Ici (0 : ℝ)) := by
    change ContinuousOn (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (Set.Ici (0 : ℝ))
    fun_prop
  have hderiv_h : ∀ t : ℝ,
      HasDerivAt h ((0 - 2 * t / 2 + 4 * t ^ 3 / 24) - (-Real.sin t)) t := by
    intro t
    have hC : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℕ) * t ^ (2 - 1)) t :=
      hasDerivAt_pow 2 t
    have h2' : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (2 * t / 2) t := by
      have := h2.div_const (2 : ℝ)
      simpa using this
    have h4 : HasDerivAt (fun s : ℝ => s ^ 4) ((4 : ℕ) * t ^ (4 - 1)) t :=
      hasDerivAt_pow 4 t
    have h4' : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (4 * t ^ 3 / 24) t := by
      have := h4.div_const (24 : ℝ)
      simpa using this
    have hcos : HasDerivAt (fun s : ℝ => Real.cos s) (-Real.sin t) t :=
      Real.hasDerivAt_cos t
    exact ((hC.sub h2').add h4').sub hcos
  have hderiv_h_pos : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv h t := by
    intro t ht
    rw [interior_Ici] at ht
    have hsin := sin_gt_sub_cube_div_six ht
    have hdt : deriv h t = (0 - 2 * t / 2 + 4 * t ^ 3 / 24) - (-Real.sin t) :=
      (hderiv_h t).deriv
    have hdt' : deriv h t = Real.sin t - (t - t ^ 3 / 6) := by
      rw [hdt]; ring
    rw [hdt']
    linarith
  have hmono_h : StrictMonoOn h (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont_h hderiv_h_pos
  have hzero_h : h 0 = 0 := by
    change 1 - (0 : ℝ) ^ 2 / 2 + (0 : ℝ) ^ 4 / 24 - Real.cos 0 = 0
    rw [Real.cos_zero]; norm_num
  have h_pos_on_Ioi : ∀ t : ℝ, 0 < t → 0 < h t := by
    intro t ht_pos
    have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
    have htmem : t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ht_pos.le
    have hht : h 0 < h t := hmono_h h0mem htmem ht_pos
    rw [hzero_h] at hht
    exact hht
  set g : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t with hg_def
  have hcont_g : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    change ContinuousOn (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (Set.Ici (0 : ℝ))
    fun_prop
  have hderiv_g : ∀ t : ℝ,
      HasDerivAt g ((1 - 3 * t ^ 2 / 6 + 5 * t ^ 4 / 120) - Real.cos t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) ((3 : ℕ) * t ^ (3 - 1)) t :=
      hasDerivAt_pow 3 t
    have h3' : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (3 * t ^ 2 / 6) t := by
      have := h3.div_const (6 : ℝ)
      simpa using this
    have h5 : HasDerivAt (fun s : ℝ => s ^ 5) ((5 : ℕ) * t ^ (5 - 1)) t :=
      hasDerivAt_pow 5 t
    have h5' : HasDerivAt (fun s : ℝ => s ^ 5 / 120) (5 * t ^ 4 / 120) t := by
      have := h5.div_const (120 : ℝ)
      simpa using this
    have hsin : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos t) t :=
      Real.hasDerivAt_sin t
    exact ((h1.sub h3').add h5').sub hsin
  have hderiv_g_pos : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv g t := by
    intro t ht
    rw [interior_Ici] at ht
    have hht := h_pos_on_Ioi t ht
    have hht' : (0 : ℝ) < 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := hht
    have hdt : deriv g t = (1 - 3 * t ^ 2 / 6 + 5 * t ^ 4 / 120) - Real.cos t :=
      (hderiv_g t).deriv
    have hdt' : deriv g t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
      rw [hdt]; ring
    rw [hdt']
    exact hht'
  have hmono_g : StrictMonoOn g (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont_g hderiv_g_pos
  have hzero_g : g 0 = 0 := by
    change (0 : ℝ) - (0 : ℝ) ^ 3 / 6 + (0 : ℝ) ^ 5 / 120 - Real.sin 0 = 0
    rw [Real.sin_zero]; norm_num
  have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hxmem : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hx.le
  have hgx : g 0 < g x := hmono_g h0mem hxmem hx
  rw [hzero_g] at hgx
  have hgx' : (0 : ℝ) < x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := hgx
  linarith

end ProofRefinement.PolygonPi.Candidates.V5
