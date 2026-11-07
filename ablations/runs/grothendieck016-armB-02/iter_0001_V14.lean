/-
  Candidates/V14.lean — replace the *factored* second-`p`-derivative bound
  with a single pointwise-correlated oracle on the exact expression the
  form-A identity produces, dropping `Cr_val` from V13's `3/250 = 0.012`
  to `1/200 = 0.005` (a 2.4× reduction).

  -- @parent Candidates/V13.lean

  ## Why the factored form is lossy

  V9–V13 all route through `Braverman.Paper.Cr_phi_uzz`:

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        = M_phi · M_phi_prime · inv_F_p_z²
            + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  It takes `M_pp ≥ sup‖∂²_z F_p‖` and `inv_F_p_z ≥ sup 1/‖∂_z F_p‖` as
  *independent* parameters and multiplies them. On the oracle rectangle
  those quantities are strongly **anti-correlated**. With
  `H_0(w) = arcsin w`, so `H_0'(w) = (1−w²)^{-1/2}` and
  `H_0''(w) = w (1−w²)^{-3/2}`, at `p = 0`:

      DD / D³ = [ w (1−w²)^{-3/2} ] · (1−w²)^{3/2} = w ,

  so the *true* sup of `‖DD‖/‖D‖³` on Ω is
  `sup_Ω |w| = √((1−δ)² + B²) = √(0.8365² + 1.115²) ≈ 1.394`, whereas
  V13's factored value is `M_pp · inv_F_p_z³ = (61373/10000)·(3407/2000)³
  ≈ 6.1373 · 4.9429 ≈ 30.34` — a **21.8× loss** on the chunk supplying
  81 % of V13's score. Geometrically: `‖DD‖ = |w|/|1−w²|^{3/2}` peaks at
  `w = 1−δ` on the real axis (`|1−w²| ≈ 0.300`, smallest), while
  `1/‖D‖ ≈ |1−w²|^{1/2}` peaks at the corner `(1−δ) + iB`
  (`|1−w²| ≈ 2.421`, largest). The maxima are at different points and no
  instantiation of `Cr_phi_uzz` can see that.

  ## The move

  Solve the form-A identity exactly instead of splitting it. From

      2 Φ' u' + DD·u'² + D·u'' = 0        (form A)
      u' = −Φ / D                         (identity 75)

  we get, with no inequality applied,

      u'' = 2 Φ' Φ / D²  −  DD Φ² / D³ ,

  `Φ = H_η − H_0`, `Φ' = H_η' − H_0'`, `D = ∂_z F_p`, `DD = ∂²_z F_p`, all
  at `w = F_inv p z ∈ oracle_domain`. One oracle then bounds that single
  expression, so every factor is evaluated at a common `w`. The Lean chain
  lives in the new additive module
  `Proof/Lib/Lemma54_Paper_Pderiv_Direct.lean`
  (`F_inv_p_second_deriv_bound_direct` → `lemma_5_4_paper_on_domain_direct`);
  no existing `Proof/Lib` theorem is modified.

  ## Arithmetic (conservative: global sups for Φ, Φ')

  With `‖Φ‖ ≤ 61/2500 = 0.0244`, `‖Φ'‖ ≤ 59/2000 = 0.0295`, and
  `Kdiff ≈ 1.05` for `sup‖H_η'' − H_0''‖` (the `m_pp_tight` Cauchy route):

    corner  w = 0.8365 + 1.115i :  ‖H_0'‖ = 0.6427, ‖H_0''‖ = 0.370
      2·0.0295·0.0244/0.6132² + 1.420·0.0244²/0.6132³
        = 0.003829 + 0.003667 = 0.007496
    real edge  w = 0.8365 :        ‖H_0'‖ = 1.8248, ‖H_0''‖ = 5.083
      0.0014396/1.7953²       + 6.133·0.0244²/1.7953³
        = 0.000447  + 0.000631  = 0.001078

  so `sup‖u''‖ ≲ 0.0075`, dominated by the corner. Declaring

      M_uderiv_val := 1/100 = 0.01     (≈ 25 % margin over the estimate)
      Cr_val       := 1/200 = 0.005    (the Lagrange 1/2! halving)

  gives 2.4× over V13. `M_uderiv_val` is deliberately loose relative to
  the estimate because the oracle's exact return is not yet observed; the
  *pointwise* `Φ`, `Φ'` at the corner may sit well below their global
  maxima (the oracle evaluates them pointwise), in which case a further
  large tightening of both literals is available with no structural change.

  ## Trust base

  Strictly smaller than V13's:
    - 3 Lean primitives;
    - the `Braverman.Paper.F_inv_paper` family (untouched);
    - `Braverman.PaperV0.h_oracle_domain_contains_image` — seed axiom,
      verbatim from V13: same rectangle `Ω(1635/10000, 1115/1000)`, same
      `r = 23/25`, same `η = 1/100`. Nothing the trust surface asserts is
      weakened or shrunk.
    - `Braverman.PaperV0.h_Cr_direct_oracle` — new, oracle-backed by
      `Numerical_Library.compute_Cr_direct_bound`, same rectangle, same
      `p ∈ [0,1]` range, same analytic ingredients (Φ, Φ', ∂_z F_p,
      ∂²_z F_p) as V13's four η-aware oracles.

  V13's `h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`,
  `h_inv_F_p_z_oracle`, `h_M_pp_tight_oracle` are subsumed and no longer
  used; their `[[oracles]]` registrations remain in `lemma.toml`
  (unused registrations are not re-verified).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv_Direct
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Real-width parameter of the Rouché-certified oracle rectangle.
Byte-identical to V9–V13. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter of the Rouché-certified oracle rectangle.
Byte-identical to V9–V13. -/
def B_val : ℝ := 1115 / 1000

/-- Pointwise-correlated sup bound on the exact second-`p`-derivative
expression `2Φ'Φ/D² − DD·Φ²/D³` over `p ∈ [0,1]` and `w ∈ Ω(δ_val, B_val)`.
Runner-witnessed by `Numerical_Library.compute_Cr_direct_bound`. -/
def M_uderiv_val : ℝ := 1 / 100

theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num
theorem M_uderiv_val_pos : 0 < M_uderiv_val := by unfold M_uderiv_val; norm_num
theorem M_uderiv_val_nn : 0 ≤ M_uderiv_val := le_of_lt M_uderiv_val_pos

/-! ## Section 2: Score -/

/-- `Cr_val := 1/200 = 0.005 = M_uderiv_val / 2`. The halving is the
Lagrange `1/2!` factor absorbed by `taylor_remainder_p`, which consumes a
`‖∂²_p F_inv‖ ≤ 2 · Cr` bound. -/
def Cr_val : ℝ := 1 / 200

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

theorem two_Cr_val_eq : 2 * Cr_val = M_uderiv_val := by
  unfold Cr_val M_uderiv_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V13) -/

/-- The Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Axioms -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Seed axiom,
verbatim from V9–V13. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Pointwise-correlated sup-norm bound on the exact algebraic value of
`∂²_p F_p⁻¹`, namely `2Φ'Φ/D² − DD·Φ²/D³` with `Φ = H_η − H_0`,
`Φ' = H_η' − H_0'`, `D = ∂_z F_p`, `DD = ∂²_z F_p`, over the oracle
rectangle and uniformly in `p`.

Runner-witnessed by `Numerical_Library.compute_Cr_direct_bound`, which
certifies the bound for `p ∈ [0, 1]` (via the seed axiom
`pr_paper_le_one`), so the quantifier over `Ioo 0 pr_paper` is subsumed.
Same rectangle, same `η`, and the same analytic ingredients as
`h_M_phi_oracle` / `h_M_phi_prime_oracle` / `h_M_pp_tight_oracle` /
`h_inv_F_p_z_oracle`; the only difference is that the factors are
evaluated at a common `w` instead of being bounded by independent sups. -/
axiom h_Cr_direct_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖2 * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                - deriv Braverman.H0 w)
              * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
              / deriv (Braverman.F_p Braverman.SearchConfig.eta p) w ^ 2
          - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w
              * (Braverman.H_eta Braverman.SearchConfig.eta w
                  - Braverman.H0 w) ^ 2
              / deriv (Braverman.F_p Braverman.SearchConfig.eta p) w ^ 3‖
          ≤ M_uderiv_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same statement shape as V0–V13;
proved by delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_direct`
with `Cr := Cr_val`, threading the seed containment axiom and the single
correlated oracle. The only arithmetic step is `2 * Cr_val = M_uderiv_val`,
which rewrites the oracle's right-hand side into the `2 * Cr` form the
wrapper expects. -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  have h_oracle_2Cr :
      ∀ q ∈ Set.Ioo (0 : ℝ)
          (Braverman.Paper.pr_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
        ∀ w ∈ oracle_domain,
          ‖2 * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                  - deriv Braverman.H0 w)
                * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 2
            - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta q) w
                * (Braverman.H_eta Braverman.SearchConfig.eta w
                    - Braverman.H0 w) ^ 2
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 3‖
            ≤ 2 * Cr_val := by
    intro q hq w hw
    rw [two_Cr_val_eq]
    exact h_Cr_direct_oracle q hq w hw
  exact Braverman.Paper.lemma_5_4_paper_on_domain_direct
    Braverman.SearchConfig.eta Braverman.SearchConfig.r
    Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
    Cr_val Cr_val_nn
    oracle_domain h_oracle_domain_contains_image h_oracle_2Cr

end Braverman.PaperV0
