/-
  Candidates/V15.lean — stop splitting `∂²_p F_inv` into independently-supped
  factors; hand the exact algebraic expression to a single oracle so all four
  factors are evaluated at the common point `w = F_inv p z`.

  -- @parent Candidates/V14.lean

  V11–V14 route through `Cr_phi_uzz`, which ends by splitting

      ‖u''‖ ≤ 2‖Φ'‖‖Φ‖·(1/‖D‖)² + ‖u_zz‖·‖Φ‖²,   ‖u_zz‖ ≤ ‖DD‖·(1/‖D‖)³,

  bounding each factor by its own sup-norm oracle. At V14's literals the second
  chunk is `½·6.1373·4.9434·5.9536e-4 ≈ 9.03e-3` — 81% of the score — and its
  coefficient `M_pp·inv_F_p_z³ ≈ 30.3` is a *correlation* loss, not a precision
  loss: over `Ω(1635/10000, 1115/1000)`, with `H_0 = arcsin` so
  `H_0' = (1−w²)^{−1/2}`, `H_0'' = w(1−w²)^{−3/2}`,

      sup‖∂²_z F_p‖  ≈ 5.08  at w ≈ 0.8365      (there 1/‖∂_z F_p‖ ≈ 0.55, its min)
      sup 1/‖∂_z F_p‖ ≈ 1.56  at 0.8365+1.115i  (there ‖∂²_z F_p‖ ≈ 0.37)

  and at p = 0 the closed forms cancel exactly: `DD/D³ = w`, so the correlated
  ratio obeys `‖DD‖/‖D‖³ ≲ |w| ≤ 1.394` — ~22× below the product of sups.
  V14's header flagged this and deferred it; V15 collects it.

  Mechanism. `Proof/Lib/Lemma54_Paper_Pderiv_Direct.lean` (present in the
  workspace, unused by every candidate so far) does not split. From form A
  `2Φ'u' + DD·u'² + D·u'' = 0` and identity 75 `u' = −Φ/D` it derives, with no
  inequality applied,

      u'' = 2Φ'Φ/D² − DD·Φ²/D³,

  and `lemma_5_4_paper_on_domain_direct` consumes a single oracle bound on the
  norm of that one expression (`≤ 2·Cr`, `Cr` a bare parameter; the Lagrange
  `1/2!` is absorbed exactly as in the `Cr_phi*` family). So V15 adds exactly
  one oracle and no new proof infrastructure.

  The oracle. `Numerical_Library/direct_bound.py` certifies

      sup_{q ∈ [0,1], w ∈ Ω(δ,B)}
        ‖2Φ'(w)Φ(w)/D(q,w)² − DD(q,w)Φ(w)²/D(q,w)³‖ ≤ direct_bound_val

  evaluating `Φ = H_η − H_0` and `Φ'` pointwise from the cached η = 1/100
  phi-series (the same `eval_H_eta_at_acb` / `eval_H_eta_deriv_at_acb` calls
  behind `compute_M_phi_bound` / `compute_M_phi_prime_bound`), `H_0'`, `H_0''`
  pointwise in closed form, and the `q`-dependence per point via
  `‖D‖ ≥ ‖H_0'‖ − q‖Φ'‖` and `‖DD‖ ≤ ‖H_0''‖ + q·sup‖H_η''−H_0''‖` (the latter
  by the same Cauchy-on-the-difference route as `compute_M_pp_tight_bound`).
  For each fixed `q` the expression is analytic on a neighbourhood of `Ω̄`
  (`D ≠ 0` there), so its sup on `Ω̄` is attained on `∂Ω`; and
  `sup_q sup_{∂Ω} = sup_{∂Ω} sup_q`. `p_max = 1` covers the full quantifier
  range since `pr_paper ≤ 1` (seed axiom `pr_paper_le_one`) — the same
  justification `compute_inv_F_p_z_bound` and `compute_M_pp_tight_bound` use.

  Score. `direct_bound_val := 1/125 = 8e-3`, `Cr_val := 1/250 = 4e-3`, so the
  closing step `direct_bound_val ≤ 2·Cr_val` is an equality. Hand analysis puts
  the oracle's output near `1.1e-3` (its max sits at the real edge, where `‖D‖`
  is *largest*), with an absolute worst case `≈ 7.5e-3` reached only if `|Φ|`
  did not decay off the real axis at all; `1/125` dominates even that. vs V14's
  `1113/100000`: a 2.783× reduction. Once the audit prints the recomputed
  bound, `Cr_val` can be re-declared at half of it.

  Trust surface: strictly smaller than V14's. Same locked constants
  (`eta = 1/100`, `r = 23/25`), same rectangle `Ω(1635/10000, 1115/1000)`, same
  seed `h_oracle_domain_contains_image`, same 9 trusted analytic axioms. The
  four η-aware oracles V14 consumed (`M_phi`, `M_phi_prime`, `inv_F_p_z`,
  `M_pp_tight`) are replaced by the one `h_direct_oracle` whose statement is
  their exact correlated combination.

  Known limitation. `Cr_val ≤ 1/6400` is out of reach for this whole family,
  and the obstruction is a floor rather than slack. `Cr` must dominate
  `½·sup|∂²_p F_inv|`, and the single term `½|DD/D³|·|Φ|² = ½|w||Φ|²` already
  forces, at whichever point of `∂Ω` attains `sup|Φ| ≈ 0.0242` (certified by
  `compute_M_phi_bound`; every point of `∂Ω` has `|w| ≥ 1−δ = 0.8365`),

      Cr ≥ ½·0.8365·0.0242² ≈ 2.4e-4 > 1/6400 = 1.5625e-4.

  Restricting `E` to `Ω ∩ closedBall 0 (sinh (49/50))` — derivable from the
  existing `F_inv_paper_R_bound` seed, no new axiom — excises the corner but
  not that point, so the floor is unmoved. Beating `1/6400` needs either a
  smaller certified `sup‖H_η − H_0‖` on this locked rectangle or a remainder
  argument that does not route through `sup‖∂²_p F_inv‖`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Pderiv_Direct
import LeanProof.Defs.Strip

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: The oracle rectangle (unchanged from V9–V14) -/

/-- Real-width parameter for the Rouché-certified oracle rectangle. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the Rouché-certified oracle rectangle. -/
def B_val : ℝ := 1115 / 1000

theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-- The Step-1/Rouché-certified rectangle `Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 2: Numerical witness and score -/

/-- Certified sup, over `q ∈ [0, 1]` and `w ∈ Ω(δ_val, B_val)`, of the exact
algebraic value of `∂²_p F_inv`,

    ‖2Φ'Φ/D² − DD·Φ²/D³‖,   Φ = H_η − H_0, D = ∂_z F_p, DD = ∂²_z F_p.

`1/125 = 8·10⁻³`, dominating the value `Numerical_Library.compute_direct_bound`
recomputes at its module-level defaults. -/
def direct_bound_val : ℝ := 1 / 125

theorem direct_bound_val_pos : 0 < direct_bound_val := by
  unfold direct_bound_val; norm_num
theorem direct_bound_val_nn : 0 ≤ direct_bound_val := le_of_lt direct_bound_val_pos

/-- `Cr_val := 1/250 = 4·10⁻³ = direct_bound_val / 2`. The Lagrange `1/2!`
factor in Step 6 turns the `≤ 2·Cr` second-derivative bound into `Cr·p²`, so
the closing step `direct_bound_val ≤ 2·Cr_val` is an equality. -/
def Cr_val : ℝ := 1 / 250

theorem Cr_val_pos : 0 < Cr_val := by unfold Cr_val; norm_num
theorem Cr_val_nn : 0 ≤ Cr_val := le_of_lt Cr_val_pos

/-! ## Section 3: Axioms (one seed + one oracle) -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Seed axiom, carried
over byte-identical from V9–V14. -/
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

/-- **The pointwise-correlated oracle.** Sup-norm bound on the exact algebraic
value of `∂²_p F_inv` over `q ∈ Ioo 0 pr_paper` and `w ∈ Ω(δ_val, B_val)`.
Runner-witnessed by `Numerical_Library.compute_direct_bound`, which evaluates
`Φ`, `Φ'`, `H_0'`, `H_0''` pointwise on `∂Ω` (so the four factors are
correlated) and covers the `q`-range with `p_max = 1`, justified by the seed
axiom `pr_paper_le_one`. -/
axiom h_direct_oracle :
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
          ≤ direct_bound_val

/-! ## Section 4: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V14; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_direct`, which
consumes the single correlated oracle in place of V14's four independent
sup-norm oracles. -/
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
  -- Lift the oracle's RHS to the `2 * Cr` shape the wrapper expects. The
  -- inequality is an equality: `1/125 = 2 * (1/250)`.
  have h_two_Cr :
      ∀ q ∈ Set.Ioo (0 : ℝ)
          (Braverman.Paper.pr_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
        ∀ w ∈ oracle_domain,
          ‖2 * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                  - deriv Braverman.H0 w)
                * (Braverman.H_eta Braverman.SearchConfig.eta w
                    - Braverman.H0 w)
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 2
            - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta q) w
                * (Braverman.H_eta Braverman.SearchConfig.eta w
                    - Braverman.H0 w) ^ 2
                / deriv (Braverman.F_p Braverman.SearchConfig.eta q) w ^ 3‖
            ≤ 2 * Cr_val := by
    intro q hq w hw
    refine le_trans (h_direct_oracle q hq w hw) ?_
    unfold direct_bound_val Cr_val
    norm_num
  obtain ⟨pr, hpr_pos, h_main⟩ :=
    Braverman.Paper.lemma_5_4_paper_on_domain_direct
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      Cr_val Cr_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_two_Cr
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  exact ⟨F_inv, hF_eq, hF_S, hF_bound⟩

end Braverman.PaperV0
