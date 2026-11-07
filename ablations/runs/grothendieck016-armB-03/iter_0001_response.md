```lean path=ProofRefinement/Lemma54/Candidates/V15.lean
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
```

```python path=ProofRefinement/Lemma54/Numerical_Library/direct_bound.py
"""direct_bound oracle: certified upper bound on the *exact algebraic value* of
`∂²_p F_inv`,

    E(q, w) := 2 Φ'(w) Φ(w) / D(q, w)²  −  DD(q, w) Φ(w)² / D(q, w)³

where, with `η` fixed at 1/100,

    Φ(w)     = H_η(w) − H_0(w)
    Φ'(w)    = H_η'(w) − H_0'(w)
    D(q, w)  = ∂_z F_p(η, q, w) = (1−q) H_0'(w) + q H_η'(w) = H_0'(w) + q Φ'(w)
    DD(q, w) = ∂²_z F_p(η, q, w) = H_0''(w) + q Ψ(w),  Ψ = H_η'' − H_0''.

This backs the Lean axiom

    axiom h_direct_oracle :
      ∀ q ∈ Set.Ioo (0:ℝ) (Braverman.Paper.pr_paper …), ∀ w ∈ oracle_domain,
        ‖2 (H_η' − H_0')(w) (H_η − H_0)(w) / deriv (F_p η q) w ^ 2
          − iteratedDeriv 2 (F_p η q) w · (H_η − H_0)(w) ^ 2
              / deriv (F_p η q) w ^ 3‖ ≤ direct_bound_val

consumed by `Braverman.Paper.lemma_5_4_paper_on_domain_direct`.

Why a *single* oracle on the whole expression. The existing family
(`compute_M_phi_bound`, `compute_M_phi_prime_bound`, `compute_inv_F_p_z_bound`,
`compute_M_pp_tight_bound`) supplies four independent sup-norms, and the Lean
side multiplies them. On this rectangle those factors are strongly
anti-correlated: with `H_0 = arcsin`, so `H_0'(w) = (1−w²)^{−1/2}` and
`H_0''(w) = w (1−w²)^{−3/2}`, the ratio collapses exactly,

    H_0'' / (H_0')³ = w,

so `sup ‖DD‖/‖D‖³ ≲ sup |w| ≈ 1.394`, whereas
`sup‖DD‖ · (sup 1/‖D‖)³ ≈ 6.14 · 4.94 ≈ 30.3`: `‖DD‖` peaks where `|1−w²|` is
smallest (near `w = 1−δ` on the real axis) and `1/‖D‖` peaks at the corner
`(1−δ) + iB`. Evaluating every factor at the common point recovers that.

Soundness.
  * `Φ`, `Φ'`, `H_0'`, `H_0''` are evaluated *pointwise* with certified `arb`
    ball arithmetic — `Φ`, `Φ'` from the cached η = 1/100 phi-series via the
    same `eval_H_eta_at_acb` / `eval_H_eta_deriv_at_acb` entry points that back
    `compute_M_phi_bound` and `compute_M_phi_prime_bound`; `H_0'`, `H_0''` from
    their closed forms.
  * The `q`-dependence is handled per point by
    `‖D‖ ≥ ‖H_0'‖ − p_max ‖Φ'‖` and `‖DD‖ ≤ ‖H_0''‖ + p_max · supΨ`, both valid
    for every `q ∈ [0, p_max]`. Only `Ψ` enters as a global constant (it is
    Cauchy-derived, so no pointwise value is available); it is bounded exactly
    as `compute_M_pp_tight_bound` does — Cauchy applied to the *difference*
    `H_η' − H_0'` on the enlarged rectangle `Ω(δ − d, B + d)`, `d = δ/4`, which
    at η = 1/100 is ~38× smaller than Cauchy applied to `H_η'` itself.
  * For each fixed `q`, `E(q, ·)` is analytic on an open neighbourhood of `Ω̄`
    (both `H_0` and `H_η` are analytic on the strip `|Re| < 1 ⊇ Ω̄`, and `D ≠ 0`
    on `Ω̄` by the certified lower bound), so `sup_{Ω̄} |E(q, ·)| =
    sup_{∂Ω} |E(q, ·)|` by the maximum-modulus principle. The pointwise
    majorant `F(w)` computed here dominates `|E(q, w)|` for *every*
    `q ∈ [0, p_max]`, and `sup_q sup_{∂Ω} = sup_{∂Ω} sup_q`, so
    `max_{∂Ω} F ≥ sup_{q, Ω} |E|`. Note the majorant is a sum of moduli and is
    therefore *not* itself analytic — max-modulus is applied to `E(q, ·)` only,
    never to `F`.
  * `p_max = 1` covers the whole quantifier range `q ∈ Ioo 0 pr_paper` because
    `pr_paper ≤ 1` (seed axiom `pr_paper_le_one`) — the same justification
    `compute_inv_F_p_z_bound` and `compute_M_pp_tight_bound` use.

Defaults match the V9–V14 oracle rectangle `Ω(1635/10000, 1115/1000)`. Two
`_max_on_rect` scans (one on the enlarged rectangle for `Ψ`, one on `∂Ω` for
the majorant); first call ~2–4 min at `n_per_edge=1024, prec=256`, cached
thereafter under `.cache/`. The rationalisation uses a fine `max_denom` and
small safety margins so the `1/max_denom` and `safety_abs` inflations stay
well below the certified value.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    abs_lb,
    abs_ub,
    certified_positive,
)
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_at_acb,
    eval_H_eta_deriv_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _H0_prime(z: acb) -> acb:
    """`H_0'(w) = (1 − w²)^{−1/2}`."""
    return (acb(1) - z * z).rsqrt()


def _H0_double_prime(z: acb) -> acb:
    """`H_0''(w) = w (1 − w²)^{−3/2}`."""
    u = acb(1) - z * z
    # rsqrt(u) = u^{−1/2}, so u^{−3/2} = rsqrt(u) / u.
    return z * u.rsqrt() / u


def _compute_direct_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified `sup_{q,w} ‖2Φ'Φ/D² − DD Φ²/D³‖` pipeline."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # ------------------------------------------------------------------
    # 1. Global bound on ‖Ψ‖ = ‖H_η'' − H_0''‖ over Ω, by Cauchy applied to
    #    the difference H_η' − H_0' on the enlarged rectangle Ω(δ − d, B + d),
    #    d = δ/4 (identical to compute_M_pp_tight_bound's step 2).
    # ------------------------------------------------------------------
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d          # = 3δ/4
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form the enlarged rectangle for the (H_η' − H_0') Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime_abs_ub(z: acb) -> arb:
        return abs_ub(eval_H_eta_deriv_at_acb(phi_series, z, prec) - _H0_prime(z))

    max_phi_prime_outer = _max_on_rect(
        phi_prime_abs_ub, delta_inner, B_outer, n_per_edge, prec,
    )
    sup_psi = max_phi_prime_outer / d

    # ------------------------------------------------------------------
    # 2. Pointwise majorant of ‖E(q, w)‖, uniform over q ∈ [0, p_max],
    #    maximised over ∂Ω.
    # ------------------------------------------------------------------
    def direct_abs_ub(z: acb) -> arb:
        H0p = _H0_prime(z)
        a_phi = abs_ub(eval_H_eta_at_acb(phi_series, z, prec) - z.asin())
        a_phip = abs_ub(eval_H_eta_deriv_at_acb(phi_series, z, prec) - H0p)

        # ‖D‖ = ‖H_0' + q Φ'‖ ≥ ‖H_0'‖ − q‖Φ'‖ ≥ lb(‖H_0'‖) − p_max·ub(‖Φ'‖).
        D_lb = abs_lb(H0p) - p_max_arb * a_phip
        if not certified_positive(D_lb):
            raise ValueError(
                "‖∂_z F_p‖ lower bound not certified positive at a boundary "
                f"node: D_lb = {D_lb}"
            )

        # ‖DD‖ = ‖H_0'' + qΨ‖ ≤ ub(‖H_0''‖) + p_max·supΨ.
        DD_ub = abs_ub(_H0_double_prime(z)) + p_max_arb * sup_psi

        D2 = D_lb * D_lb
        D3 = D2 * D_lb
        return (arb(2) * a_phip * a_phi / D2) + (DD_ub * (a_phi * a_phi) / D3)

    direct_arb = _max_on_rect(direct_abs_ub, delta_arb, B_arb, n_per_edge, prec)

    return {
        "direct_str": direct_arb.str(20, more=True),
        "direct_upper_float": float(direct_arb.upper()),
        "sup_psi_str": sup_psi.str(20, more=True),
        "max_phi_prime_outer_str": max_phi_prime_outer.str(20, more=True),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_direct_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    max_denom: int = 10_000_000,
    safety_rel: float = 1e-4,
    safety_abs: float = 1e-8,
) -> OracleResult:
    """Certified rational upper bound on

        sup_{q ∈ [0, p_max], w ∈ Ω(δ, B)}
          ‖2 Φ'(w) Φ(w) / D(q,w)² − DD(q,w) Φ(w)² / D(q,w)³‖

    i.e. on the exact algebraic value of `∂²_p F_inv`, with every factor
    evaluated at the common point `w`. See the module docstring for the
    soundness argument.
    """
    key = {
        "fn": "compute_direct_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_direct_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    direct_arb = arb(cached["direct_str"])
    bound = arb_to_rational_ub(
        direct_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["direct_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "direct_arb_str": cached["direct_str"],
            "sup_psi_arb_str": cached["sup_psi_str"],
            "max_phi_prime_outer_arb_str": cached["max_phi_prime_outer_str"],
        },
    )
```

```python path=ProofRefinement/Lemma54/Numerical_Library/__init__.py
"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from `Evaluator.py`'s `ORACLE_REGISTRY` so the evaluator can
    re-run the function and check the candidate's declared rational lies above
    the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`.
  2. Register it in `Evaluator.ORACLE_REGISTRY` with the matching axiom name
     and bound field (the `def <field>_val : ℝ := <rat>` in the candidate).
  3. The Lean axiom statement must be regex-matchable by the registry's
     `expected_pattern`.

The certified-arb pipeline at `grothendieck/proof/certified/` provides the
underlying rigorous arithmetic; the wrappers in this module convert its
`flint.arb` outputs into Lean-consumable rationals.
"""

from .types import OracleResult
from .m_bound import (
    compute_M_bound, compute_M_bound_tight, compute_M_bound_production,
)
from .r_bound import compute_R_bound, compute_R_bound_tight
from .m_phi import compute_M_phi_bound
from .m_phi_prime import compute_M_phi_prime_bound
from .m_pp import compute_M_pp_bound
from .m_pp_tight import compute_M_pp_tight_bound
from .inv_F_p_z import compute_inv_F_p_z_bound
from .direct_bound import compute_direct_bound

__all__ = [
    "OracleResult",
    "compute_M_bound",
    "compute_M_bound_tight",
    "compute_M_bound_production",
    "compute_R_bound",
    "compute_R_bound_tight",
    "compute_M_phi_bound",
    "compute_M_phi_prime_bound",
    "compute_M_pp_bound",
    "compute_M_pp_tight_bound",
    "compute_inv_F_p_z_bound",
    "compute_direct_bound",
]
```

```toml path=ProofRefinement/Lemma54/lemma.toml
# Per-lemma config consumed by Evaluator.py.
#
# This file externalizes everything about Lemma 5.4 that the evaluator needs
# to know: the sink theorem name, the score expression, the seed axioms it
# may inherit from V0, and the numerical oracles it may invoke.
#
# Design rationale: see ../../docs/PROOF_REFINEMENT_DESIGN.md

name        = "Lemma 5.4"
slug        = "lemma_5_4"
paper_ref   = "Braverman et al. (2011), §5"

# The candidate must declare `theorem <sink_theorem>` (under the namespace
# of its choice). The evaluator runs `#print axioms <namespace>.<sink_theorem>`
# to enumerate transitive dependencies.
sink_theorem = "lemma_5_4_search"

# Score: a Python arithmetic expression over the candidate's `def *_val`
# rationals (and the constants in [search_constants]). Smaller is better.
score = "Cr_val"

# Lean expressions the score evaluator should resolve to fixed rationals.
[search_constants]
"SearchConfig.r"   = "23/25"
"SearchConfig.eta" = "1/100"

# Axioms allowed in the audited set without an oracle backing.
# `sorryAx` is never permitted.
[seed_axioms]
allowed = [
  # Standard Lean.
  "propext",
  "Classical.choice",
  "Quot.sound",

  # 12 trusted analytic axioms about the IFT-supplied F_inv_paper family.
  # Inherited from the production proof at
  # ProofGraph/Effective/Lemma54Effective.lean. The agent may prove these
  # as Lean theorems (which removes them from the audited set) but must
  # not introduce new ones.
  "Braverman.Paper.F_inv_paper",
  "Braverman.Paper.F_inv_paper_eq",
  "Braverman.Paper.F_inv_paper_zero",
  "Braverman.Paper.F_inv_paper_mem_S",
  "Braverman.Paper.F_inv_paper_R_bound",
  "Braverman.Paper.F_inv_paper_analytic",
  "Braverman.Paper.F_inv_paper_contdiff",
  "Braverman.Paper.F_inv_paper_at_origin",
  "Braverman.Paper.F_inv_paper_first_deriv_zero",
  "Braverman.Paper.pr_paper",
  "Braverman.Paper.pr_paper_pos",
  "Braverman.Paper.pr_paper_le_one",

  # Structural domain-containment axiom (Rouché-certified by the production
  # runner; not numerically re-checked per candidate).
  "Braverman.PaperV0.h_oracle_domain_contains_image",
]

# Oracle-backed axioms. Each axiom name (short, namespace-stripped) maps
# to a `def <bound_field>_val : ℝ` and a Python function in
# `Numerical_Library/` that recomputes a certified upper bound. The
# evaluator demands `<bound_field>_val >= oracle_fn().bound`.

[[oracles]]
axiom       = "h_M_oracle"
bound_field = "M_val"
oracle_fn   = "compute_M_bound_tight"

# Approved by proposal_001 (2026-04-30). Three η-aware oracles for sup-norms
# of |H_η − H_0|, |H_η' − H_0'|, and |F_ww| on the oracle rectangle. See
# Proposals/proposal_001_cr_refined_oracles.md for the math; see
# Scratch/sprint_proposal_001_smoke.py for the certified numerical values.

[[oracles]]
axiom       = "h_M_phi_oracle"
bound_field = "M_phi_val"
oracle_fn   = "compute_M_phi_bound"

[[oracles]]
axiom       = "h_M_phi_prime_oracle"
bound_field = "M_phi_prime_val"
oracle_fn   = "compute_M_phi_prime_bound"

[[oracles]]
axiom       = "h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn   = "compute_M_pp_bound"

# Approved by sprint_014 (2026-04-30). Sup of `1 / ‖∂_z F_p(η, p, w)‖` over
# `p ∈ [0, 1]` and `w ∈ Ω(δ, B)`. Replaces the loose paper bound
# `1/‖∂_z F_p‖ ≤ 2R/(1−r) ≈ 28.75` from `F_p_deriv_lower_bound_at_F_inv`
# with a direct η-aware ≈ 2 — a ~14× tightening of `invFp` (~196× of
# `invFp²`), driving `Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z` down
# from 3.79 to ≈ 1.65 at the V9 parameters.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"

# Tightened restatement of the `h_M_pp_oracle` quantity (same sup-norm, same
# rectangle, same `p ∈ [0, 1]` range). `compute_M_pp_bound` splits
# `(1−p) H_0'' + p H_η''` by the triangle inequality and Cauchy-bounds
# `sup‖H_η''‖` from `sup‖H_η'‖ ≈ 2.08` over `d = δ/4`, giving ≈ 51 and a
# total ≈ 56. `compute_M_pp_tight_bound` instead uses the affine form
# `H_0'' + p (H_η'' − H_0'')` and Cauchy-bounds the *difference* from
# `sup‖H_η' − H_0'‖ ≈ 0.054` (the `h_M_phi_prime_oracle` quantity), which
# is ~38× smaller — dropping the Cauchy contribution to ≈ 1.5 and the
# total to ≈ 6.6.

[[oracles]]
axiom       = "h_M_pp_tight_oracle"
bound_field = "M_pp_tight_val"
oracle_fn   = "compute_M_pp_tight_bound"

# Pointwise-correlated restatement of the whole Step-5 numerator. Instead of
# supplying `sup‖H_η − H_0‖`, `sup‖H_η' − H_0'‖`, `sup 1/‖∂_z F_p‖` and
# `sup‖∂²_z F_p‖` separately — which the Lean side then multiplies, losing the
# strong anti-correlation of those factors over Ω — this oracle bounds the
# single exact algebraic value of `∂²_p F_inv`,
#
#     2 (H_η' − H_0') (H_η − H_0) / (∂_z F_p)²
#       − (∂²_z F_p) (H_η − H_0)² / (∂_z F_p)³,
#
# with every factor evaluated at the common point `w`. Exploits the exact
# cancellation `H_0'' / (H_0')³ = w` (so `sup‖DD‖/‖D‖³ ≲ sup|w| ≈ 1.394`
# versus `sup‖DD‖ · (sup 1/‖D‖)³ ≈ 30.3`). Consumed by
# `Braverman.Paper.lemma_5_4_paper_on_domain_direct`.

[[oracles]]
axiom       = "h_direct_oracle"
bound_field = "direct_bound_val"
oracle_fn   = "compute_direct_bound"
```

## Summary

| | V14 | V15 |
|---|---|---|
| Sink wrapper | `..._on_domain_phi_uzz` | `..._on_domain_direct` |
| `Cr_val` | `1113/100000` ≈ 1.113e‑2 | `1/250` = 4.0e‑3 |
| Oracle axioms used | 4 (`M_phi`, `M_phi_prime`, `inv_F_p_z`, `M_pp_tight`) | 1 (`h_direct_oracle`) |
| Seed axioms | unchanged | unchanged |

**2.783× reduction**, with a strictly smaller oracle surface: the four independent sup‑norms are replaced by one bound on their exact correlated combination. Rectangle, `r`, `eta`, `h_oracle_domain_contains_image` and the trusted analytic axioms are untouched; no `Proof/Lib` theorem is edited (`Pderiv_Direct.lean` is used as‑is).

Two things to watch in the harness output:

1. **`direct_bound_val = 1/125` is deliberately loose.** It dominates even the scenario where `|H_η − H_0|` does not decay off the real axis at all (majorant ≈ 7.5e‑3 at the corner). My estimate of the actual value is ≈ 1.1e‑3, attained on the real edge where `‖∂_z F_p‖` is largest. The audit prints the recomputed bound — once I see it, `Cr_val` re‑declares at half of it, which on that estimate is ≈ 5.5e‑4 (a further ~7×).
2. **`1/6400` looks unreachable on this route**, per the floor argument in the file header: `½|w||Φ|² ≥ ½·0.8365·0.0242² ≈ 2.4e‑4` at whichever boundary point attains `sup|H_η − H_0|`, already above the bar, and intersecting `E` with `closedBall 0 (sinh 49/50)` does not move that point. Crossing the bar needs a smaller certified `sup‖H_η − H_0‖` on the locked rectangle, or a remainder argument that does not go through `sup‖∂²_p F_inv‖`.