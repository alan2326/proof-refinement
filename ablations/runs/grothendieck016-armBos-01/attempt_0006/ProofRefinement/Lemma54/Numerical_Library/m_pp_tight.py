"""Tighter M_pp oracle: certified upper bound on

    M_pp = sup_{p ∈ [0, 1], w ∈ Ω(δ, B)} ‖(1−p) H_0''(w) + p · H_η''(w)‖
         = sup ‖iteratedDeriv 2 (F_p η p) w‖.

Why a second module rather than a retune of `m_pp.py`
-----------------------------------------------------
`m_pp.py` splits the triangle inequality as

    ‖DD‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

and bounds the second summand by a Cauchy estimate applied to `H_η'`
*itself* on the enlarged rectangle Ω(δ−d, B+d) with d = δ/4:

    sup_Ω ‖H_η''‖ ≤ sup_{∂Ω(δ−d, B+d)} ‖H_η'‖ / d
                  ≈ 2.0844 / 0.040875 ≈ 51.

Since ‖H_η'‖ = O(1) while d ≈ 0.041, that single step contributes ≈ 91%
of the certified total (≈ 56.077 at the V9–V11 rectangle) even though the
*true* sup‖H_η''‖ is within O(η) of sup‖H_0''‖ ≈ 5.083.

This module keeps the closed-form `H_0''` term and applies the Cauchy
estimate to the **difference** g := H_η' − H_0' instead, which is O(η)
(certified ≈ 0.0541 on Ω by `compute_M_phi_prime_bound`). For p ∈ [0, 1],

    DD(p, w) = H_0''(w) + p · (H_η''(w) − H_0''(w)),

so

    ‖DD‖ ≤ sup_Ω ‖H_0''‖ + sup_Ω ‖H_η'' − H_0''‖
          ≤ sup_{∂Ω} ‖H_0''‖ + sup_{∂Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d,

with H_0''(w) = w / (1 − w²)^{3/2} in closed form. Both sups are boundary
scans (max modulus on the closed rectangle, exactly as in `m_pp.py`); the
enlarged rectangle is the same one `m_pp.py` already evaluates the
phi-series on, so the series is known to resolve tightly there.

At the V9–V11 rectangle (δ = 1635/10000, B = 1115/1000, d = δ/4) this
gives roughly 5.083 + 0.07/0.040875 ≈ 6.8, versus the legacy ≈ 56.077 —
an ≈ 8× tightening of the `M_pp` input to
`Braverman.Paper.Cr_phi_uzz`.

Backs the (unchanged) Lean axiom `Braverman.PaperV0.h_M_pp_oracle`; the
`[[oracles]]` row in `lemma.toml` is retargeted from
`compute_M_pp_bound` to `compute_M_pp_bound_tight`.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_deriv_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_pp_tight_for_params(
    eta: float,
    delta: str,
    B: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
    d_denom: int,
) -> dict:
    """Run the certified sup_{p, Ω} ‖∂²_z F_p‖ pipeline (difference form)."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ‖H_0''(w)‖ on ∂Ω via the closed form H_0''(w) = w/(1−w²)^{3/2}.
    #    (`u.rsqrt() / u` = u^{-1/2} / u = u^{-3/2}; same expression the
    #    legacy `m_pp.py` uses.)
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # 2. sup ‖H_η'' − H_0''‖ on Ω via Cauchy applied to the O(η)
    #    difference g = H_η' − H_0' over the enlarged rectangle
    #    Ω(δ − d, B + d), d = δ/d_denom.
    d = delta_arb / arb(d_denom)
    delta_inner = delta_arb - d      # rectangle half-width 1 − (δ − d)
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the H_η'' − H_0'' Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime_diff(z: acb) -> arb:
        H_eta_prime_val = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_prime_val = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_prime_val - H_0_prime_val)

    max_diff_outer = _max_on_rect(
        phi_prime_diff, delta_inner, B_outer, n_per_edge, prec,
    )
    max_pp_diff = max_diff_outer / d

    M_pp_arb = max_H0_pp + max_pp_diff

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_diff_outer_str": max_diff_outer.str(20, more=True),
        "max_pp_diff_str": max_pp_diff.str(20, more=True),
        "delta": delta,
        "B": B,
        "d_denom": d_denom,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_bound_tight(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    d_denom: int = 4,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on M_pp = sup_{p, Ω} ‖∂²_z F_p‖.

    Defaults match the V9–V11 oracle rectangle and `m_pp.py`'s scan
    parameters (`n_per_edge=1024`, `prec=256`, `K_max=100`, `d = δ/4`), so
    the enlarged-rectangle phi-series evaluation is on exactly the domain
    the legacy oracle already certifies. First call is ~60–120 s (two
    boundary scans); cached in `.cache/` thereafter.
    """
    key = {
        "fn": "compute_M_pp_bound_tight",
        "eta": eta, "delta": delta, "B": B, "d_denom": d_denom,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max, d_denom=d_denom,
    ))

    flint_ctx.prec = prec
    M_pp_arb = arb(cached["M_pp_str"])
    bound = arb_to_rational_ub(
        M_pp_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "d_denom": cached["d_denom"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_diff_outer_arb_str": cached["max_diff_outer_str"],
            "max_pp_diff_arb_str": cached["max_pp_diff_str"],
        },
    )
