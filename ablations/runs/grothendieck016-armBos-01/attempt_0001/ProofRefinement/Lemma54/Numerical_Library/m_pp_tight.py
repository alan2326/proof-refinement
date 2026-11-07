"""Tight M_pp oracle: certified upper bound on

    M_pp_tight = sup_{(p, w) in [0, 1] x Omega(delta, B)}
                     ||(1-p) H_0''(w) + p H_eta''(w)||

i.e. sup ||iteratedDeriv 2 (F_p eta p) w||, the same quantity `m_pp.py`
bounds — but decomposed around H_0 instead of split into two independent
sups.

Why this is much tighter than `compute_M_pp_bound`
--------------------------------------------------
`m_pp.py` uses the triangle bound

    ||(1-p) H_0'' + p H_eta''||  <=  sup||H_0''|| + sup||H_eta''||

and estimates the second summand by Cauchy on an enlarged rectangle,
`sup||H_eta'||_out / d ~ 2.08 / 0.0409 ~ 51`, which dominates everything.
But the family is affine in p around H_0:

    (1-p) H_0''(w) + p H_eta''(w) = H_0''(w) + p * (H_eta'' - H_0'')(w),

and the *difference* is O(eta). So for p in [0, 1],

    ||d^2_z F_p(w)||  <=  sup_Omega ||H_0''||  +  sup_Omega ||H_eta'' - H_0''||
                      <=  sup_Omega ||H_0''||
                            + sup_{Omega_out} ||H_eta' - H_0'|| / d,

the last step by Cauchy's estimate on the disk of radius d = delta/4 about
each w in Omega (that disk lies in Omega_out = Omega(3*delta/4, B + d),
which is inside the strip |Re| < 1 where both H_0 and H_eta are analytic).

At eta = 1/100 on Omega(1635/10000, 1115/1000):

  * sup_Omega ||H_0''|| ~ 5.084.  Closed form H_0''(w) = w (1-w^2)^{-3/2};
    the sup is attained at w = +-(1-delta) on the real axis, where
    |1-w^2| = 0.30027 is smallest.  H_0'' is analytic on the closure of
    Omega (its singularities sit at w = +-1, i.e. |Re| = 1), so the
    boundary scan is a valid max-modulus argument.
  * sup_{Omega_out} ||H_eta' - H_0'|| ~ 0.08 (the same quantity certified
    on the *inner* rectangle by `compute_M_phi_prime_bound` is ~0.0541;
    widening |Re| from 0.8365 to 0.877375 inflates it mildly), so the
    Cauchy term is ~0.08/0.040875 ~ 1.97.

Total ~ 7.1, versus ~56.1 from `compute_M_pp_bound` — an ~8x tightening of
the term that dominates `Cr_phi_uzz`.

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      forall p in Ioo 0 pr_paper, forall w in oracle_domain,
        ||iteratedDeriv 2 (Braverman.F_p eta p) w|| <= M_pp_tight_val

(the `p in [0,1]` range covers `Ioo 0 pr_paper` via the seed axiom
`pr_paper_le_one`).

Implementation mirrors `m_pp.py` exactly, with one change: the enlarged-
rectangle scan is applied to `H_eta' - H_0'` rather than to `H_eta'`.
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
) -> dict:
    """Run the certified sup_{Omega} ||d^2_z F_p|| pipeline (tight form)."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ||H_0''(w)|| on dOmega, closed form H_0''(w) = w (1-w^2)^{-3/2}.
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 - w^2
        # rsqrt(u) = u^{-1/2}, so u^{-3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # 2. sup ||H_eta'' - H_0''|| on Omega via Cauchy on the enlarged
    #    rectangle Omega_out = Omega(3*delta/4, B + delta/4), applied to the
    #    *difference* H_eta' - H_0' (which is O(eta)).
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d      # = 3*delta/4  ->  |Re| <= 1 - 3*delta/4
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the Cauchy bound: "
            f"delta_inner = {delta_inner}"
        )

    def phi_prime(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H0_p)

    max_phi_prime_outer = _max_on_rect(
        phi_prime, delta_inner, B_outer, n_per_edge, prec,
    )
    max_phi_pp = max_phi_prime_outer / d

    M_pp_tight_arb = max_H0_pp + max_phi_pp

    return {
        "M_pp_tight_str": M_pp_tight_arb.str(20, more=True),
        "M_pp_tight_upper_float": float(M_pp_tight_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_phi_prime_outer_str": max_phi_prime_outer.str(20, more=True),
        "max_phi_pp_str": max_phi_pp.str(20, more=True),
        "delta": delta,
        "B": B,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_tight_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    M_pp_tight = sup_{p in [0,1], w in Omega} ||(1-p) H_0'' + p H_eta''||.

    Defaults match the V9-V11 oracle rectangle (delta = 1635/10000,
    B = 1115/1000) and the `m_pp.py` scan parameters, so the cached
    phi-series is shared with `m_phi.py`, `m_phi_prime.py` and `m_pp.py`.

    Performance: two `_max_on_rect` scans on different rectangles, same
    profile as `compute_M_pp_bound` (~60-120s cold, cached thereafter).
    """
    key = {
        "fn": "compute_M_pp_tight_bound",
        "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_pp_tight_arb = arb(cached["M_pp_tight_str"])
    bound = arb_to_rational_ub(
        M_pp_tight_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_tight_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_tight_arb_str": cached["M_pp_tight_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_phi_prime_outer_arb_str": cached["max_phi_prime_outer_str"],
            "max_phi_pp_arb_str": cached["max_phi_pp_str"],
        },
    )
