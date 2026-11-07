"""
R-bound: rigorous upper bound on
    sup{ ‖F_p⁻¹(ζ)‖ : ζ ∈ closedBall(0, (1+r)/2), p ∈ (0, p_r) }

Justification (Braverman et al. 2011, Lemma 5.3 + Rouché): F_p maps
Ω(δ, B) bijectively onto a domain containing ((1+r)/2)·D, hence
F_p⁻¹(ζ) ∈ Ω for all such ζ. Therefore
    ‖F_p⁻¹(ζ)‖ ≤ max_{w ∈ Ω̄} ‖w‖ = √((1-δ)² + B²)

(corner-of-rectangle distance). This wraps
`grothendieck.proof.certified.compute_cr.compute_R_rigorous` and rounds
up to a Fraction.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Optional

from flint import arb, ctx as flint_ctx

from grothendieck.proof.certified.compute_cr import (
    compute_R_rigorous,
)
from grothendieck.proof.certified.certify_invertibility import (
    certify_invertibility,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from .types import OracleResult


def _compute_R_for_params(
    r: str,
    eta: float,
    delta: Optional[str],
    B: Optional[str],
    prec: int,
) -> dict:
    flint_ctx.prec = prec
    if delta is None or B is None:
        inv = certify_invertibility(r=float(arb(r)), eta=eta, prec=prec, verbose=False)
        delta_arb = inv["delta"]
        B_arb = inv["B"]
    else:
        delta_arb = arb(delta)
        B_arb = arb(B)
    R_arb = compute_R_rigorous(delta_arb, B_arb, prec=prec)
    return {
        "R_str": R_arb.str(20, more=True),
        "R_upper_float": float(R_arb.upper()),
        "delta_str": delta_arb.str(20, more=True),
        "B_str": B_arb.str(20, more=True),
        "prec": prec,
    }


def compute_R_bound(
    *,
    r: str = "23/25",
    eta: float = 0.01,
    delta: Optional[str] = None,
    B: Optional[str] = None,
    prec: int = 128,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
) -> OracleResult:
    """Certified rational upper bound on R = sup ‖F_p⁻¹‖ over disk (1+r)/2."""
    key = {
        "fn": "compute_R_bound",
        "r": r, "eta": eta, "delta": delta, "B": B, "prec": prec,
    }
    cached = cached_run(key, lambda: _compute_R_for_params(
        r=r, eta=eta, delta=delta, B=B, prec=prec,
    ))
    flint_ctx.prec = prec
    R_arb = arb(cached["R_str"])
    bound = arb_to_rational_ub(R_arb, safety_rel=safety_rel, max_denom=max_denom)
    return OracleResult(
        bound=bound,
        ball_value=cached["R_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta_str"],
            "B": cached["B_str"],
            "R_arb_str": cached["R_str"],
        },
    )


def compute_R_bound_tight(**overrides) -> OracleResult:
    """Same (δ, B) as compute_M_bound_tight."""
    params = dict(
        r="23/25", eta=0.01,
        delta="163/1000", B="1115/1000",
        prec=200,
        max_denom=10000, safety_rel=1e-3,
    )
    params.update(overrides)
    return compute_R_bound(**params)
