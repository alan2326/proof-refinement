"""M_phi oracle: certified upper bound on

    M_phi = sup_{w ∈ Ω(δ, B)} ‖H_η(w) − H_0(w)‖

Replaces the loose triangle-inequality bound `‖Φ‖ = ‖H_η − H_0‖ ≤ 2M` used
in the current `Lemma54_Paper_Pderiv_Single.lean` Step 5 derivation. For
small η, `H_η ≈ H_0`, so the *direct* sup of |H_η − H_0| is much smaller
than `|H_η| + |H_0| ≤ 2M`.

Backs the proposed Lean axiom

    axiom h_M_phi_oracle :
      ∀ w ∈ oracle_domain, ‖H_eta η_val w - H0 w‖ ≤ M_phi_val

where `oracle_domain = Braverman.Omega delta_val B_val`.

Implementation: for each rectangle-boundary node `z`, compute
`|H_η(z) − H_0(z)|` directly (using the cached phi-series for H_η and the
acb arcsin function for H_0). Take the sup via `arb.max`. By the
maximum-modulus principle, sup on dΩ = sup on Ω̄.
"""

from __future__ import annotations

from typing import Optional

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_phi_for_params(
    eta: float,
    delta: str,
    B: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup |H_η − H_0| on dΩ pipeline."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    def f(z: acb) -> arb:
        H_eta_val = eval_H_eta_at_acb(phi_series, z, prec)
        H_0_val = z.asin()
        return abs_ub(H_eta_val - H_0_val)

    M_phi_arb = _max_on_rect(f, delta_arb, B_arb, n_per_edge, prec)

    return {
        "M_phi_str": M_phi_arb.str(20, more=True),
        "M_phi_upper_float": float(M_phi_arb.upper()),
        "delta": delta,
        "B": B,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_phi_bound(
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
    """Certified rational upper bound on M_phi = sup_{Ω} |H_η − H_0|.

    Defaults match the V8 oracle rectangle (`δ = 1635/10000`, `B = 1115/1000`)
    used by `compute_M_bound_tight`. The phi-series cache is shared with
    `m_phi_prime.py` and `m_pp.py`.

    Performance: first call (cold cache) is ~30–60s for n_per_edge=1024,
    prec=256. Subsequent calls hit the JSON cache in `.cache/`.
    """
    key = {
        "fn": "compute_M_phi_bound",
        "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_phi_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_phi_arb = arb(cached["M_phi_str"])
    bound = arb_to_rational_ub(
        M_phi_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_phi_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_phi_arb_str": cached["M_phi_str"],
        },
    )
