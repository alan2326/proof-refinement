"""M_phi_prime oracle: certified upper bound on

    M_phi_prime = sup_{w ∈ Ω(δ, B)} ‖H_η'(w) − H_0'(w)‖

Replaces the loose triangle-inequality bound `‖Φ'‖ ≤ 2M` used in the
current `Lemma54_Paper_Pderiv_Single.lean` Step 5 derivation. For small
η, `H_η' ≈ H_0'`, so the *direct* sup of |H_η' − H_0'| is much smaller
than `|H_η'| + |H_0'| ≤ 2M`.

Backs the proposed Lean axiom

    axiom h_M_phi_prime_oracle :
      ∀ w ∈ oracle_domain,
        ‖deriv (H_eta η_val) w - deriv H0 w‖ ≤ M_phi_prime_val

where `H_0'(w) = 1/√(1 − w²)`.

Implementation: for each rectangle-boundary node `z`, compute
`|H_η'(z) − H_0'(z)|` directly via the closed-form `H_0'(z) = (1−z²)^{−1/2}`
and `eval_H_eta_deriv_at_acb` for `H_η'(z)`. Take the sup via `arb.max`.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_deriv_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_phi_prime_for_params(
    eta: float,
    delta: str,
    B: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup |H_η' − H_0'| on dΩ pipeline."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    def f(z: acb) -> arb:
        H_eta_prime_val = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_prime_val = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_prime_val - H_0_prime_val)

    M_phi_prime_arb = _max_on_rect(f, delta_arb, B_arb, n_per_edge, prec)

    return {
        "M_phi_prime_str": M_phi_prime_arb.str(20, more=True),
        "M_phi_prime_upper_float": float(M_phi_prime_arb.upper()),
        "delta": delta,
        "B": B,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_phi_prime_bound(
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
    """Certified rational upper bound on M_phi_prime = sup_{Ω} |H_η' − H_0'|."""
    key = {
        "fn": "compute_M_phi_prime_bound",
        "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_phi_prime_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_phi_prime_arb = arb(cached["M_phi_prime_str"])
    bound = arb_to_rational_ub(
        M_phi_prime_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_phi_prime_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_phi_prime_arb_str": cached["M_phi_prime_str"],
        },
    )
