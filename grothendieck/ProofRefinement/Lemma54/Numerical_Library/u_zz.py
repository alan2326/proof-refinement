# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_*at_acb` family from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The bound inherits an
# unbounded heuristic step.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the truncation-free replacement (Scratch/joint_merged_uderiv.py
# computes |DD/D³| with the same per-cell Taylor pad as the merged
# numerator), the cached round-3 chunks, and the binding rules R1–R5.
# The Evaluator's G7.a will fail any candidate whose oracle path reaches
# `eval_H_eta_*at_acb`.
# =============================================================================
"""u_zz oracle: certified upper bound on the analytic quotient

    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)}  ‖DD(p, w)‖ / ‖D(p, w)‖^3

where
    D(p, w)  = (1−p)·H_0'(w)  + p·H_eta'(w)
    DD(p, w) = (1−p)·H_0''(w) + p·H_eta''(w)

This is exactly `‖∂²_z F_p(η, p, w)‖ / ‖∂_z F_p(η, p, w)‖³`. By the
auxiliary z-identity `DD · h_z² + D · u_zz = 0` (Lemma
`F_inv_aux_z_identity`) combined with `‖h_z‖ = 1/‖D‖`, we have
`‖u_zz‖ = ‖DD‖ / ‖D‖³` exactly. Thus this oracle directly bounds
`‖u_zz‖` — a single sup over the joint analytic quotient, instead of
the loose triangle product `M_pp · inv_F_p_z³` which inflates by ~224×
on the V11 rectangle.

Backs the proposed Lean axiom

    axiom h_u_zz_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper ...),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η p) w‖
          ≤ ‖deriv (Braverman.F_p η p) w‖^3 * u_zz_bound_val

(equivalently `‖DD‖/‖D‖³ ≤ u_zz_bound_val`).

Strategy. We scan the boundary `∂Ω` in `w` at high resolution, and for
each `w`-cell, subdivide `p ∈ [0, p_max]` into small intervals. On each
`(w-cell, p-interval)` we use arb interval arithmetic to obtain
certified `‖DD‖_ub` and `‖D‖_lb`; then `‖DD‖_ub / ‖D‖_lb^3` upper-bounds
the quotient on the cell. The max over cells is a certified upper bound
on the joint sup.

Closed form at p=0: `H_0''(w) / H_0'(w)³ = w` exactly (since
`H_0'(w)³ = (1−w²)^{−3/2}` and `H_0''(w) = w·(1−w²)^{−3/2}` cancel).
So `g(0, w) = |w| ≤ √((1−δ)² + B²) ≈ 1.394` on the V11 rectangle. The
η=1/100 perturbation `(p · (H_eta_p − H_0_p))` adds ~10%, so the
certified bound is well below 2.

The H_eta'' evaluator is built from the closed-form chain rule on
`H_eta(w) = arcsin(w) − phi(arcsin(w))/cos(arcsin(w))`. With
`u(z) := phi(z) sec(z)`:

    u'(z)  = sec(z) · (phi'(z) + phi(z) tan(z))
    u''(z) = sec(z) · (phi''(z) + 2 phi'(z) tan(z)
                        + phi(z) (2 sec²(z) − 1))
    H_eta'(w)  = (1 − u'(z)) / cos(z),                      z = arcsin(w)
    H_eta''(w) = −u''(z)/cos²(z) + (1 − u'(z)) sin(z)/cos³(z)

We compute `phi(z), phi'(z), phi''(z)` by simultaneous Horner on the
phi_series coefficients (extending the existing
`eval_phi_and_deriv_at_acb` to second order).
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_lb, abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _iter_rect_boundary

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _eval_phi_phi_p_phi_pp_at_acb(phi_series, z: acb) -> tuple:
    """Evaluate phi(z), phi'(z), phi''(z) at acb z via simultaneous Horner.

    Returns (phi_v, phi_p, phi_pp) as acb.
    """
    coeffs = phi_series.coeffs()
    n = len(coeffs)
    if n == 0:
        return acb(0), acb(0), acb(0)
    if n == 1:
        return acb(coeffs[0]), acb(0), acb(0)
    if n == 2:
        return acb(coeffs[0]) + acb(coeffs[1]) * z, acb(coeffs[1]), acb(0)
    # Horner with simultaneous derivative and second derivative:
    #   p   = c_{n-1}
    #   p'  = 0
    #   p'' = 0
    # for k = n-2 down to 0:
    #   p'' = p''*z + 2*p'
    #   p'  = p'*z  + p
    #   p   = p*z   + c_k
    p_v = acb(coeffs[n - 1])
    p_p = acb(0)
    p_pp = acb(0)
    for k in range(n - 2, -1, -1):
        new_pp = p_pp * z + acb(2) * p_p
        new_p = p_p * z + p_v
        new_v = p_v * z + acb(coeffs[k])
        p_pp, p_p, p_v = new_pp, new_p, new_v
    return p_v, p_p, p_pp


def _eval_H_eta_p_pp_at_acb(phi_series, w_acb: acb) -> tuple:
    """Evaluate H_eta'(w) and H_eta''(w) using the chain-rule formula.

    Returns (H_eta_p, H_eta_pp) as acb.
    """
    z = w_acb.asin()
    cos_z = z.cos()
    sin_z = z.sin()
    sec_z = acb(1) / cos_z
    tan_z = sin_z / cos_z
    sec_sq = sec_z * sec_z

    phi_v, phi_p, phi_pp = _eval_phi_phi_p_phi_pp_at_acb(phi_series, z)

    # u(z)   = phi(z) sec(z)
    # u'(z)  = sec(z) (phi'(z) + phi(z) tan(z))
    # u''(z) = sec(z) (phi''(z) + 2 phi'(z) tan(z) + phi(z) (2 sec²(z) - 1))
    u_p = sec_z * (phi_p + phi_v * tan_z)
    u_pp = sec_z * (
        phi_pp + acb(2) * phi_p * tan_z + phi_v * (acb(2) * sec_sq - acb(1))
    )

    cos_sq = cos_z * cos_z
    cos_cu = cos_sq * cos_z

    H_eta_p = (acb(1) - u_p) / cos_z
    H_eta_pp = -u_pp / cos_sq + (acb(1) - u_p) * sin_z / cos_cu
    return H_eta_p, H_eta_pp


def _H0_prime_at_acb(w: acb) -> acb:
    """H_0'(w) = (1 − w²)^{−1/2}."""
    return (acb(1) - w * w).rsqrt()


def _H0_pp_at_acb(w: acb) -> acb:
    """H_0''(w) = w · (1 − w²)^{−3/2}."""
    u = acb(1) - w * w
    return w * u.rsqrt() / u


def _compute_u_zz_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    n_p_subdiv: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} ‖DD‖/‖D‖³ pipeline.

    For each w-cell on ∂Ω(δ, B) and each p-subinterval of [0, p_max]:
    bound `|D|_lb = abs_lb(D_iv)` (via interval arb arithmetic on acb)
    and `|DD|_ub = abs_ub(DD_iv)`; the per-cell ratio `|DD|_ub /
    |D|_lb^3` upper-bounds the quotient there. The global max over cells
    is a certified upper bound.
    """
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    max_g = arb(0)
    n_failed = 0
    n_total = 0
    for w_acb in _iter_rect_boundary(delta_arb, B_arb, n_per_edge, prec):
        H0_p_val = _H0_prime_at_acb(w_acb)
        H0_pp_val = _H0_pp_at_acb(w_acb)
        He_p_val, He_pp_val = _eval_H_eta_p_pp_at_acb(phi_series, w_acb)
        D_diff = He_p_val - H0_p_val
        DD_diff = He_pp_val - H0_pp_val

        for j in range(n_p_subdiv):
            p_lo = p_max_arb * arb(j) / arb(n_p_subdiv)
            p_hi = p_max_arb * arb(j + 1) / arb(n_p_subdiv)
            p_iv = arb.union(p_lo, p_hi)

            D_iv = H0_p_val + acb(p_iv) * D_diff
            DD_iv = H0_pp_val + acb(p_iv) * DD_diff

            D_lb = abs_lb(D_iv)
            DD_ub = abs_ub(DD_iv)

            if not certified_positive(D_lb):
                n_failed += 1
                n_total += 1
                continue

            ratio = DD_ub / (D_lb ** 3)
            max_g = arb.max(max_g, ratio)
            n_total += 1

    if n_failed > 0:
        raise ValueError(
            f"compute_u_zz_bound: {n_failed}/{n_total} cells could not "
            f"certify |D|>0; increase n_per_edge or n_p_subdiv."
        )

    return {
        "u_zz_str": max_g.str(20, more=True),
        "u_zz_upper_float": float(max_g.upper()),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "n_p_subdiv": n_p_subdiv,
        "prec": prec,
        "K_max": K_max,
        "n_total": n_total,
    }


def compute_u_zz_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 2048,
    n_p_subdiv: int = 4,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖DD(p,w)‖ / ‖D(p,w)‖^3.

    Defaults match the V12 oracle rectangle (δ = 1635/10000,
    B = 1115/1000) and `p_max = 1` (uses the `pr_paper ≤ 1` seed
    axiom for the universal quantifier in the corresponding Lean axiom).

    Performance: scans 4·n_per_edge·n_p_subdiv ≈ 32k cells at
    n_per_edge=2048, prec=200; first call ~30–60s, cached thereafter.
    """
    key = {
        "fn": "compute_u_zz_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "n_p_subdiv": n_p_subdiv,
        "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_u_zz_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, n_p_subdiv=n_p_subdiv,
        prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    u_zz_arb = arb(cached["u_zz_str"])
    bound = arb_to_rational_ub(
        u_zz_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["u_zz_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "n_p_subdiv": cached["n_p_subdiv"],
            "K_max": cached["K_max"],
            "n_total": cached["n_total"],
            "u_zz_arb_str": cached["u_zz_str"],
        },
    )
