# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_*at_acb` family from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The bound inherits an
# unbounded heuristic step.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the truncation-free replacement: Scratch/joint_merged_uderiv.py's
# `_eval_three_at_cell` (in Scratch/_naive_audit.py) computes
# `joint_phi_phip_invD2 = sup |Phi·Phi'/D²|` per (chunk, p-cell) using
# 2nd-order Taylor pad in w with rigorous Cauchy `M_phi_ppp` remainder.
# The Evaluator's G7.a will fail any candidate whose oracle path reaches
# `eval_H_eta_*at_acb`.
# =============================================================================
"""joint_phi_phip_invD2 oracle: certified upper bound on

    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)}  ‖Phi(w) · Phi'(w) / D(p, w)²‖

where
    Phi(w)   = H_eta(w) - H_0(w)
    Phi'(w)  = H_eta'(w) - H_0'(w)
    D(p, w)  = (1−p)·H_0'(w) + p·H_eta'(w)

This is the joint analytic quotient that bounds term-1 of
`Cr_phi_uzz_direct`. By taking a single direct sup over the joint
expression instead of the triangle product
`M_phi · M_phi_prime · inv_F_p_z²`, the bound aligns with whatever
single (p, w) actually achieves the worst-case product, rather than
inflating each factor independently to its own corner.

Backs the proposed Lean axiom

    axiom h_joint_phi_phip_invD2_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper ...),
      ∀ w ∈ oracle_domain,
        ‖(H_eta η w - H0 w) * (deriv (H_eta η) w - deriv H0 w)‖
          ≤ ‖deriv (F_p η p) w‖^2 * joint_phi_phip_invD2_val

(equivalently `‖Phi · Phi'‖ / ‖D‖² ≤ joint_phi_phip_invD2_val`).

Strategy. We scan the boundary `∂Ω` in `w` at high resolution. For each
`w`-cell `Phi` and `Phi'` are p-INDEPENDENT (they're η-perturbations of
H_0 and H_0', not p-dependent), so the per-cell numerator
`abs_ub(Phi) · abs_ub(Phi')` is constant across all p-subintervals. The
divisor `|D|^2 = |(1−p) H_0' + p H_eta'|^2` varies with p, and we
compute a per-cell lower bound `|D|_lb` on each subdivided
`(w-cell, p-interval)`. The per-cell ratio
`abs_ub(Phi) · abs_ub(Phi') / abs_lb(D)^2` upper-bounds
`|Phi · Phi' / D²|` on the cell. The max over cells is a certified
upper bound on the joint sup.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_lb, abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _iter_rect_boundary
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_at_acb,
    eval_H_eta_deriv_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _H0_at_acb(w: acb) -> acb:
    """H_0(w) = arcsin(w)."""
    return w.asin()


def _H0_prime_at_acb(w: acb) -> acb:
    """H_0'(w) = (1 − w²)^{−1/2}."""
    return (acb(1) - w * w).rsqrt()


def _compute_joint_phi_phip_invD2_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    n_p_subdiv: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} ‖Phi · Phi' / D²‖ pipeline.

    For each w-cell on ∂Ω(δ, B):
      - compute `Phi_iv = H_eta(w) - H_0(w)` and
        `Phi_p_iv = H_eta'(w) - H_0'(w)` (both p-independent).
      - For each p-subinterval `[p_lo, p_hi] ⊂ [0, p_max]`:
        - compute `D_iv = H_0' + p_iv · (H_eta' - H_0')`
        - bound `|D|_lb = abs_lb(D_iv)`, abort if non-positive.
        - per-cell ratio = `abs_ub(Phi_iv) * abs_ub(Phi_p_iv) / |D|_lb²`.
        - track running max.

    The global max is a certified upper bound on the joint sup.
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
        # Compute Phi(w) = H_eta(w) - H_0(w).
        H0_v = _H0_at_acb(w_acb)
        H_eta_v = eval_H_eta_at_acb(phi_series, w_acb, prec)
        Phi_iv = H_eta_v - H0_v
        # Compute Phi'(w) = H_eta'(w) - H_0'(w).
        H0_p_val = _H0_prime_at_acb(w_acb)
        H_eta_p_val = eval_H_eta_deriv_at_acb(phi_series, w_acb, prec)
        Phi_p_iv = H_eta_p_val - H0_p_val
        # Numerator upper bound: |Phi(w)| · |Phi'(w)| (constant in p).
        numer_ub = abs_ub(Phi_iv) * abs_ub(Phi_p_iv)
        # H_eta'(w) − H_0'(w), used to construct D(p, w) = H_0' + p · Phi'.
        D_diff = H_eta_p_val - H0_p_val

        for j in range(n_p_subdiv):
            p_lo = p_max_arb * arb(j) / arb(n_p_subdiv)
            p_hi = p_max_arb * arb(j + 1) / arb(n_p_subdiv)
            p_iv = arb.union(p_lo, p_hi)

            D_iv = H0_p_val + acb(p_iv) * D_diff

            D_lb = abs_lb(D_iv)

            if not certified_positive(D_lb):
                n_failed += 1
                n_total += 1
                continue

            ratio = numer_ub / (D_lb ** 2)
            max_g = arb.max(max_g, ratio)
            n_total += 1

    if n_failed > 0:
        raise ValueError(
            f"compute_joint_phi_phip_invD2_bound: {n_failed}/{n_total} cells "
            f"could not certify |D|>0; increase n_per_edge or n_p_subdiv."
        )

    return {
        "joint_phi_phip_invD2_str": max_g.str(20, more=True),
        "joint_phi_phip_invD2_upper_float": float(max_g.upper()),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "n_p_subdiv": n_p_subdiv,
        "prec": prec,
        "K_max": K_max,
        "n_total": n_total,
    }


def compute_joint_phi_phip_invD2_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 65536,  # n_per_edge=65536 from sprint_028 (fresh-scan ball value 4.622·10⁻⁶, rationalised 47/10000000 ≈ 4.70·10⁻⁶ slack 1.70%); was 32768 in sprint_027 (ball 6.452·10⁻⁶, rationalised 13/2000000 slack 0.74% with safety_abs=1e-8/max_denom=10⁷ rationaliser from sprint_026)
    n_p_subdiv: int = 4,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-8,
) -> OracleResult:
    """Certified rational upper bound on
    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖Phi(w) · Phi'(w) / D(p,w)²‖.

    Defaults match the V13 oracle rectangle (δ = 1635/10000,
    B = 1115/1000) and `p_max = 1` (uses the `pr_paper ≤ 1` seed
    axiom for the universal quantifier in the corresponding Lean axiom).

    Note `safety_abs = 1e-8` and `max_denom = 10000000` (sprint_026
    tightening; previously 1e-7 / 1M from sprint_021): at
    n_per_edge=65536 (sprint_028 resolution-tightening), the
    ball_value drops to 4.622·10⁻⁶ and the rationaliser extracts
    47/10000000 ≈ 4.70·10⁻⁶ with ~1.70% slack. Previously at
    n_per_edge=32768 (sprint_027), the ball_value was 6.452·10⁻⁶,
    rationalised 13/2000000 ≈ 6.50·10⁻⁶ with ~0.74% slack.

    Performance: scans 4·n_per_edge·n_p_subdiv ≈ 1048k cells at
    n_per_edge=65536, prec=200; sprint_028 measured fresh at 66.2s
    (much faster than the per-doubling 4× extrapolation suggested,
    since per-cell work is dominated by acb-arithmetic constants
    that don't scale linearly in cell count). Cache populated. The
    cache key intentionally excludes `safety_*` and `max_denom`
    params, so future rationaliser tightening hits the existing
    cache instantly with no recomputation.
    """
    key = {
        "fn": "compute_joint_phi_phip_invD2_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "n_p_subdiv": n_p_subdiv,
        "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_joint_phi_phip_invD2_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, n_p_subdiv=n_p_subdiv,
        prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    joint_arb = arb(cached["joint_phi_phip_invD2_str"])
    bound = arb_to_rational_ub(
        joint_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["joint_phi_phip_invD2_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "n_p_subdiv": cached["n_p_subdiv"],
            "K_max": cached["K_max"],
            "n_total": cached["n_total"],
            "joint_phi_phip_invD2_arb_str": cached["joint_phi_phip_invD2_str"],
        },
    )
