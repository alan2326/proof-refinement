# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_*at_acb` family from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The bound inherits an
# unbounded heuristic step.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the truncation-free replacement: Scratch/_naive_audit.py's
# `_eval_three_at_cell` computes `uzz_phi_sq = sup |DD·Phi²/D³|` per
# (chunk, p-cell) using the patched joint-oracle Taylor pad. The
# Evaluator's G7.a will fail any candidate whose oracle path reaches
# `eval_H_eta_*at_acb`.
# =============================================================================
"""uzz_phi_sq oracle: certified upper bound on the joint analytic quotient

    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)}  ‖DD(p, w) · Phi(w)² / D(p, w)³‖

where
    Phi(w)   = H_eta(w) - H_0(w)
    D(p, w)  = (1−p)·H_0'(w)  + p·H_eta'(w)
    DD(p, w) = (1−p)·H_0''(w) + p·H_eta''(w)

By the auxiliary z-identity (Lemma `F_inv_aux_z_identity`) combined with
`‖h_z‖ = 1/‖D‖`, we have `‖u_zz‖ = ‖DD‖/‖D‖³`, so this quotient equals
`‖u_zz‖ · ‖Phi‖²` exactly. By taking a single direct sup over the joint
quantity instead of the triangle product `u_zz_bound · M_phi²`, the bound
aligns with whatever single (p, w) actually achieves the worst-case
product, rather than inflating each factor independently to its own
corner.

Backs the proposed Lean axiom

    axiom h_uzz_phi_sq_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper ...),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η p) w
            * (H_eta η w - H0 w) ^ 2‖
          ≤ ‖deriv (F_p η p) w‖^3 * uzz_phi_sq_val

(equivalently `‖DD · Phi²‖ / ‖D‖³ ≤ uzz_phi_sq_val`).

Strategy. We scan the boundary `∂Ω` in `w` at high resolution. For each
`w`-cell, `Phi` is p-INDEPENDENT (it's the η-perturbation of H_0, not
p-dependent), so the per-cell `phi_sq_ub = abs_ub(Phi)²` is constant
across all p-subintervals. The divisor `|D|^3` and numerator factor
`|DD|` vary with p, and we compute per-cell `|D|_lb` and `|DD|_ub` on
each subdivided `(w-cell, p-interval)`. The per-cell ratio
`(|DD|_ub · phi_sq_ub) / |D|_lb^3` upper-bounds `|DD · Phi² / D³|` on
the cell. The max over cells is a certified upper bound on the joint
sup.

The `H_eta''` evaluator is shared with `u_zz.py` via
`_eval_H_eta_p_pp_at_acb`.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_lb, abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _iter_rect_boundary
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult
from .u_zz import _eval_H_eta_p_pp_at_acb


def _H0_at_acb(w: acb) -> acb:
    """H_0(w) = arcsin(w)."""
    return w.asin()


def _H0_prime_at_acb(w: acb) -> acb:
    """H_0'(w) = (1 − w²)^{−1/2}."""
    return (acb(1) - w * w).rsqrt()


def _H0_pp_at_acb(w: acb) -> acb:
    """H_0''(w) = w · (1 − w²)^{−3/2}."""
    u = acb(1) - w * w
    return w * u.rsqrt() / u


def _compute_uzz_phi_sq_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    n_p_subdiv: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} ‖DD · Phi² / D³‖ pipeline.

    For each w-cell on ∂Ω(δ, B):
      - compute `Phi_iv = H_eta(w) - H_0(w)` (p-independent),
        `phi_sq_ub = abs_ub(Phi_iv) ** 2`.
      - For each p-subinterval `[p_lo, p_hi] ⊂ [0, p_max]`:
        - compute `D_iv = H_0'  + p_iv · (H_eta' - H_0')`,
          `DD_iv = H_0'' + p_iv · (H_eta'' - H_0'')`.
        - bound `|D|_lb = abs_lb(D_iv)`, abort if non-positive.
        - per-cell ratio = `abs_ub(DD_iv) * phi_sq_ub / |D|_lb^3`.
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
        # Compute Phi(w) = H_eta(w) - H_0(w) (p-independent).
        H0_v = _H0_at_acb(w_acb)
        H_eta_v = eval_H_eta_at_acb(phi_series, w_acb, prec)
        Phi_iv = H_eta_v - H0_v
        phi_ub = abs_ub(Phi_iv)
        phi_sq_ub = phi_ub * phi_ub

        # First/second derivatives of H_0 and H_eta at w (all p-independent).
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

            numer_ub = DD_ub * phi_sq_ub
            denom_lb = D_lb ** 3
            ratio = numer_ub / denom_lb
            max_g = arb.max(max_g, ratio)
            n_total += 1

    if n_failed > 0:
        raise ValueError(
            f"compute_uzz_phi_sq_bound: {n_failed}/{n_total} cells "
            f"could not certify |D|>0; increase n_per_edge or n_p_subdiv."
        )

    return {
        "uzz_phi_sq_str": max_g.str(20, more=True),
        "uzz_phi_sq_upper_float": float(max_g.upper()),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "n_p_subdiv": n_p_subdiv,
        "prec": prec,
        "K_max": K_max,
        "n_total": n_total,
    }


def compute_uzz_phi_sq_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 65536,  # n_per_edge=65536 from sprint_028 (fresh-scan ball value 2.368·10⁻⁶, rationalised 3/1250000 ≈ 2.40·10⁻⁶ slack 1.33%); was 32768 in sprint_027 (ball 2.993·10⁻⁶, rationalised 31/10000000 slack 3.57% with safety_abs=1e-8/max_denom=10⁷ rationaliser from sprint_026)
    n_p_subdiv: int = 4,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-8,
) -> OracleResult:
    """Certified rational upper bound on
    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖DD(p,w) · Phi(w)² / D(p,w)^3‖.

    Defaults match the V14 oracle rectangle (δ = 1635/10000,
    B = 1115/1000) and `p_max = 1` (uses the `pr_paper ≤ 1` seed
    axiom for the universal quantifier in the corresponding Lean axiom).

    Note `safety_abs = 1e-8` and `max_denom = 10000000` (sprint_026
    tightening; previously 1e-7 / 1M from sprint_021): at
    n_per_edge=65536 (sprint_028 resolution-tightening), the
    ball_value drops to 2.368·10⁻⁶ and the rationaliser extracts
    3/1250000 ≈ 2.40·10⁻⁶ with ~1.33% slack. Previously at
    n_per_edge=32768 (sprint_027), the ball_value was 2.993·10⁻⁶,
    rationalised 31/10000000 ≈ 3.10·10⁻⁶ with ~3.57% slack.

    Performance: scans 4·n_per_edge·n_p_subdiv ≈ 1048k cells at
    n_per_edge=65536, prec=200; sprint_028 measured fresh at 90.9s.
    Cache populated.
    """
    key = {
        "fn": "compute_uzz_phi_sq_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "n_p_subdiv": n_p_subdiv,
        "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_uzz_phi_sq_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, n_p_subdiv=n_p_subdiv,
        prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    uzz_phi_sq_arb = arb(cached["uzz_phi_sq_str"])
    bound = arb_to_rational_ub(
        uzz_phi_sq_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["uzz_phi_sq_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "n_p_subdiv": cached["n_p_subdiv"],
            "K_max": cached["K_max"],
            "n_total": cached["n_total"],
            "uzz_phi_sq_arb_str": cached["uzz_phi_sq_str"],
        },
    )
