"""Rigorous chunk bound for sup_{z ∈ Z} |H_η''(z)| via the real-majorant.

From the LLM analysis:
    |H_η''(z)| ≤ (1/(π·d_Z)) · ∫∫ |1+P'Q'| · E_Z(x,y) ·
              · (2·|z|_ub/d_Z + (2·|z|_ub·A + 2·(1+|z|²_ub)·|B|)/d_Z²) dx dy

where E_Z, d_Z, α_Z, β_Z come from the chunk-constants helper, and
A(x,y) = x²+P²+y²+Q², B(x,y) = xy+PQ.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Callable

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))

from grothendieck.proof.certified.bk_rigor import (
    h3_arb,
    compute_gl_nodes_weights_arb,
    scale_gl_to_interval,
)


def _chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    one_minus_z = acb(1) - z_ball
    one_plus_z = acb(1) + z_ball
    one_minus_z2 = one_minus_z * one_plus_z
    inv_one_minus_z = acb(1) / one_minus_z
    inv_one_plus_z = acb(1) / one_plus_z
    d_Z = one_minus_z2.abs_lower()
    alpha_Z = inv_one_minus_z.real.lower()
    if alpha_Z < arb(0): alpha_Z = arb(0)
    beta_Z = inv_one_plus_z.real.lower()
    if beta_Z < arb(0): beta_Z = arb(0)
    z_abs_ub = z_ball.abs_upper()
    return d_Z, alpha_Z, beta_Z, z_abs_ub


def bound_H_eta_pp_on_chunk(
    z_ball: acb,
    P: Callable, Pp: Callable,
    Q: Callable, Qp: Callable,
    L_outer: int = 8,
    n_panels: int = 8,
    n_gl: int = 20,
    prec: int = 200,
    gl_dps: int = 80,
    verbose: bool = False,
) -> arb:
    """Upper bound on sup_{z ∈ Z} |H_η''(z)| via real-positive majorant.
    Uses GL on the real integrand; rigor inherits the standard caveat
    about GL error.
    """
    flint_ctx.prec = prec
    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)
    d_Z2 = d_Z * d_Z
    half = arb(1) / arb(2)
    one_plus_z2_ub = arb(1) + z_abs_ub * z_abs_ub
    two_z = arb(2) * z_abs_ub
    two_z_over_d = two_z / d_Z

    if verbose:
        print(f"  d_Z={float(d_Z):.4e}, |z|_ub={float(z_abs_ub):.4f}")

    L_arb = arb(L_outer)
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []
    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(ref_nodes, ref_weights, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            all_nodes.append((nd, wt))

    P_at = [P(nd, prec) for nd, _ in all_nodes]
    Pp_at = [Pp(nd, prec) for nd, _ in all_nodes]
    Q_at = [Q(nd, prec) for nd, _ in all_nodes]
    Qp_at = [Qp(nd, prec) for nd, _ in all_nodes]

    integral_sum = arb(0)
    for j in range(len(all_nodes)):
        y_j, w_y = all_nodes[j]
        Q_y = Q_at[j]
        Qp_y = Qp_at[j]
        for i in range(len(all_nodes)):
            x_i, w_x = all_nodes[i]
            P_x = P_at[i]
            Pp_x = Pp_at[i]
            diff_x = x_i - y_j
            diff_P = P_x - Q_y
            sum_x = x_i + y_j
            sum_P = P_x + Q_y
            minus_sq = diff_x * diff_x + diff_P * diff_P
            plus_sq = sum_x * sum_x + sum_P * sum_P

            E = (-half * (alpha_Z * minus_sq + beta_Z * plus_sq)).exp()
            J_abs = abs(arb(1) + Pp_x * Qp_y)

            A = x_i * x_i + P_x * P_x + y_j * y_j + Q_y * Q_y
            B_abs = abs(x_i * y_j + P_x * Q_y)
            extra = two_z_over_d + (two_z * A + arb(2) * one_plus_z2_ub * B_abs) / d_Z2

            integral_sum += w_x * w_y * J_abs * E * extra

    return integral_sum / (arb.pi() * d_Z)


# ----------------------------------------------------------------------
if __name__ == "__main__":
    PREC = 200
    flint_ctx.prec = PREC

    sys.path.insert(0, str(_HERE))
    from h_eta_prime_integral import make_v26_P, make_v26_Pprime

    eta_arb = arb("0.01")
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    print("=" * 72)
    print("Test: H_η'' chunk bound vs known arcsin'' value")
    print("=" * 72)

    # arcsin''(0.5) = 0.5/(0.75)^{1.5} ≈ 0.7698
    z_ball = acb(arb.union(arb("0.45"), arb("0.55")), arb(0))
    print(f"chunk: Re ∈ [0.45, 0.55], Im = 0")
    print(f"arcsin''(0.5) ≈ 0.7698")

    t0 = time.time()
    bound = bound_H_eta_pp_on_chunk(
        z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
        L_outer=8, n_panels=8, n_gl=20, prec=PREC, verbose=True,
    )
    t1 = time.time()
    print(f"\nbound = {float(bound):.4e}")
    print(f"time: {t1-t0:.2f}s")
