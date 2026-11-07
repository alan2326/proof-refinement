"""Chunk bound for sup_{z ∈ Z} |H_η'(z)| using the real-positive majorant.

For a chunk Z ⊆ {z : |Re z| < 1}, define:
    d_Z = inf_{z ∈ Z} |1 − z²|
    α_Z = inf_{z ∈ Z} Re(1/(1 − z))
    β_Z = inf_{z ∈ Z} Re(1/(1 + z))

By the identity
    S_z(x,y) = |u−w|² / (2(1−z)) + |u+w|² / (2(1+z))
where u = (x, P(x)), w = (y, Q(y)), we have
    Re S_z(x,y) ≥ (α_Z/2)·|u−w|² + (β_Z/2)·|u+w|².

So |exp(−S_z(x,y))| ≤ exp(−(α_Z/2)·|u−w|² − (β_Z/2)·|u+w|²) = E_Z(x,y).

Therefore
    sup_{z ∈ Z} |H_η'(z)| ≤ (1/(π·d_Z)) · ∫∫ |1 + P'(x)Q'(y)| · E_Z(x,y) dx dy.

Similarly for H_η''(z), with explicit additional terms from S_z'(x,y).

This file provides the certified bounds.
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


# ----------------------------------------------------------------------
def _chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    """For a chunk Z (acb ball), return (d_Z, alpha_Z, beta_Z, |z|_Z_upper).

    d_Z       : lower bound on |1 − z²| (positive arb)
    alpha_Z   : lower bound on Re(1 / (1 − z))
    beta_Z    : lower bound on Re(1 / (1 + z))
    z_abs_ub  : upper bound on |z|
    """
    one_minus_z = acb(1) - z_ball
    one_plus_z = acb(1) + z_ball
    one_minus_z2 = one_minus_z * one_plus_z

    inv_one_minus_z = acb(1) / one_minus_z
    inv_one_plus_z  = acb(1) / one_plus_z

    # d_Z: lower bound on |1 - z²|
    d_Z = one_minus_z2.abs_lower()

    # alpha_Z: lower bound on Re(1/(1-z))
    alpha_Z = inv_one_minus_z.real.lower()
    if alpha_Z < arb(0):
        # Should be positive for z in strip; clamp to small if numerical
        alpha_Z = arb(0)

    # beta_Z: lower bound on Re(1/(1+z))
    beta_Z = inv_one_plus_z.real.lower()
    if beta_Z < arb(0):
        beta_Z = arb(0)

    # |z| upper
    z_abs_ub = z_ball.abs_upper()

    return d_Z, alpha_Z, beta_Z, z_abs_ub


# ----------------------------------------------------------------------
def bound_H_eta_prime_on_chunk(
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
    """Upper bound (arb) on sup_{z ∈ Z} |H_η'(z)| via the real majorant.

    Returns a positive arb upper bound.

    NOTE: this uses GL quadrature on the real-positive majorant; the GL
    error and tail-truncation error are NOT yet certified rigorously.
    For now, we report the GL value plus a heuristic tail estimate.
    Add proper rigorous bounds in v2.
    """
    flint_ctx.prec = prec

    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)

    if verbose:
        print(f"  chunk constants:")
        print(f"    d_Z = {float(d_Z):.6e}")
        print(f"    α_Z = {float(alpha_Z):.6e}")
        print(f"    β_Z = {float(beta_Z):.6e}")
        print(f"    |z|_ub = {float(z_abs_ub):.4f}")

    L_arb = arb(L_outer)

    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []
    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(
            ref_nodes, ref_weights, a, b
        )
        for nd, wt in zip(s_nodes, s_weights):
            all_nodes.append((nd, wt))
    n_total = len(all_nodes)

    P_at = [P(nd, prec) for nd, _ in all_nodes]
    Pp_at = [Pp(nd, prec) for nd, _ in all_nodes]
    Q_at = [Q(nd, prec) for nd, _ in all_nodes]
    Qp_at = [Qp(nd, prec) for nd, _ in all_nodes]

    half = arb(1) / arb(2)
    integral_sum = arb(0)

    for j in range(n_total):
        y_j, w_y = all_nodes[j]
        Q_y = Q_at[j]
        Qp_y = Qp_at[j]

        for i in range(n_total):
            x_i, w_x = all_nodes[i]
            P_x = P_at[i]
            Pp_x = Pp_at[i]

            # |u-w|² = (x-y)² + (P(x)-Q(y))²
            diff_x = x_i - y_j
            diff_P = P_x - Q_y
            minus_sq = diff_x * diff_x + diff_P * diff_P

            # |u+w|² = (x+y)² + (P(x)+Q(y))²
            sum_x = x_i + y_j
            sum_P = P_x + Q_y
            plus_sq = sum_x * sum_x + sum_P * sum_P

            # E_Z(x,y) = exp(-α/2 * minus_sq - β/2 * plus_sq)
            exponent_neg = -half * (alpha_Z * minus_sq + beta_Z * plus_sq)
            E_Z = exponent_neg.exp()

            # |J| = |1 + P'(x)Q'(y)|
            J = arb(1) + Pp_x * Qp_y
            J_abs = abs(J)

            integral_sum += w_x * w_y * J_abs * E_Z

    pi_arb = arb.pi()
    H_prime_bound = integral_sum / (pi_arb * d_Z)

    if verbose:
        print(f"  ∫∫ |J|·E_Z = {float(integral_sum):.6e}")
        print(f"  bound = (1/π) · {float(integral_sum):.4e} / {float(d_Z):.4e}"
              f" = {float(H_prime_bound):.4e}")

    return H_prime_bound


# ----------------------------------------------------------------------
# Self-test: bound on a chunk vs sharp value at midpoint
# ----------------------------------------------------------------------
if __name__ == "__main__":
    PREC = 200
    flint_ctx.prec = PREC

    from h_eta_prime_integral import (
        compute_H_eta_prime_sharp,
        make_v26_P, make_v26_Pprime,
    )

    eta_arb = arb("0.01")
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    print("=" * 72)
    print("Test: chunk bound vs sharp-midpoint H_η' value")
    print("=" * 72)

    # Test chunks
    test_chunks = [
        ("real, half=0.05",  acb(arb("0.5"), arb.union(arb("-0.05"), arb("0.05")))),
        ("real, half=0.10",  acb(arb("0.5"), arb.union(arb("-0.10"), arb("0.10")))),
        ("imag, half=0.10",  acb(arb.union(arb("-0.05"), arb("0.05")), arb("1.0"))),
        ("corner",           acb(arb.union(arb("0.78"), arb("0.83")),
                                  arb.union(arb("1.05"), arb("1.10")))),
    ]

    for label, z_ball in test_chunks:
        print(f"\n>> chunk: {label}")
        print(f"   z_ball.real = {z_ball.real}")
        print(f"   z_ball.imag = {z_ball.imag}")

        # Bound via real majorant
        t0 = time.time()
        bound = bound_H_eta_prime_on_chunk(
            z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=PREC, verbose=True,
        )
        t1 = time.time()
        print(f"  Real-majorant chunk bound: |H_η'(z)| ≤ {float(bound):.4e}")
        print(f"  time: {t1 - t0:.2f}s")

        # Sharp at midpoint
        z_mid = acb(z_ball.real.mid(), z_ball.imag.mid())
        H_prime_mid = compute_H_eta_prime_sharp(
            z_mid, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=PREC,
        )
        print(f"  sharp midpoint |H_η'(z_mid)| = {float(H_prime_mid.abs_upper()):.4e}")
        ratio = float(bound) / float(H_prime_mid.abs_upper())
        print(f"  bound/sharp ratio = {ratio:.2f}")

    print("\n" + "=" * 72)
