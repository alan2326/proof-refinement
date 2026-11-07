"""H_η'(z) via Price's-theorem derivative formula — no inner K_z integral.

Per the LLM analysis (chat 2026-05-02):

    H_η'(z) = (1/(π·(1-z²))) · ∫∫ (1 + P'(x)Q'(y)) · exp(-S_z(x,y)) dx dy

where
    A(x,y)   = x² + P(x)² + y² + Q(y)²
    B(x,y)   = x·y + P(x)·Q(y)
    S_z(x,y) = (A − 2zB) / (1 − z²)

For P=Q=0: gives 1/√(1-z²) = arcsin'(z) ✓

Identity for chunk bounds:
    S_z(x,y) = |u-w|² / (2(1-z))  +  |u+w|² / (2(1+z))
where u = (x, P(x)), w = (y, Q(y)).
For z in the strip |Re z| < 1, Re(1/(1-z)) and Re(1/(1+z)) are both
positive. So Re S_z(x,y) ≥ (real positive quadratic in x, y).

This file: sharp-z evaluation of H_η'(z) only. Chunk bounds are a
separate file (h_eta_prime_chunk_bound.py) using the real majorant.

Convention: V26 framework uses P(x) = +η·h₃(√2·x)/√2,
            Q(y) = -η·h₃(√2·y)/√2 (variance-1 / probabilist's bridge).
"""

from __future__ import annotations

import math
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
# Curves and their derivatives, V26 convention
# ----------------------------------------------------------------------
def make_v26_P(eta_arb: arb, sign: int):
    """P(x) = sign · η · h₃(√2·x) / √2 (variance-1 bridge)."""
    s = arb(sign)
    sqrt2 = arb(2).sqrt()
    def P(x, prec=256):
        return s * eta_arb * h3_arb(sqrt2 * x, prec) / sqrt2
    return P


def make_v26_Pprime(eta_arb: arb, sign: int):
    """P'(x) = sign · η · h₃'(√2·x).

    h₃(t) = (2t³ − 3t)/(√3·π^{1/4})
    h₃'(t) = (6t² − 3)/(√3·π^{1/4})
    P(x) = sign·η·h₃(√2·x)/√2
    P'(x) = sign·η·h₃'(√2·x)·√2/√2 = sign·η·h₃'(√2·x)
    """
    s = arb(sign)
    sqrt2 = arb(2).sqrt()
    def Pprime(x, prec=256):
        t = sqrt2 * x
        pi_quarter = arb.pi().sqrt().sqrt()
        denom = arb(3).sqrt() * pi_quarter
        return s * eta_arb * (arb(6) * t * t - arb(3)) / denom
    return Pprime


# ----------------------------------------------------------------------
# Sharp-z evaluation of H_η'(z)
# ----------------------------------------------------------------------
def compute_H_eta_prime_sharp(
    z: acb,
    P: Callable, Pp: Callable,
    Q: Callable, Qp: Callable,
    L_outer: int = 8,
    n_panels: int = 8,
    n_gl: int = 20,
    prec: int = 200,
    gl_dps: int = 80,
    verbose: bool = False,
) -> acb:
    """Evaluate H_η'(z) at sharp acb z via the K_z-free 2D Gauss-Legendre.

    Returns the GL-quadrature value as an acb. NOTE: this routine does
    NOT include rigorous GL+tail error bounds — it returns the raw GL
    sum. Use compute_H_eta_prime_certified for certified bounds.
    """
    flint_ctx.prec = prec

    one_minus_z2 = acb(1) - z * z
    inv_one_minus_z2 = acb(1) / one_minus_z2
    L_arb = arb(L_outer)

    # Outer GL nodes on [-L, L]
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

    if verbose:
        print(f"  H_η'(z) sharp: {n_total}² = {n_total**2} outer GL evaluations")
        t_start = time.time()

    # Precompute P(x), P'(x), and node-dependent quantities
    P_at = [P(nd, prec) for nd, _ in all_nodes]
    Pp_at = [Pp(nd, prec) for nd, _ in all_nodes]
    Q_at = [Q(nd, prec) for nd, _ in all_nodes]
    Qp_at = [Qp(nd, prec) for nd, _ in all_nodes]

    H_sum = acb(0)
    for j in range(n_total):
        y_j, w_y = all_nodes[j]
        Q_y = Q_at[j]
        Qp_y = Qp_at[j]
        y2 = y_j * y_j
        Q2 = Q_y * Q_y

        for i in range(n_total):
            x_i, w_x = all_nodes[i]
            P_x = P_at[i]
            Pp_x = Pp_at[i]

            # A = x² + P(x)² + y² + Q(y)²
            A = x_i * x_i + P_x * P_x + y2 + Q2
            # B = xy + P(x)Q(y)
            B = x_i * y_j + P_x * Q_y
            # J = 1 + P'(x) Q'(y)
            J = arb(1) + Pp_x * Qp_y

            # S_z = (A - 2zB)/(1 - z²)
            S = (acb(A) - acb(2) * z * acb(B)) * inv_one_minus_z2

            integrand = acb(J) * (-S).exp()
            H_sum += acb(w_x * w_y) * integrand

    pi_arb = arb.pi()
    H_prime = H_sum / (acb(pi_arb) * one_minus_z2)

    if verbose:
        t_end = time.time()
        print(f"  H_η'(z) sharp: done in {t_end - t_start:.1f}s")

    flint_ctx.prec = prec
    return H_prime


# ----------------------------------------------------------------------
# Self-test: at z=0.5, η=0.01, compare against numerical differentiation
# of H_η using existing compute_H_fg_complex_certified.
# ----------------------------------------------------------------------
if __name__ == "__main__":
    PREC = 200
    flint_ctx.prec = PREC

    eta_arb = arb("0.01")
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    z = acb(arb("0.5"), arb(0))

    print("=" * 72)
    print("Sanity check: H_η'(z=0.5) via Price's-theorem formula")
    print("=" * 72)
    print(f"  η = 0.01, prec = {PREC}")
    print()

    # Compute via the K_z-free formula
    print("[1] Direct (no inner K_z):")
    t0 = time.time()
    H_prime = compute_H_eta_prime_sharp(
        z, P_plus, Pp_plus, Q_minus, Qp_minus,
        L_outer=8, n_panels=8, n_gl=20, prec=PREC, verbose=True,
    )
    t1 = time.time()
    print(f"  H_η'(0.5) = {H_prime}")
    print(f"  time: {t1 - t0:.1f}s")
    print()

    # Reference: arcsin'(0.5) = 1/√(1−0.25) = 1.1547
    arcsin_prime_ref = arb(1) / (arb(1) - arb("0.25")).sqrt()
    print(f"[2] Reference: arcsin'(0.5) = 1/√(0.75) = "
          f"{float(arcsin_prime_ref):.10f}")
    print()

    # Compare via numerical diff of H_eta:
    # H'(0.5) ≈ (H(0.5+ε) - H(0.5-ε)) / (2ε)
    # Use compute_H_fg_complex_certified for sharp H values.
    print("[3] Numerical differentiation of H_η via existing certified integrator:")
    from grothendieck.proof.certified.h_fg_rigor_complex import (
        compute_H_fg_complex_certified,
    )
    eps = arb("1e-6")
    z_plus = acb(arb("0.5") + eps, arb(0))
    z_minus = acb(arb("0.5") - eps, arb(0))

    t0 = time.time()
    res_p = compute_H_fg_complex_certified(
        z=z_plus, P_arb=P_plus, Q_arb=Q_minus,
        L_outer=8, n_panels=8, n_gl=20, prec=PREC, gl_dps=80,
    )
    res_m = compute_H_fg_complex_certified(
        z=z_minus, P_arb=P_plus, Q_arb=Q_minus,
        L_outer=8, n_panels=8, n_gl=20, prec=PREC, gl_dps=80,
    )
    H_prime_numdiff = (res_p.H_fg - res_m.H_fg) / (acb(2) * acb(eps))
    t1 = time.time()
    print(f"  H_η' (num diff) = {H_prime_numdiff}")
    print(f"  time: {t1 - t0:.1f}s")
    print()

    print("[4] Comparison")
    diff = H_prime - H_prime_numdiff
    diff_abs = float(diff.abs_upper())
    print(f"  |Direct − NumDiff| = {diff_abs:.4e}")
    if diff_abs < 1e-3:
        print("  ✓ MATCH — derivative formula is correct.")
    else:
        print("  ✗ MISMATCH — investigate.")
    print("=" * 72)
