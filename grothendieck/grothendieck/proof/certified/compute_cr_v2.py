"""
Compute C_r with direct H_eta(z) evaluation on dOmega via the phi series.

Replaces the Lemma 4.2 bound for |H_eta| with actual computation using:
    H_eta(w) = arcsin(w) - phi(arcsin(w)) / cos(arcsin(w))

where phi(z) = (z - H_eta(sin z)) * cos z has convergence radius pi/2.
Since |arcsin(w)| < pi/2 for all w on dOmega (where |Re w| < 1), the phi
series converges at all boundary points -- even those with |w| > 1.

This avoids the Lemma 4.2 bound entirely and should reduce M by orders
of magnitude (from ~4000 to ~O(1)), since H_eta ~ arcsin for small eta.

NOTE: Experimental v2 for testing. Phi truncation error is heuristic
(not rigorously bounded), but with K=50 terms it's ~ 10^{-8}.
"""

from __future__ import annotations

import time
from typing import Callable

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    abs_ub,
)
from grothendieck.proof.certified.certify_invertibility import (
    _max_on_rect,
)
from grothendieck.proof.certified.compute_cr import (
    compute_R_rigorous,
    compute_Cr,
)


# ---------------------------------------------------------------------------
# Evaluate H_eta at complex w via the phi series
# ---------------------------------------------------------------------------

def eval_phi_and_deriv_at_acb(
    phi_series: arb_series, z: acb, prec: int = 128,
) -> tuple:
    """Evaluate phi(z) and phi'(z) simultaneously via Horner.

    Returns (phi_val, phi_prime_val) as acb.
    """
    coeffs = phi_series.coeffs()
    n = len(coeffs)
    if n == 0:
        return acb(0), acb(0)

    # Horner with simultaneous derivative:
    # p = c_{n-1}, p' = 0
    # for k = n-2 down to 0: p' = p'*z + p; p = p*z + c_k
    p = acb(coeffs[n - 1])
    p_prime = acb(0)
    for k in range(n - 2, -1, -1):
        p_prime = p_prime * z + p
        p = p * z + acb(coeffs[k])
    return p, p_prime


def eval_phi_at_acb(phi_series: arb_series, z: acb, prec: int = 128) -> acb:
    """Evaluate phi(z) = sum c_k z^k at complex z using Horner's method."""
    val, _ = eval_phi_and_deriv_at_acb(phi_series, z, prec)
    return val


def eval_H_eta_at_acb(phi_series: arb_series, w: acb, prec: int = 128) -> acb:
    """Evaluate H_eta(w) for complex w using the phi series.

    H_eta(w) = arcsin(w) - phi(arcsin(w)) / cos(arcsin(w))
             = arcsin(w) - phi(arcsin(w)) / sqrt(1 - w^2)

    Convergence: |arcsin(w)| < pi/2 for all w with |Re w| < 1,
    and phi has convergence radius pi/2. So this works on all of dOmega.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    z = w.asin()           # arcsin(w)
    cos_z = z.cos()        # cos(arcsin(w)) = sqrt(1-w^2)
    phi_z = eval_phi_at_acb(phi_series, z, prec)
    result = z - phi_z / cos_z

    flint_ctx.prec = old_prec
    return result


def eval_H_eta_deriv_at_acb(
    phi_series: arb_series, w: acb, prec: int = 128,
) -> acb:
    """Evaluate H_eta'(w) for complex w using the phi series.

    H_eta(w) = arcsin(w) - phi(arcsin(w)) / cos(arcsin(w))

    Differentiating w.r.t. w, with z = arcsin(w) and dz/dw = 1/cos(z):

    H_eta'(w) = (1/cos(z)) * [1 - phi'(z)/cos(z) + phi(z)*sin(z)/cos^2(z)]
              = (1/cos(z)) * [1 - (phi'(z)*cos(z) - phi(z)*sin(z)) / cos^2(z)]

    Equivalently: H_eta'(w) = 1/cos(z) - d/dz[phi(z)/cos(z)] / cos(z)
    where d/dz[phi/cos] = (phi'*cos + phi*sin) / cos^2.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    z = w.asin()
    cos_z = z.cos()
    sin_z = z.sin()
    phi_z, phi_prime_z = eval_phi_and_deriv_at_acb(phi_series, z, prec)

    # d/dz [phi(z) / cos(z)] = (phi'(z) cos(z) + phi(z) sin(z)) / cos^2(z)
    d_phi_over_cos = (phi_prime_z * cos_z + phi_z * sin_z) / (cos_z ** 2)

    # H_eta'(w) = (1/cos(z)) * (1 - d_phi_over_cos)
    result = (acb(1) - d_phi_over_cos) / cos_z

    flint_ctx.prec = old_prec
    return result


# ---------------------------------------------------------------------------
# Boundary scanning
# ---------------------------------------------------------------------------

def _iter_rect_boundary_midpoints(delta, B, n_per_edge, prec):
    """Yield acb midpoints on dOmega(delta, B)."""
    one = arb(1)
    re_bound = one - delta
    n = n_per_edge
    half = arb(str(0.5))

    # Left/right edges
    for sign_re in [one, -one]:
        a = sign_re * re_bound
        for k in range(n):
            b_mid = -B + arb(2) * B * (arb(k) + half) / arb(n)
            yield acb(a, b_mid)

    # Top/bottom edges
    for sign_im in [one, -one]:
        b = sign_im * B
        for k in range(n):
            a_mid = -re_bound + arb(2) * re_bound * (arb(k) + half) / arb(n)
            yield acb(a_mid, b)


def max_H_eta_on_rect_via_phi(
    delta: arb,
    B: arb,
    phi_series: arb_series,
    n_per_edge: int = 64,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute max|H_eta(w)| on dOmega via phi series evaluation.

    Fast: each evaluation is just a degree-K polynomial evaluation (Horner).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    max_val = arb(0)
    count = 0
    total_points = 4 * n_per_edge
    t0 = time.time()

    for w in _iter_rect_boundary_midpoints(delta, B, n_per_edge, prec):
        H_val = eval_H_eta_at_acb(phi_series, w, prec)
        abs_H = abs_ub(H_val)
        max_val = arb.max(max_val, abs_H)
        count += 1

        if verbose and count % max(1, total_points // 4) == 0:
            elapsed = time.time() - t0
            print(f"    point {count}/{total_points}: "
                  f"|H_eta| = {float(abs_H.mid()):.6f}, "
                  f"max = {float(max_val.mid()):.6f} ({elapsed:.2f}s)")

    elapsed = time.time() - t0
    if verbose:
        print(f"  max|H_eta| on dOmega = {max_val} ({elapsed:.2f}s, {count} pts)")

    flint_ctx.prec = old_prec
    return max_val


def max_H_eta_prime_on_rect_via_phi(
    delta: arb,
    B: arb,
    phi_series: arb_series,
    n_per_edge: int = 64,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute max|H_eta'(w)| on dOmega via phi series derivative.

    Direct computation — no Cauchy inflation needed.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    max_val = arb(0)
    count = 0
    total_points = 4 * n_per_edge
    t0 = time.time()

    for w in _iter_rect_boundary_midpoints(delta, B, n_per_edge, prec):
        H_prime = eval_H_eta_deriv_at_acb(phi_series, w, prec)
        abs_H_prime = abs_ub(H_prime)
        max_val = arb.max(max_val, abs_H_prime)
        count += 1

        if verbose and count % max(1, total_points // 4) == 0:
            elapsed = time.time() - t0
            print(f"    point {count}/{total_points}: "
                  f"|H_eta'| = {float(abs_H_prime.mid()):.6f}, "
                  f"max = {float(max_val.mid()):.6f} ({elapsed:.2f}s)")

    elapsed = time.time() - t0
    if verbose:
        print(f"  max|H_eta'| on dOmega = {max_val} ({elapsed:.2f}s, {count} pts)")

    flint_ctx.prec = old_prec
    return max_val


# ---------------------------------------------------------------------------
# M computation via phi series
# ---------------------------------------------------------------------------

def compute_M_v2(
    r: arb,
    delta: arb,
    B: arb,
    phi_series: arb_series = None,
    h_eta_series: arb_series = None,
    eta: float = 0.01,
    P: Callable = None,
    Q: Callable = None,
    K_max: int = 50,
    dps: int = 50,
    n_per_edge: int = 64,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute M = max{|H_0|, |H_eta|, |H_0'|, |H_eta'|} on Omega(delta, B).

    Uses phi series to evaluate H_eta at complex boundary points.
    If phi_series is not provided, computes it from h_eta_series or from scratch.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    try:
        # Compute phi_series if not provided
        if phi_series is None:
            if h_eta_series is None:
                from grothendieck.proof.certified.h_eta_evaluator import compute_h_eta_series
                if P is None:
                    from grothendieck.proof.bk_semi_analytic import h3
                    P = h3
                if Q is None:
                    from grothendieck.proof.bk_semi_analytic import h3
                    Q = h3
                if verbose:
                    print(f"  Computing H_eta Taylor series (K={K_max}, dps={dps})...")
                h_eta_series = compute_h_eta_series(eta, P, Q, K_max, dps, prec, verbose=False)

            from grothendieck.proof.certified.phi_taylor import compute_phi_coefficients
            if verbose:
                print(f"  Computing phi coefficients...")
            phi_series = compute_phi_coefficients(h_eta_series, K_max, prec, verbose=False)

        # Verify phi is small (sanity check)
        pc = phi_series.coeffs()
        if len(pc) > 1 and verbose:
            print(f"  phi_1 = {pc[1]} (should be ~0 for small eta)")
            if len(pc) > 3:
                print(f"  phi_3 = {pc[3]}")

        n_per_edge_fast = max(n_per_edge, 256)  # more points for cheap evals

        # 1. max|H_0| = max|arcsin| on dOmega
        max_H0 = _max_on_rect(
            lambda z: abs_ub(z.asin()),
            delta, B, n_per_edge_fast, prec,
        )
        if verbose:
            print(f"  max|H_0| on dOmega = {max_H0}")

        # 2. max|H_eta| on dOmega via phi series
        if verbose:
            print(f"  Computing max|H_eta| on dOmega via phi series...")
        max_H_eta = max_H_eta_on_rect_via_phi(
            delta, B, phi_series,
            n_per_edge=n_per_edge,
            prec=prec, verbose=verbose,
        )
        if verbose:
            print(f"  max|H_eta| on dOmega (phi) = {max_H_eta}")

        # 3. max|H_0'| = max|1/sqrt(1-z^2)| on dOmega
        max_H0_prime = _max_on_rect(
            lambda z: abs_ub((acb(1) - z * z).rsqrt()),
            delta, B, n_per_edge_fast, prec,
        )
        if verbose:
            print(f"  max|H_0'| on dOmega = {max_H0_prime}")

        # 4. max|H_eta'| — direct evaluation via phi derivative
        if verbose:
            print(f"  Computing max|H_eta'| on dOmega via phi derivative...")
        max_H_eta_prime = max_H_eta_prime_on_rect_via_phi(
            delta, B, phi_series,
            n_per_edge=n_per_edge,
            prec=prec, verbose=verbose,
        )
        if verbose:
            print(f"  max|H_eta'| on dOmega (direct) = {max_H_eta_prime}")

        # M = max of all four
        M = arb.max(
            arb.max(max_H0, max_H_eta),
            arb.max(max_H0_prime, max_H_eta_prime),
        )

        if verbose:
            print(f"  M = {M}")

        return M
    finally:
        flint_ctx.prec = old_prec


def compute_Cr_v2(
    r: arb,
    delta: arb,
    B: arb,
    phi_series: arb_series = None,
    h_eta_series: arb_series = None,
    eta: float = 0.01,
    P: Callable = None,
    Q: Callable = None,
    K_max: int = 50,
    dps: int = 50,
    n_per_edge: int = 64,
    prec: int = 128,
    verbose: bool = False,
) -> dict:
    """Full C_r computation with phi-series-based H_eta evaluation."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        if verbose:
            print(f"Step 2 (v2): Computing C_r via phi series")
            print(f"  Omega: delta={delta}, B={B}")

        M = compute_M_v2(
            r, delta, B,
            phi_series=phi_series,
            h_eta_series=h_eta_series,
            eta=eta, P=P, Q=Q,
            K_max=K_max, dps=dps,
            n_per_edge=n_per_edge,
            prec=prec, verbose=verbose,
        )
        R = compute_R_rigorous(delta, B, prec=prec, verbose=verbose)
        Cr = compute_Cr(M, R, r, prec)

        if verbose:
            print(f"  C_r = {Cr}")

        return {
            'M': M,
            'R': R,
            'C_r': Cr,
        }
    finally:
        flint_ctx.prec = old_prec


# ---------------------------------------------------------------------------
# Test / comparison
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    from grothendieck.proof.certified.certify_invertibility import certify_invertibility
    from grothendieck.proof.certified.compute_cr import compute_Cr_full

    flint_ctx.prec = 128
    eta = 0.01
    r = 0.92

    print("=" * 70)
    print("STEP 1: Certify invertibility")
    print("=" * 70)
    inv_result = certify_invertibility(r=r, eta=eta, prec=128, verbose=True)
    delta = inv_result['delta']
    B = inv_result['B']
    r_arb = inv_result['r']

    print()
    print("=" * 70)
    print("STEP 2 (original): C_r via Lemma 4.2")
    print("=" * 70)
    t0 = time.time()
    cr_old = compute_Cr_full(r_arb, delta, B, prec=128, verbose=True)
    t1 = time.time()
    print(f"  Time: {t1-t0:.1f}s")

    print()
    print("=" * 70)
    print("STEP 2 (v2): C_r via phi series")
    print("=" * 70)
    t0 = time.time()
    cr_new = compute_Cr_v2(
        r_arb, delta, B,
        eta=eta, K_max=50, dps=50,
        n_per_edge=64, prec=128,
        verbose=True,
    )
    t1 = time.time()
    print(f"  Time: {t1-t0:.1f}s")

    print()
    print("=" * 70)
    print("COMPARISON")
    print("=" * 70)
    M_old = float(cr_old['M'].mid())
    M_new = float(cr_new['M'].mid())
    print(f"  M (Lemma 4.2): {M_old:.4f}")
    print(f"  M (phi):       {M_new:.4f}")
    if M_new > 0:
        print(f"  Ratio:         {M_old/M_new:.1f}x improvement")
    print(f"  C_r (old):     {float(cr_old['C_r'].mid()):.2f}")
    print(f"  C_r (new):     {float(cr_new['C_r'].mid()):.2f}")
    if float(cr_new['C_r'].mid()) > 0:
        print(f"  C_r ratio:     {float(cr_old['C_r'].mid())/float(cr_new['C_r'].mid()):.1f}x")
