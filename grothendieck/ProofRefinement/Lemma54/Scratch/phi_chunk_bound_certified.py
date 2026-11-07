"""Fully certified (closed-form arb) chunk bound on sup_{z ∈ Z} |Φ(z)|.

Avoids the need for sharp H_mid evaluation by bounding the kernel difference
K_z(P, Q) - K_z(0, 0) directly via polynomial bounds + Gaussian moment closed
forms. Result: pure arb arithmetic, no quadrature, no GL/tail error.

Math:

    Φ(z) = H_η(z) − arcsin(z) = (1/(2σ)) · ∫∫ [K_z(P, Q) − K_z(0, 0)] · exp(-Q_z) dxdy

For real x, y (P = real, Q = real):

    K_z(a, b) − K_z(0, 0) = erf(a)·erf(b)
                          + (2z/π) · ∫₀¹ [exp(-N(u)) − 1] / sqrt(1 − z²u²) du

with N(u) = (a² + b² − 2ab·zu) / (1 − z²u²).

Bounds (all rigorous in arb arithmetic):

    |erf(a)·erf(b)| ≤ (4/π) · |a|·|b| ≤ (2/π) · (a² + b²)        (AM-GM after erf bound)

For z ∈ Z and u ∈ [0, 1] in our V26 chunks (Re z ∈ (-1, 1)),
    Re N(u) = (a-b)²/2 · Re(1/(1-zu)) + (a+b)²/2 · Re(1/(1+zu)) ≥ 0
so |exp(-N(u)) − 1| ≤ |N(u)| (rigorous for Re N ≥ 0).

    |N(u)| ≤ (a² + b² + 2|ab|·|z|·u) / |1 − z²u²|
          ≤ (a² + b² + 2|ab|·|z|·u) / d_min(Z)

where d_min(Z) := inf_{z ∈ Z, u ∈ [0,1]} |1 − z²u²|, computed as an arb lower
bound by interval-evaluating 1 − z²·u² with z = chunk-acb-ball, u² = arb([0,1]).

    ∫₀¹ |N(u)| du ≤ (a² + b² + |ab|·|z|) / d_min(Z)
                  ≤ (a² + b²) · (1 + |z|/2) / d_min(Z)        (AM-GM on |ab|)

    ∫₀¹ |N(u)| / |sqrt(1 − z²u²)| du ≤ (a² + b²)·(1 + |z|/2) / d_min(Z)^{3/2}

Combined:

    |K_z(a, b) − K_z(0, 0)| ≤ C_K_diff(Z) · (a² + b²)

with

    C_K_diff(Z) := (2/π) + |z|_ub · (2 + |z|_ub) / (π · d_min(Z)^{3/2})

(The factor (1+|z|/2) was rewritten as (2 + |z|)/2; combined with the 2|z|/π outer
factor we get |z|·(2+|z|)/π.)

Now (using V26 convention Q = -P, so Q² = P²):

    |Φ(z)| ≤ (1/(2|σ|_Z_lower)) · ∫∫ |K_z(P,Q) − K_z(0,0)| · exp(-Q_z) dxdy
          ≤ (C_K_diff(Z) / (2 sqrt(d_Z))) · ∫∫ (P²(x) + Q²(y)) · E_Z dxdy
          = (C_K_diff(Z) / sqrt(d_Z)) · K₁ · ∫_R P²(x) · exp(-σ·x²) dx

with K₁ = sqrt(2π/(α+β)), σ = 2αβ/(α+β) as in the marginal Gaussian identity.

For V26 P(x) = K_P · (4x³ − 3x), K_P = η/(√3·π^{1/4}):

    ∫_R P²(x)·exp(-σ·x²) dx = K_P² · (9·M(1;σ) − 24·M(2;σ) + 16·M(3;σ))

Final:

    sup_{z ∈ Z} |Φ(z)| ≤ (C_K_diff(Z) · K₁ · K_P² / sqrt(d_Z)) · (9·M₁ − 24·M₂ + 16·M₃)

This is a strict arb upper bound; no GL/tail/quadrature error.

LOOSENESS: The bound uses AM-GM on |ab| → (a²+b²)/2 (factor 2 max),
and bounds |sqrt(1-z²u²)|^{-1} by d_min^{-1/2} (loose at chunks where the
worst-u and worst-z are at different (u, z) configurations). Empirically
~3-5× looser than the mean-value enclosure with sharp H_mid.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import NamedTuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
from gaussian_tail_bounds import M_full


def _chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    from chunk_constants_safe import safe_chunk_constants
    return safe_chunk_constants(z_ball)


def _d_min_uniform(z_ball: acb, n_subdiv: int = 16) -> arb:
    """Lower bound on inf_{u ∈ [0, 1], z ∈ Z} |1 - z²u²|.

    Subdivides u² ∈ [0, 1] into n_subdiv equal arb intervals, computes
    |1 - z²u²|.abs_lower() on each (with z = full chunk-ball), takes the
    min over subintervals.
    """
    z2 = z_ball * z_ball
    d_min = None
    for k in range(n_subdiv):
        u2_lo = arb(k) / arb(n_subdiv)
        u2_hi = arb(k + 1) / arb(n_subdiv)
        u2_interval = arb.union(u2_lo, u2_hi)
        one_minus = acb(1) - z2 * u2_interval
        d_k = one_minus.abs_lower()
        if d_min is None:
            d_min = d_k
        else:
            d_min = arb.min(d_min, d_k)
    return d_min


# ----------------------------------------------------------------------
class PhiChunkResult(NamedTuple):
    bound: arb
    d_Z: arb
    d_min: arb
    alpha_Z: arb
    beta_Z: arb
    z_abs_ub: arb
    K1: arb
    sigma: arb
    K_P: arb
    C_K_diff: arb


def bound_Phi_on_chunk_certified(
    z_ball: acb,
    eta_arb: arb,
    prec: int = 200,
    n_subdiv_u: int = 16,
) -> PhiChunkResult:
    """Closed-form arb upper bound on sup_{z ∈ Z} |Φ(z)| for V26 curves.

    Returns PhiChunkResult with bound + diagnostics.
    """
    flint_ctx.prec = prec
    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)

    if not (alpha_Z > arb(0) and beta_Z > arb(0)):
        raise ValueError(f"alpha_Z={alpha_Z}, beta_Z={beta_Z} must be positive")

    # d_min(Z) = inf over (z, u) of |1 - z²u²|
    d_min = _d_min_uniform(z_ball, n_subdiv=n_subdiv_u)
    if not (d_min > arb(0)):
        raise ValueError(f"d_min(Z) not positive: {d_min}")

    # K_P, K1, σ
    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P2 = K_P * K_P
    sum_ab = alpha_Z + beta_Z
    sigma = arb(2) * alpha_Z * beta_Z / sum_ab
    K1 = (arb(2) * arb.pi() / sum_ab).sqrt()

    # Gaussian moments
    sqrt_pi_over_sigma = (arb.pi() / sigma).sqrt()
    M1 = sqrt_pi_over_sigma / (arb(2) * sigma)
    M2 = arb(3) * sqrt_pi_over_sigma / (arb(2) * sigma)**2
    M3 = arb(15) * sqrt_pi_over_sigma / (arb(2) * sigma)**3

    # P² polynomial moment integral
    P2_moment = K_P2 * (arb(9) * M1 - arb(24) * M2 + arb(16) * M3)

    # C_K_diff(Z) = (2/π) + |z|_ub · (2 + |z|_ub) / (π · d_min^{3/2})
    pi_arb = arb.pi()
    d_min_3half = d_min * d_min.sqrt()
    C_K_diff = arb(2) / pi_arb + z_abs_ub * (arb(2) + z_abs_ub) / (pi_arb * d_min_3half)

    # |Φ| bound = (C_K_diff · K1 / sqrt(d_Z)) · P2_moment
    bound = (C_K_diff * K1 / d_Z.sqrt()) * P2_moment

    return PhiChunkResult(
        bound=bound, d_Z=d_Z, d_min=d_min, alpha_Z=alpha_Z, beta_Z=beta_Z,
        z_abs_ub=z_abs_ub, K1=K1, sigma=sigma, K_P=K_P, C_K_diff=C_K_diff,
    )


# ----------------------------------------------------------------------
# Smoke tests
# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200
    eta_arb = arb("0.01")

    print("=" * 78)
    print("Φ chunk bound: closed-form (kernel-diff) certified vs mean-value")
    print("=" * 78)

    test_chunks = [
        ("real, half=0.05",  acb(arb("0.5"),  arb.union(arb("-0.05"), arb("0.05")))),
        ("interior cplx",    acb(arb.union(arb("0.35"), arb("0.45")),
                                  arb.union(arb("0.45"), arb("0.55")))),
        ("V26 corner-ish",   acb(arb("0.84"), arb.union(arb("0.97"), arb("1.115")))),
        ("V26 spike",        acb(arb("0.84"), arb.union(arb("0.14"), arb("0.28")))),
    ]

    for label, z_ball in test_chunks:
        print(f"\n>> {label}")
        r = bound_Phi_on_chunk_certified(z_ball, eta_arb, prec=200)
        print(f"   d_Z={float(r.d_Z):.4e}, d_min={float(r.d_min):.4e}, "
              f"|z|_ub={float(r.z_abs_ub):.4f}")
        print(f"   C_K_diff = {float(r.C_K_diff):.4e}")
        print(f"   certified |Φ| bound = {r.bound.str(8)}")

    print("\n" + "=" * 78)
