"""Fully certified (closed-form arb) η²-tight chunk bound on sup_{z∈Z} |Φ'(z)|.

Replaces phi_prime_chunk_bound_direct.py's numerical Gauss-Legendre with
a closed-form 1D Gaussian-moment expression — fully rigorous in arb
arithmetic, no GL+tail error to worry about.

Math derivation:
  |Φ'(z)| ≤ (1/(π·d_Z)) · ∫∫ J(x,y) · E_Z(x,y) dx dy
where
  J(x,y) = |P'(x)·Q'(y)| + (P²+Q²+2|z|·|PQ|)/d_Z

Use AM-GM bounds (x↔y are real-axis integration variables, so |a·b|≤(a²+b²)/2):
  |P'·Q'| ≤ (P'²(x) + Q'²(y))/2
  |P·Q|   ≤ (P²(x)  + Q²(y) )/2

For V26 with Q = -P:  Q² = P², Q'² = P'². So:
  J(x,y) ≤ A(x) + A(y) + B(x) + B(y),
  A(x) = P'(x)²/2,   B(x) = (1+|z|_ub)·P(x)²/d_Z

Marginal: ∫_R E_Z(x,y) dy = sqrt(2π/(α+β)) · exp(-σ·x²),  σ = 2αβ/(α+β).

Hence ∫∫ A(x)·E_Z = K₁·∫_R A(x)·exp(-σ·x²) dx, and similarly for A(y), B(x), B(y).

Total ∫∫ J·E_Z ≤ 2·K₁·(I_A + I_B),
where
  K₁  = sqrt(2π/(α+β))
  I_A = ∫_R A(x)·exp(-σ·x²) dx = (K_P²/2)·(9·M(0;σ) − 72·M(1;σ) + 144·M(2;σ))
  I_B = ∫_R B(x)·exp(-σ·x²) dx = K_P²·(1+|z|)/d_Z·(9·M(1;σ) − 24·M(2;σ) + 16·M(3;σ))
  M(k;σ) = ∫_R x^{2k}·exp(-σ·x²) dx = (2k-1)!!·sqrt(π/σ)/(2σ)^k

For V26 P = sign·η·h₃(√2·x)/√2 = sign·K_P·(4x³−3x),  K_P = η/(√3·π^{1/4}).
Then  P²(x) = K_P²·(16x⁶ − 24x⁴ + 9x²),
      P'²(x) = K_P²·(144x⁴ − 72x² + 9).

Final bound:
  sup_{z∈Z} |Φ'(z)| ≤ (1/(π·d_Z)) · 2·K₁ · (I_A + I_B)

CAVEAT: the AM-GM substitution is rigorous (always an upper bound on the
absolute value), so this gives a strict arb interval upper bound. NO
GL/quadrature/tail errors anywhere; everything is closed-form arb arithmetic.

Looseness vs the original GL-based bound: AM-GM swap inflates each |a·b|
term by at most a factor 2 (when a=b, the inequality is tight). For η²
scaling, this doesn't change leading order — just a small multiplicative
constant.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import NamedTuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
from gaussian_tail_bounds import double_factorial_double, M_full


# ----------------------------------------------------------------------
def _chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    """Compute (d_Z, alpha_Z, beta_Z, |z|_ub) using safe-squaring helper
    that avoids arb-ball squaring imprecision. See chunk_constants_safe.py
    for derivation."""
    from chunk_constants_safe import safe_chunk_constants
    return safe_chunk_constants(z_ball)


# ----------------------------------------------------------------------
class PhiPrimeChunkResult(NamedTuple):
    bound: arb
    d_Z: arb
    alpha_Z: arb
    beta_Z: arb
    z_abs_ub: arb
    K1: arb
    sigma: arb
    I_A: arb
    I_B: arb
    K_P: arb


def bound_Phi_prime_on_chunk_certified(
    z_ball: acb,
    eta_arb: arb,
    prec: int = 200,
) -> PhiPrimeChunkResult:
    """Closed-form arb upper bound on sup_{z∈Z} |Φ'(z)| for V26 curves.

    Returns a PhiPrimeChunkResult with the bound + diagnostic fields.

    Note: assumes V26 convention P_plus = +η·h₃(√2·x)/√2,  Q_minus = -P_plus.
    """
    flint_ctx.prec = prec
    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)

    if not (alpha_Z > arb(0) and beta_Z > arb(0)):
        raise ValueError("alpha_Z, beta_Z must be positive on Ω(δ, B); "
                         f"got alpha_Z={alpha_Z}, beta_Z={beta_Z}")

    # K_P = η / (√3 · π^{1/4})
    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P2 = K_P * K_P

    # Marginal Gaussian decay rate σ = 2αβ/(α+β)
    sum_ab = alpha_Z + beta_Z
    sigma = arb(2) * alpha_Z * beta_Z / sum_ab
    K1 = (arb(2) * arb.pi() / sum_ab).sqrt()

    # Gaussian moments M(k; σ) = (2k-1)!! · sqrt(π/σ) / (2σ)^k
    sqrt_pi_over_sigma = (arb.pi() / sigma).sqrt()
    M0 = sqrt_pi_over_sigma                                # k=0
    M1 = sqrt_pi_over_sigma / (arb(2) * sigma)             # k=1
    M2 = arb(3) * sqrt_pi_over_sigma / (arb(2) * sigma)**2 # k=2
    M3 = arb(15) * sqrt_pi_over_sigma / (arb(2) * sigma)**3  # k=3

    # I_A = ∫ A(x)·exp(-σx²) dx,  A(x) = P'²/2 = (K_P²/2)·(9 − 72x² + 144x⁴)
    I_A = (K_P2 / arb(2)) * (
        arb(9) * M0 - arb(72) * M1 + arb(144) * M2
    )
    # I_B = ∫ B(x)·exp(-σx²) dx,  B(x) = (1+|z|)·P²/d_Z = K_P²·(1+|z|)/d_Z·(9x² − 24x⁴ + 16x⁶)
    coef_B = K_P2 * (arb(1) + z_abs_ub) / d_Z
    I_B = coef_B * (
        arb(9) * M1 - arb(24) * M2 + arb(16) * M3
    )

    # Total integrand (using x↔y symmetry):  ∫∫ J·E_Z ≤ 2·K1·(I_A + I_B)
    integral = arb(2) * K1 * (I_A + I_B)

    bound = integral / (arb.pi() * d_Z)
    return PhiPrimeChunkResult(
        bound=bound, d_Z=d_Z, alpha_Z=alpha_Z, beta_Z=beta_Z,
        z_abs_ub=z_abs_ub, K1=K1, sigma=sigma, I_A=I_A, I_B=I_B, K_P=K_P,
    )


# ----------------------------------------------------------------------
# Smoke tests
# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200
    eta_arb = arb("0.01")

    print("=" * 72)
    print("Φ' chunk bound: closed-form certified vs prior GL-based direct")
    print("=" * 72)

    test_chunks = [
        ("real, half=0.05",  acb(arb("0.5"),  arb.union(arb("-0.05"), arb("0.05")))),
        ("interior cplx",    acb(arb.union(arb("0.35"), arb("0.45")),
                                  arb.union(arb("0.45"), arb("0.55")))),
        ("V26 corner-ish",   acb(arb("0.84"), arb.union(arb("0.97"), arb("1.115")))),
        ("V26 spike",        acb(arb("0.84"), arb.union(arb("0.14"), arb("0.28")))),
    ]

    sys.path.insert(0, str(_HERE))
    from phi_prime_chunk_bound_direct import bound_Phi_prime_on_chunk_direct
    from h_eta_prime_integral import make_v26_P, make_v26_Pprime
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    for label, z_ball in test_chunks:
        print(f"\n>> {label}")
        r = bound_Phi_prime_on_chunk_certified(z_ball, eta_arb, prec=200)
        print(f"   d_Z={float(r.d_Z):.4e}, α_Z={float(r.alpha_Z):.4e}, "
              f"β_Z={float(r.beta_Z):.4e}, σ={float(r.sigma):.4e}")
        print(f"   certified bound = {r.bound.str(8)}")
        # Compare to GL-based direct bound
        gl_bound = bound_Phi_prime_on_chunk_direct(
            z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=200,
        )
        print(f"   GL-based direct = {gl_bound.str(8)}")
        ratio = r.bound / gl_bound
        print(f"   certified/GL    = {ratio.str(8)}× (looseness vs GL)")

    print("\n" + "=" * 72)
