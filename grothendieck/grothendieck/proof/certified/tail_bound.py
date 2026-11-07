"""
Step 7: Compute the tail bound ε.

ε = 2 M_ρ · (γ/ρ)^{2n+3} / (1 - (γ/ρ)²)

This bounds the contribution from Taylor coefficients beyond index n,
using Cauchy estimates + geometric series.

Since γ/ρ = 1/α < 1, the geometric series converges.
"""

from __future__ import annotations

from flint import arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import certified_positive


def compute_epsilon(
    M_rho: arb,
    gamma_over_rho: arb,
    n: int,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute the tail bound ε.

    ε = 2 M_ρ · (γ/ρ)^{2n+3} / (1 - (γ/ρ)²)

    Args:
        M_rho: Max|φ(z)| on circle |z| = ρ.
        gamma_over_rho: γ/ρ = 1/α (must be < 1).
        n: Crossing index.
        prec: Precision in bits.

    Returns:
        ε as arb upper bound.

    Raises:
        RuntimeError: If denominator not certifiably positive.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    # t = (γ/ρ)^{2n+3}
    exponent = 2 * n + 3
    t = gamma_over_rho ** exponent

    # den = 1 - (γ/ρ)²
    g_over_r_sq = gamma_over_rho * gamma_over_rho
    den = arb(1) - g_over_r_sq

    if not certified_positive(den):
        raise RuntimeError(
            f"Cannot certify 1 - (γ/ρ)² > 0: den = {den}. "
            f"Check that α > 1."
        )

    # ε = 2 · M_ρ · t / den
    epsilon = arb(2) * M_rho * t / den

    if verbose:
        print(f"Step 7: Computing tail bound ε")
        print(f"  γ/ρ = {gamma_over_rho}")
        print(f"  n = {n}")
        print(f"  (γ/ρ)^{exponent} = {t}")
        print(f"  1 - (γ/ρ)² = {den}")
        print(f"  ε = {epsilon}")

    flint_ctx.prec = old_prec
    return epsilon
