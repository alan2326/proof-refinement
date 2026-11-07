"""
Step 4: Compute the head contribution from terms failing the crossing condition.

Instead of stopping at the first k where p*|c_{2k+1}| >= 1/(2k+1)!,
we scan all k = 0..n, allow failures, and explicitly bound their contribution:

  contribution(k) = 2 * (p * |c_{2k+1}|_ub - 1/(2k+1)!) * gamma_0^{2k+1}

Passing terms contribute 0. The sum of failing contributions is the head error.
"""

from __future__ import annotations

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import certified_lt


def compute_head_contribution(
    p: arb,
    phi_series: arb_series,
    n: int = 124,
    prec: int = 128,
    verbose: bool = False,
) -> dict:
    """Compute explicit head contribution from terms failing the crossing condition.

    Instead of stopping at the first k where p*|c_{2k+1}| >= 1/(2k+1)!,
    we scan all k = 0..n, allow failures, and explicitly bound their contribution:

      contribution(k) = 2 * (p * |c_{2k+1}|_ub - 1/(2k+1)!) * gamma_0^{2k+1}

    Passing terms contribute 0. The sum of failing contributions is the head error.

    Args:
        p: Perturbation parameter (arb).
        phi_series: Taylor series of phi(z) as arb_series.
        n: Number of odd-indexed terms to scan (k=0..n, odd indices 1..2n+1).
        prec: Precision in bits.
        verbose: Print progress.

    Returns:
        Dict with 'head_contribution', 'n', 'num_passing', 'num_failing', 'failing_ks'.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    phi_coeffs = phi_series.coeffs()

    # gamma_0 = atanh(1/sqrt(2))
    gamma_0 = (arb(1) / arb(2).sqrt()).atanh()

    num_passing = 0
    num_failing = 0
    failing_ks = []
    head_contribution = arb(0)

    # Precompute gamma_0 powers: gamma_0^1, gamma_0^3, gamma_0^5, ...
    gamma_pow = gamma_0  # gamma_0^1

    if verbose:
        print(f"Step 4: Computing head contribution (relaxed crossing, n={n})")
        print(f"  p = {p}")
        print(f"  gamma_0 = {gamma_0}")

    for k in range(n + 1):
        idx = 2 * k + 1

        if idx >= len(phi_coeffs):
            if verbose:
                print(f"  Reached end of phi series at k={k} (idx={idx})")
            break

        c = phi_coeffs[idx]

        # |c_{2k+1}| upper bound via rigorous ball arithmetic
        c_abs_ub = acb(c).abs_upper()

        # p * |c_{2k+1}|
        lhs = p * c_abs_ub

        # 1/(2k+1)!
        rhs = arb(1) / arb.fac_ui(idx)

        if certified_lt(lhs, rhs):
            num_passing += 1
        else:
            num_failing += 1
            failing_ks.append(k)
            # contribution = 2 * (p * |c_{2k+1}|_ub - 1/(2k+1)!) * gamma_0^{2k+1}
            contrib = arb(2) * (lhs - rhs) * gamma_pow
            head_contribution = head_contribution + contrib

            if verbose and num_failing <= 10:
                print(f"  k={k} (idx={idx}): FAIL, contrib = {contrib}")

        # Update gamma_pow: gamma_0^{2k+1} -> gamma_0^{2(k+1)+1} = gamma_0^{2k+3}
        gamma_pow = gamma_pow * gamma_0 * gamma_0

    if verbose:
        print(f"  Passing: {num_passing}, Failing: {num_failing}")
        print(f"  Head contribution = {head_contribution}")

    flint_ctx.prec = old_prec
    return {
        'head_contribution': head_contribution,
        'n': n,
        'num_passing': num_passing,
        'num_failing': num_failing,
        'failing_ks': failing_ks,
    }
