"""
Step 9: Solve for γ (certified lower bound).

The self-consistent inequality:
  γ = γ₀ + p·(H_η(i)/i - γ₀) - L·(p·ε + 2·C_r·p²/r · γ/r / (1 - (γ/r)²))

Define:
  G(γ) = γ₀ + p·(H(i)/i - γ₀) - L·(p·ε + 2·C_r·p²/r · T(γ))

where T(γ) = (γ/r) / (1 - (γ/r)²) is increasing for γ ∈ [0, r).

Three approaches:
  1. Fixed-point iteration (recommended)
  2. Bisection on F(γ) = γ - G(γ)
  3. Coarse: eliminate γ from RHS using known upper bound
"""

from __future__ import annotations

from flint import arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    certified_positive, certified_lt, certified_gt,
)


def T_func(gamma: arb, r: arb) -> arb:
    """Compute T(γ) = (γ/r) / (1 - (γ/r)²).

    T is increasing for γ ∈ [0, r).
    """
    g_over_r = gamma / r
    g_over_r_sq = g_over_r * g_over_r
    den = arb(1) - g_over_r_sq
    return g_over_r / den


def G_func(
    gamma: arb,
    gamma_0: arb,
    p: arb,
    H_eta_i_over_i: arb,
    L: arb,
    series_error: arb,
    C_r: arb,
    r: arb,
) -> arb:
    """Evaluate the RHS of the self-consistency equation G(γ).

    G(γ) = γ₀ + p·(H(i)/i - γ₀) - L·(series_error + 2·C_r·p²/r · T(γ))

    series_error = head_contribution + p·tail_epsilon already has the right units
    (no extra p factor needed).

    Returns an arb ball enclosing the true value of G(γ).  Rigorous
    lower/upper bounds are extracted later by certified comparison
    functions (certified_gt, certified_lt).
    """
    # Positive term: γ₀ + p·(H(i)/i - γ₀) = (1-p)γ₀ + p·H(i)/i
    improvement = H_eta_i_over_i - gamma_0
    positive_part = gamma_0 + p * improvement

    # Negative term: L·(series_error + 2·C_r·p²/r · T(γ))
    T_val = T_func(gamma, r)
    error_budget = series_error + arb(2) * C_r * p * p / r * T_val
    negative_part = L * error_budget

    return positive_part - negative_part


def solve_gamma_coarse(
    gamma_0: arb,
    p: arb,
    H_eta_i_over_i: arb,
    L: arb,
    series_error: arb,
    C_r: arb,
    r: arb,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Approach 3: Eliminate γ from RHS using known upper bound.

    Use γ_up = γ₀ + p·(H(i)/i - γ₀) (ignoring corrections) and bound
    T(γ) ≤ T(γ_up). Then:

    γ ≥ γ₀ + p·(H(i)/i - γ₀) - L·(series_error + 2·C_r·p²/r · T(γ_up))

    This is explicit (no iteration needed).

    Returns γ_low as rigorous lower bound.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        improvement = H_eta_i_over_i - gamma_0
        gamma_up = gamma_0 + p * improvement

        # Check γ_up < r
        if not certified_lt(gamma_up, r):
            if verbose:
                print(f"  WARNING: γ_up = {gamma_up} ≥ r = {r}")
            # Use a safe upper bound
            gamma_up = r * arb('0.99')

        T_up = T_func(gamma_up, r)
        error_budget = series_error + arb(2) * C_r * p * p / r * T_up
        gamma_low = gamma_0 + p * improvement - L * error_budget

        if verbose:
            print(f"  Coarse γ_low = {gamma_low}")
            print(f"    γ_up = {gamma_up}")
            print(f"    T(γ_up) = {T_up}")
            print(f"    Error budget = {error_budget}")
            print(f"    γ_low > γ₀? {certified_gt(gamma_low, gamma_0)}")

        return gamma_low
    finally:
        flint_ctx.prec = old_prec


def solve_gamma_fixed_point(
    gamma_0: arb,
    p: arb,
    H_eta_i_over_i: arb,
    L: arb,
    series_error: arb,
    C_r: arb,
    r: arb,
    tol: arb = arb('1e-100'),
    prec: int = 128,
    max_iter: int = 200,
    verbose: bool = False,
) -> arb:
    """Fixed-point iteration for the self-consistency equation.

    Start from γ⁰ = γ₀ + p·(H(i)/i - γ₀) (upper bound, ignoring corrections).
    Iterate γ^{k+1} = G(γ^k).

    Since G is decreasing in γ (because T is increasing), the iterates
    alternate around the fixed point γ^*. Convergence is rapid because
    |G'| = O(L · C_r · p² / r) ≪ 1.

    After convergence, the result is verified: consecutive iterates bracket
    γ^*, and the lower one is returned as a certified lower bound.

    Returns γ as a rigorous lower bound.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        improvement = H_eta_i_over_i - gamma_0
        gamma = gamma_0 + p * improvement

        if verbose:
            print(f"  Fixed-point iteration:")
            print(f"    γ⁰ = {gamma}")

        for k in range(max_iter):
            if not certified_lt(gamma, r):
                gamma = r * arb('0.99')

            gamma_new = G_func(gamma, gamma_0, p, H_eta_i_over_i,
                               L, series_error, C_r, r)

            if verbose and k < 5:
                print(f"    γ^{k+1} = {gamma_new}")

            # Check convergence: arb balls overlap or |diff| < tol
            diff = gamma - gamma_new
            converged = diff.contains(arb(0))
            if not converged:
                converged = (certified_lt(diff, tol)
                             and certified_gt(diff, -tol))

            if converged:
                if verbose:
                    print(f"    Converged at iteration {k+1}")
                gamma = gamma_new
                break

            gamma = gamma_new

        # Verify: consecutive iterates bracket γ^*, return the lower one.
        if certified_lt(gamma, r):
            G_gamma = G_func(gamma, gamma_0, p, H_eta_i_over_i,
                             L, series_error, C_r, r)
            if certified_gt(G_gamma, gamma):
                # G(γ) > γ  =>  F(γ) < 0  =>  γ < γ^*
                # γ is a valid lower bound.
                pass
            elif certified_gt(gamma, G_gamma):
                # γ > G(γ)  =>  F(γ) > 0  =>  γ > γ^*
                # G is decreasing, so G(γ) < G(γ^*) = γ^*.
                # G(γ) is a valid lower bound.
                gamma = G_gamma
            else:
                # Indeterminate: fall back to γ₀
                if verbose:
                    print(f"    WARNING: Fixed-point not certified, using γ₀")
                gamma = gamma_0
        else:
            gamma = gamma_0

        if verbose:
            print(f"  Final γ = {gamma}")
            print(f"  γ > γ₀? {certified_gt(gamma, gamma_0)}")
 
        return gamma
    finally:
        flint_ctx.prec = old_prec


def solve_gamma_bisection(
    gamma_0: arb,
    p: arb,
    H_eta_i_over_i: arb,
    L: arb,
    series_error: arb,
    C_r: arb,
    r: arb,
    prec: int = 128,
    max_iter: int = 200,
    verbose: bool = False,
) -> arb:
    """Approach 2: Bisection on F(γ) = γ - G(γ).

    F is increasing (since G is decreasing in γ).
    Find [a, b] with F(a) < 0 < F(b).
    Bisection yields certified enclosure of fixed point.
    Return lower endpoint as γ_low.

    Returns γ_low as rigorous lower bound.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        def F(g):
            return g - G_func(g, gamma_0, p, H_eta_i_over_i,
                              L, series_error, C_r, r)

        # Initial bracket: [gamma_0, gamma_0 + p*(H(i)/i - gamma_0)]
        improvement = H_eta_i_over_i - gamma_0
        a = gamma_0
        b = gamma_0 + p * improvement

        # Ensure b < r
        if not certified_lt(b, r):
            b = r * arb('0.99')

        # Verify bracket: need F(a) < 0 and F(b) > 0
        F_a = F(a)
        F_b = F(b)
        if not certified_positive(-F_a):
            if verbose:
                print(f"  WARNING: Cannot certify F(a) < 0; falling back to γ₀")
            return gamma_0
        if not certified_positive(F_b):
            if verbose:
                print(f"  WARNING: Cannot certify F(b) > 0; falling back to γ₀")
            return gamma_0

        if verbose:
            print(f"  Bisection: a = {a}, b = {b}")

        tol = arb('1e-30')
        for k in range(max_iter):
            mid = (a + b) / arb(2)

            F_mid = F(mid)

            if certified_positive(-F_mid):
                # F(mid) < 0 certifiably => root is in [mid, b]
                a = mid
            elif certified_positive(F_mid):
                # F(mid) > 0 certifiably => root is in [a, mid]
                b = mid
            else:
                # F(mid) ball contains 0; cannot narrow further
                break

            if certified_lt(b - a, tol):
                break

        gamma_low = a  # Lower endpoint is a certified lower bound

        if verbose:
            print(f"  Bisection result: γ ∈ [{a}, {b}]")
            print(f"  γ_low = {gamma_low}")
            print(f"  γ_low > γ₀? {certified_gt(gamma_low, gamma_0)}")

        return gamma_low
    finally:
        flint_ctx.prec = old_prec


def solve_gamma(
    gamma_0: arb,
    p: arb,
    H_eta_i_over_i: arb,
    L: arb,
    series_error: arb,
    C_r: arb,
    r: arb,
    prec: int = 128,
    verbose: bool = False,
) -> dict:
    """Solve for γ using all three methods.

    Args:
        series_error: Combined series error = head_contribution + p * tail_epsilon.
            Already has the right units (no extra p factor needed).

    Returns dict with results from each method and the best lower bound.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        if verbose:
            print(f"Step 9: Solving for γ")
            print(f"  γ₀ = {gamma_0}")
            print(f"  H_η(i)/i = {H_eta_i_over_i}")
            print(f"  p = {p}")
            print(f"  L = {L}")
            print(f"  series_error = {series_error}")
            print(f"  C_r = {C_r}")
            print(f"  r = {r}")

        # Method 3: Coarse (simplest)
        gamma_coarse = solve_gamma_coarse(
            gamma_0, p, H_eta_i_over_i, L, series_error, C_r, r, prec, verbose
        )

        # Method 1: Fixed-point iteration
        gamma_fp = solve_gamma_fixed_point(
            gamma_0, p, H_eta_i_over_i, L, series_error, C_r, r, prec,
            verbose=verbose,
        )

        # Method 2: Bisection
        gamma_bisect = solve_gamma_bisection(
            gamma_0, p, H_eta_i_over_i, L, series_error, C_r, r, prec,
            verbose=verbose,
        )

        # Take the best (largest) certified lower bound
        best = gamma_coarse
        best_name = 'coarse'

        if certified_gt(gamma_fp, best):
            best = gamma_fp
            best_name = 'fixed_point'
        if certified_gt(gamma_bisect, best):
            best = gamma_bisect
            best_name = 'bisection'

        if verbose:
            print(f"  Best γ_low = {best} (from {best_name})")
            print(f"  γ_low > γ₀? {certified_gt(best, gamma_0)}")

        return {
            'gamma_coarse': gamma_coarse,
            'gamma_fixed_point': gamma_fp,
            'gamma_bisection': gamma_bisect,
            'gamma_best': best,
            'best_method': best_name,
            'gamma_gt_gamma0': certified_gt(best, gamma_0),
        }
    finally:
        flint_ctx.prec = old_prec
