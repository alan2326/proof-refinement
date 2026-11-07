#!/usr/bin/env python3
"""
Compute the bilinear form B_K(f,g) using Hermite diagonalization.

B_K(f,g) = ∫∫ f(x)g(y) e^{-(|x|²+|y|²)/2} sin(⟨x,y⟩) dx dy
         = (2π)² E[f(X)g(Y) sin(⟨X,Y⟩)]

This repo uses ORTHONORMAL Hermite polynomials h_α(x) = He_α(x)/√(α!).
The kernel expansion for orthonormal Hermites is:

    sin(⟨x,y⟩) = Σ_{k odd} (-1)^{(k-1)/2} / √(k!) · Σ_{|α|=k} h_α(x) h_α(y)

So with coefficients f̃_α = E[f(X) h_α(X)] (orthonormal):

    S := E[f(X)g(Y) sin(⟨X,Y⟩)]
       = Σ_{k odd, k ≤ k_max} (-1)^{(k-1)/2} / √(k!) · Σ_{|α|=k} f̃_α · g̃_α

Then B_K(f,g) = (2π)² S.
"""

from __future__ import annotations
from typing import Callable
from dataclasses import dataclass, field

from mpmath import mp, pi


@dataclass
class BKResult:
    """Result from B_K computation."""
    BK: mp.mpf                          # The B_K value = (2π)² S
    S: mp.mpf                           # S = E[f(X)g(Y) sin(⟨X,Y⟩)]
    by_degree: dict = field(default_factory=dict)     # Contribution per degree k
    cumulative: dict = field(default_factory=dict)    # Cumulative sum up to degree k
    k_max: int = 0                      # Maximum degree used


def kernel_weight(k: int) -> mp.mpf:
    """
    Compute kernel weight for total degree k (orthonormal Hermite basis).

    For k even or k=0: weight = 0
    For k odd: weight = (-1)^{(k-1)/2} / √(k!)

    Args:
        k: Total degree |α| = a + b

    Returns:
        Kernel weight as mp.mpf
    """
    if k == 0 or k % 2 == 0:
        return mp.mpf('0')

    # Robust sign computation: (-1)^m where m = (k-1)/2
    m = (k - 1) // 2
    sign = 1 if (m % 2 == 0) else -1

    return mp.mpf(sign) # / mp.sqrt(mp.factorial(k))


def BK_from_hermite(
    fhat: mp.matrix,
    ghat: mp.matrix,
    k_max: int,
    dps: int = 100,
    verbose: bool = False,
) -> BKResult:
    """
    Compute B_K(f,g) from 2D Hermite coefficient matrices.

    IMPORTANT: Assumes coefficients are in ORTHONORMAL basis:
        fhat[i,j] = E[f(X,Y) h_i(X) h_j(Y)]
    where h_n = He_n/√(n!) is the orthonormal Hermite polynomial.

    Args:
        fhat: mp.matrix of shape (N+1, N+1) with fhat[i,j] = f̃_{(i,j)}
        ghat: mp.matrix of shape (N+1, N+1) with ghat[i,j] = g̃_{(i,j)}
        k_max: Maximum total degree to include
        dps: Decimal precision
        verbose: Print diagnostics

    Returns:
        BKResult with B_K value and diagnostics
    """
    mp.dps = dps

    S = mp.mpf('0')
    by_degree = {}
    cumulative = {}

    # Sum over total degrees k from 1 to k_max (odd only)
    for k in range(1, k_max + 1, 2):  # Step by 2 for odd k only
        weight_k = kernel_weight(k)

        # Sum over all multi-indices α = (a, b) with |α| = a + b = k
        coeff_sum = mp.mpf('0')
        for a in range(k + 1):
            b = k - a
            # Check bounds
            if a < fhat.rows and b < fhat.cols and a < ghat.rows and b < ghat.cols:
                coeff_sum += fhat[a, b] * ghat[a, b]

        contribution = weight_k * coeff_sum
        S += contribution

        by_degree[k] = contribution
        cumulative[k] = S

        if verbose:
            print(f"  k={k:3d}: weight={mp.nstr(weight_k, 15)}, "
                  f"Σf̃·g̃={mp.nstr(coeff_sum, 15)}, contrib={mp.nstr(contribution, 15)}, "
                  f"S_cum={mp.nstr(S, 15)}")

    BK = (2 * pi) ** 2 * S

    return BKResult(
        BK=BK,
        S=S,
        by_degree=by_degree,
        cumulative=cumulative,
        k_max=k_max
    )


def hyperplane_hermite_1d(n: int, dps: int = 100) -> mp.mpf:
    """
    Compute 1D orthonormal Hermite coefficient for f_0(x) = sign(x).

    Returns f̃_n = E[sign(X) h_n(X)] for X ~ N(0,1),
    where h_n(x) = He_n(x)/√(n!) is the orthonormal Hermite.

    For sign(x):
        f̃_n = 0  for n even
        f̃_n = √(2/π) · (n-2)!! / √(n!)  for n odd

    where (n-2)!! = 1·3·5·...·(n-2) is the double factorial.
    """
    mp.dps = dps
    if n % 2 == 0:
        return mp.mpf('0')

    double_fact = mp.mpf('1')
    k = n - 2
    while k > 0:
        double_fact *= k
        k -= 2

    m = (n - 1) // 2
    sign = 1 if (m % 2 == 0) else -1

    return mp.mpf(sign) * mp.sqrt(2 / pi) * double_fact / mp.sqrt(mp.factorial(n))


def build_hyperplane_matrix(k_max: int, dps: int = 100, verbose: bool = False) -> mp.matrix:
    """
    Build Hermite coefficient matrix for f_0(x,y) = sign(x).

    For f_0 depending only on x:
        f̃_{(a,b)} = E[sign(X) h_a(X)] · E[h_b(Y)] = f̃_a · δ_{b,0}

    Only the first column (b=0) is nonzero, and only for odd a.
    """
    mp.dps = dps

    N = k_max + 1
    fhat = mp.matrix(N, N)

    for a in range(N):
        if a % 2 == 1:  # Only odd a have nonzero coefficients
            fhat[a, 0] = hyperplane_hermite_1d(a, dps)
            if verbose:
                print(f"  f̃_{{{a},0}} = {mp.nstr(fhat[a, 0], 15)}")

    return fhat


def BK_hyperplane_baseline(k_max: int, dps: int = 100, verbose: bool = False) -> BKResult:
    """
    Compute B_K(f_0, f_0) for the hyperplane f_0(x) = sign(x_1).

    This is the baseline value that perturbations should beat.

    Args:
        k_max: Maximum degree
        dps: Decimal precision
        verbose: Print diagnostics

    Returns:
        BKResult for the hyperplane baseline
    """
    mp.dps = dps

    if verbose:
        print("Computing hyperplane baseline f_0(x) = sign(x_1)")
        print("Building Hermite coefficient matrix...")

    fhat = build_hyperplane_matrix(k_max, dps, verbose=verbose)

    if verbose:
        print("\nComputing B_K(f_0, f_0)...")

    return BK_from_hermite(fhat, fhat, k_max, dps, verbose=verbose)


def find_max_eta(
    eval_BK_eta: Callable[[mp.mpf], BKResult],
    baseline_BK: mp.mpf,
    eta_lo: mp.mpf,
    eta_hi: mp.mpf,
    tol: mp.mpf = None,
    max_iters: int = 100,
    verbose: bool = False,
) -> dict:
    """
    Find the maximum eta where B_K(f_eta, g_eta) > B_K(f_0, f_0).

    Uses bisection on Δ(η) = B_K(f_η, g_η) - B_K(f_0, f_0).

    Args:
        eval_BK_eta: Function that takes eta and returns BKResult
        baseline_BK: B_K(f_0, f_0) baseline value
        eta_lo: Lower bound for eta (should have Δ > 0)
        eta_hi: Upper bound for eta (should have Δ < 0)
        tol: Tolerance for bisection
        max_iters: Maximum iterations
        verbose: Print progress

    Returns:
        Dictionary with optimal eta and diagnostics
    """
    if tol is None:
        tol = mp.mpf('1e-10')

    eta_lo = mp.mpf(str(eta_lo))
    eta_hi = mp.mpf(str(eta_hi))

    def Delta(eta):
        result = eval_BK_eta(eta)
        return result.BK - baseline_BK

    # Verify initial conditions
    Delta_lo = Delta(eta_lo)
    Delta_hi = Delta(eta_hi)

    if verbose:
        print(f"Initial: eta_lo={mp.nstr(eta_lo, 6)}, Δ={mp.nstr(Delta_lo, 15)}")
        print(f"Initial: eta_hi={mp.nstr(eta_hi, 6)}, Δ={mp.nstr(Delta_hi, 15)}")

    if Delta_lo <= 0:
        return {
            'success': False,
            'message': f"Δ(eta_lo) = {Delta_lo} <= 0, need positive starting point",
            'eta_lo': eta_lo,
            'Delta_lo': Delta_lo,
        }

    if Delta_hi >= 0:
        return {
            'success': False,
            'message': f"Δ(eta_hi) = {Delta_hi} >= 0, eta_hi not large enough",
            'eta_hi': eta_hi,
            'Delta_hi': Delta_hi,
        }

    # Bisection
    for iteration in range(max_iters):
        eta_mid = (eta_lo + eta_hi) / 2
        Delta_mid = Delta(eta_mid)

        if verbose:
            print(f"Iter {iteration+1}: eta={mp.nstr(eta_mid, 10)}, Δ={mp.nstr(Delta_mid, 15)}")

        if Delta_mid > 0:
            eta_lo = eta_mid
        else:
            eta_hi = eta_mid

        if eta_hi - eta_lo < tol:
            break

    # Final result
    eta_star = (eta_lo + eta_hi) / 2
    final_result = eval_BK_eta(eta_star)

    return {
        'success': True,
        'eta_star': eta_star,
        'BK_eta': final_result.BK,
        'Delta': final_result.BK - baseline_BK,
        'baseline_BK': baseline_BK,
        'iterations': iteration + 1,
        'eta_lo': eta_lo,
        'eta_hi': eta_hi,
    }


def compute_BK_from_results(results: dict, k_max: int = None, dps: int = 100, verbose: bool = False) -> BKResult:
    """
    Compute B_K from a results dict containing 'cf' and 'cg' matrices.

    This is the main interface for using coefficients computed by
    single_curve_mpmath.estimate().

    Args:
        results: Dictionary with 'cf' and 'cg' mp.matrix objects
        k_max: Maximum degree (defaults to matrix size - 1)
        dps: Decimal precision
        verbose: Print diagnostics

    Returns:
        BKResult
    """
    mp.dps = dps

    cf = results['cf']
    cg = results['cg']

    if k_max is None:
        k_max = min(cf.rows, cf.cols, cg.rows, cg.cols) - 1

    return BK_from_hermite(cf, cg, k_max, dps, verbose)


def test_hyperplane_baseline():
    """Test the hyperplane baseline computation."""
    mp.dps = 50

    print("=" * 70)
    print("Testing hyperplane baseline f_0(x) = sign(x_1)")
    print("Using ORTHONORMAL Hermite basis: h_n = He_n/√(n!)")
    print("Kernel weight: (-1)^{(k-1)/2} / √(k!)")
    print("=" * 70)

    # Test 1D Hermite coefficients
    print("\n1D orthonormal Hermite coefficients for sign(x):")
    print("f̃_n = √(2/π) · (n-2)!! / √(n!) for odd n")
    for n in range(1, 12, 2):
        c = hyperplane_hermite_1d(n, dps=50)
        print(f"  f̃_{n} = {mp.nstr(c, 20)}")

    # Test B_K computation
    print("\nB_K(f_0, f_0) by k_max:")
    for k_max in [5, 11, 21, 31, 41]:
        result = BK_hyperplane_baseline(k_max, dps=50)
        print(f"  k_max={k_max:3d}: B_K = {mp.nstr(result.BK, 20)}, S = {mp.nstr(result.S, 20)}")


if __name__ == '__main__':
    test_hyperplane_baseline()
