"""
H_eta evaluation bridge: compute Taylor coefficients of H_eta(z) and
evaluate H_eta at specific points using rigorous Arb ball arithmetic.

Strategy:
  1. Compute forward series b_k via certified arb integration
  2. H_eta(z) = (pi/2) * sum_k b_k z^k
  3. Convert to arb_series with certified error balls
  4. Compose with sin(z) via Horner for phi computation
  5. Evaluate H_eta(i)/i via bk_rigor
"""

from __future__ import annotations

from typing import Callable, Optional

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    set_prec, certified_positive,
)


def compute_b_series_arb(
    eta: float,
    P_arb: Callable,
    Q_arb: Callable,
    K_max: int = 50,
    prec: int = 256,
    L: int = 25,
    n_gl: int = 48,
    n_panels: int = 30,
    verbose: bool = False,
) -> dict:
    """Compute certified b-series coefficients via arb ball arithmetic.

    Uses composite Gauss-Legendre quadrature with rigorous error bounds
    (tail bound + GL error via Cauchy estimate). Each b_k is a certified
    arb ball guaranteed to contain the true value.

    Args:
        eta: Perturbation parameter.
        P_arb, Q_arb: Arb polynomial functions P(x, prec) -> arb.
            These are the base polynomials (e.g. h3_arb); the function
            constructs P_f(x) = eta*P(x) and P_g(y) = -eta*Q(y) internally.
        K_max: Maximum Hermite degree (number of b-series terms).
        prec: Arb precision in bits.
        L: Truncation radius for integration.
        n_gl: GL nodes per panel.
        n_panels: Number of GL panels on [-L, L].
        verbose: Print progress.

    Returns:
        dict mapping degree k to certified arb ball b_k.
    """
    from grothendieck.estimators.single_curve_arb.hermite_arb import (
        compute_coefficient_matrix_certified,
    )

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    eta_arb = arb(str(eta))

    # Build P_f(x) = eta * P(x),  P_g(y) = -eta * Q(y)
    def P_f(x):
        return eta_arb * P_arb(x, prec)

    def P_g(y):
        return -eta_arb * Q_arb(y, prec)

    # Complex extensions for GL error bounds
    def P_f_acb(z):
        return acb(eta_arb) * P_arb(z, prec)

    def P_g_acb(z):
        return -acb(eta_arb) * Q_arb(z, prec)

    if verbose:
        print(f"  Computing certified cf (prec={prec}, L={L}, "
              f"n_gl={n_gl}, n_panels={n_panels})")

    cf = compute_coefficient_matrix_certified(
        P_f, K_max,
        P_func_acb=P_f_acb,
        n_gl=n_gl, n_panels=n_panels, L=L, prec=prec,
        verbose=verbose,
    )

    if verbose:
        print(f"  Computing certified cg")

    cg = compute_coefficient_matrix_certified(
        P_g, K_max,
        P_func_acb=P_g_acb,
        n_gl=n_gl, n_panels=n_panels, L=L, prec=prec,
        verbose=verbose,
    )

    # Build b[n] = sum_{i+j=n} cf[i][j] * cg[i][j]
    sz = K_max + 1
    b = {}
    for n in range(1, K_max + 1):
        s = arb(0)
        for i in range(n + 1):
            j = n - i
            if i < sz and j < sz:
                s = s + cf[i][j] * cg[i][j]
        b[n] = s

    if verbose:
        print(f"  b_1 = {b.get(1, arb(0))}")
        if K_max >= 3:
            print(f"  b_3 = {b.get(3, arb(0))}")

    flint_ctx.prec = old_prec
    return b


def b_series_to_h_eta_arb_series(
    b: dict,
    K_max: int,
    prec: int = 128,
) -> arb_series:
    """Convert arb b_k dict to H_eta arb_series.

    H_eta(z) = (pi/2) * sum_k b_k z^k

    Each b_k should be an arb ball (certified or loaded from cache).

    Returns arb_series of length K_max+1.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    pi_half = arb.pi() / 2

    coeffs = []
    for k in range(K_max + 1):
        if k in b:
            coeffs.append(pi_half * b[k])
        else:
            coeffs.append(arb(0))

    result = arb_series(coeffs, K_max + 1)
    flint_ctx.prec = old_prec
    return result


def load_b_series_from_json(
    path: str,
    K_max: Optional[int] = None,
    prec: int = 128,
    error_dps: Optional[int] = None,
    verbose: bool = False,
) -> arb_series:
    """Load cached b_k coefficients from JSON and convert to H_eta arb_series.

    The JSON file should have keys "b" (dict of str->str), "K_max", "dps".
    Each coefficient string is parsed as an arb midpoint and inflated by
    10^{-error_dps} to account for the original quadrature error.

    Args:
        path: Path to JSON file.
        K_max: Use at most this many terms (default: all from file).
        prec: Arb precision in bits.
        error_dps: Error ball radius 10^{-error_dps}. Auto if None.
        verbose: Print diagnostics.

    Returns:
        arb_series representing H_eta(z).
    """
    import json

    with open(path) as f:
        data = json.load(f)

    file_K = data["K_max"]
    file_dps = data["dps"]

    if K_max is None:
        K_max = file_K
    else:
        K_max = min(K_max, file_K)

    if error_dps is None:
        error_dps = max(file_dps - 10, 20)

    if verbose:
        print(f"Loading b_k from {path}")
        print(f"  file: K_max={file_K}, dps={file_dps}")
        print(f"  using: K_max={K_max}, error_dps={error_dps}")

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    error_radius = arb(10) ** (-error_dps)

    # Parse JSON strings directly as arb (no mpmath needed)
    b_str = data["b"]
    b = {}
    for k in range(1, K_max + 1):
        key = str(k)
        if key in b_str:
            mid = arb(b_str[key])
            # Inflate by error_radius to account for original quadrature error
            b[k] = arb.union(mid - error_radius, mid + error_radius)

    flint_ctx.prec = old_prec

    h_series = b_series_to_h_eta_arb_series(b, K_max, prec)

    if verbose:
        h_coeffs = h_series.coeffs()
        if len(h_coeffs) > 1:
            print(f"  h_1 = {h_coeffs[1]}")
        if len(h_coeffs) > 3:
            print(f"  h_3 = {h_coeffs[3]}")

    return h_series


def compute_h_eta_series(
    eta: float,
    P_arb: Callable,
    Q_arb: Callable,
    K_max: int = 50,
    prec: int = 128,
    L: int = 25,
    n_gl: int = 48,
    n_panels: int = 30,
    verbose: bool = False,
    **kwargs,
) -> arb_series:
    """Compute H_eta(z) as an arb_series with certified b-series.

    Pipeline:
      1. Compute b_k via certified arb integration
      2. h_k = (pi/2) * b_k  (certified arb balls)
      3. Return arb_series

    Args:
        eta: Perturbation parameter.
        P_arb, Q_arb: Arb polynomial functions P(x, prec) -> arb.
        K_max: Maximum Hermite degree.
        prec: Arb precision in bits.
        L: Truncation radius for GL integration.
        n_gl: GL nodes per panel.
        n_panels: Number of GL panels on [-L, L].
        verbose: Print progress.

    Returns:
        arb_series representing H_eta(z) truncated at degree K_max.
    """
    if verbose:
        print(f"Computing certified b_k (K_max={K_max}, prec={prec}, "
              f"L={L}, n_gl={n_gl}, n_panels={n_panels})...")

    b = compute_b_series_arb(
        eta, P_arb, Q_arb, K_max,
        prec=prec, L=L, n_gl=n_gl, n_panels=n_panels,
        verbose=verbose,
    )

    h_series = b_series_to_h_eta_arb_series(b, K_max, prec)

    if verbose:
        h_coeffs = h_series.coeffs()
        if len(h_coeffs) > 1:
            print(f"  h_1 = {h_coeffs[1]}")
        if len(h_coeffs) > 3:
            print(f"  h_3 = {h_coeffs[3]}")
        print(f"  Reference (arcsin): h_1 = 1, h_3 = 1/6 = {1/6:.15f}")

    return h_series


def compose_series_horner(
    outer_coeffs: list,
    inner_series: arb_series,
    K: int,
) -> arb_series:
    """Compose outer(inner(z)) via arb_series built-in composition.

    outer(z) = sum_{k=0}^{N} a_k z^k
    inner(z) must have inner(0) = 0 for convergence.

    Returns arb_series of length K representing outer(inner(z)).
    """
    old_cap = flint_ctx.cap
    flint_ctx.cap = K + 1

    n = len(outer_coeffs)
    if n == 0:
        flint_ctx.cap = old_cap
        return arb_series([arb(0)], K + 1)

    outer = arb_series(outer_coeffs[:n], K + 1)
    result = outer(inner_series)

    flint_ctx.cap = old_cap
    return result


def _compose_series_horner_old(
    outer_coeffs: list,
    inner_series: arb_series,
    K: int,
) -> arb_series:
    """Old manual Horner implementation, kept for reference.

    outer(z) = sum_{k=0}^{N} a_k z^k
    inner(z) must have inner(0) = 0 for convergence.

    Returns arb_series of length K representing outer(inner(z)).
    """
    old_cap = flint_ctx.cap
    flint_ctx.cap = K + 1

    n = len(outer_coeffs)
    if n == 0:
        flint_ctx.cap = old_cap
        return arb_series([arb(0)], K + 1)

    # Horner: start from a_{n-1}
    result = arb_series([outer_coeffs[n - 1]], K + 1)
    for k in range(n - 2, -1, -1):
        result = result * inner_series
        # Ensure truncation at K+1 terms
        coeffs = result.coeffs()
        if len(coeffs) > K + 1:
            coeffs = coeffs[:K + 1]
            result = arb_series(coeffs, K + 1)
        # Add a_k as constant
        result_coeffs = list(result.coeffs())
        while len(result_coeffs) < K + 1:
            result_coeffs.append(arb(0))
        result_coeffs[0] = result_coeffs[0] + outer_coeffs[k]
        result = arb_series(result_coeffs[:K + 1], K + 1)

    flint_ctx.cap = old_cap
    return result


def eval_h_eta_at_i_arb(
    eta: float,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    prec: int = 128,
    L_outer: int = 10,
    n_panels: int = 10,
    n_gl: int = 16,
    verbose: bool = False,
    **kwargs,
) -> tuple:
    """Compute H_eta(i)/i and H_0(i)/i as rigorous arb balls via bk_rigor.

    Uses fully rigorous composite GL + acb.integral (no GH, no heuristic
    error balls). Delegates to bk_rigor.compute_Delta_rigor.

    Args:
        eta: Perturbation parameter.
        P_arb, Q_arb: arb polynomial functions. Defaults to h3_arb.
        prec: Arb precision in bits.
        L_outer: Truncation radius for outer integral.
        n_panels: Number of GL panels per dimension.
        n_gl: GL order per panel.
        verbose: Print progress.

    Returns:
        (H_eta_i_over_i: arb, H_0_i_over_i: arb, Delta: arb)
    """
    from grothendieck.proof.certified.bk_rigor import (
        compute_Delta_rigor,
        h3_arb as _h3_arb,
    )

    if P_arb is None:
        P_arb = _h3_arb
    if Q_arb is None:
        Q_arb = _h3_arb

    result = compute_Delta_rigor(
        eta,
        P_arb=P_arb,
        Q_arb=Q_arb,
        L_outer=L_outer,
        n_panels=n_panels,
        n_gl=n_gl,
        prec=prec,
        verbose=verbose,
    )

    if verbose:
        print(f"  H_eta(i)/i = {result.H_eta_over_i}")
        print(f"  H_0(i)/i   = {result.H_0_over_i}")
        print(f"  Delta      = {result.Delta}")
        print(f"  Delta > 0? {certified_positive(result.Delta)}")

    return result.H_eta_over_i, result.H_0_over_i, result.Delta


def gamma_0_arb(prec: int = 128) -> arb:
    """Compute gamma_0 = atanh(1/sqrt(2)) rigorously."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    result = (arb(1) / arb(2).sqrt()).atanh()
    flint_ctx.prec = old_prec
    return result
