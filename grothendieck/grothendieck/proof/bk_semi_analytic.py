#!/usr/bin/env python3
"""
Semi-analytic computation of B_K using direct integration at z=i.

Computes Δ(η) = H_η(i)/i - H_0(i)/i where:
    f_η(x1,x2) = sign(x2 - η P(x1))
    g_η(y1,y2) = sign(y2 + η Q(y1))

P and Q are arbitrary functions (typically orthonormal Hermite polynomials).

Uses the identity:
    H_η(i)/i = π E[f_η(X) g_η(Y) sin(⟨X,Y⟩)]

Key reduction: E(t,s) = E[sign(X-t)sign(Y-s)e^{iXY}] reduces to a single 1D integral:
    E(t,s) = -1/√(2π) ∫ sign(x-t) e^{-x²} erf((s-ix)/√2) dx

CRITICAL: Direct GH quadrature on sign(x-t)*erf(...) fails because sign(x-t) is
discontinuous at x=t. Instead we compute:

    E(t,s) = (2·CDF(t,s) - I_full(s)) / √(2π)

where I_full(s) = ∫ erf(...) e^{-x²} dx (smooth, computed via GH),
and CDF(t,s) = ∫_{-∞}^t erf(...) e^{-x²} dx is computed via composite
Gauss-Legendre quadrature with panel boundaries at all t_i values.

OPTIMIZATIONS:
1. Composite GL: panels bounded by sorted t values, precompute CDF via prefix sum
2. Symmetry: E(-t,-s) = E(t,s), cutting evaluations in half (when P, Q are odd)
3. I_full via GH (smooth integrand, exponential convergence)
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Callable
from mpmath import mp, pi, mpc

from flint import arb, ctx as flint_ctx

from grothendieck.estimators.single_curve_mpmath.quadrature import GaussHermite1D
from grothendieck.proof.certified.gauss_legendre import (
    certify_gl_nodes_weights,
)


# --- Orthonormal Hermite polynomials (probabilist's, normalized w.r.t. N(0,1)) ---

def h3(x):
    """Orthonormal Hermite h_3 (physicist's convention, weight e^{-x²}).

    h_3(x) = (2x³ - 3x) / (√3 · π^{1/4})
    """
    return (2*x**3 - 3*x) / (mp.sqrt(3) * mp.power(pi, mp.mpf('0.25')))


def h5(x):
    """Orthonormal Hermite h_5 (physicist's convention, weight e^{-x²}).

    h_5(x) = (4x⁵ - 20x³ + 15x) / (2 π^{1/4} √15)
    """
    return (4*x**5 - 20*x**3 + 15*x) / (2 * mp.power(pi, mp.mpf('0.25')) * mp.sqrt(15))


def hermite_h(k: int):
    """
    Return the k-th orthonormal Hermite polynomial h_k(x).

    Normalized so that E[h_k(X)²] = 1 for X ~ N(0,1).
    Uses the recurrence: He_{k+1}(x) = x He_k(x) - k He_{k-1}(x)
    with h_k = He_k / √(k!).
    """
    def h(x):
        if k == 0:
            return mp.mpf('1')
        if k == 1:
            return x
        # Compute probabilist's Hermite He_k via recurrence
        He_prev, He_curr = mp.mpf('1'), x
        for j in range(1, k):
            He_next = x * He_curr - j * He_prev
            He_prev, He_curr = He_curr, He_next
        return He_curr / mp.sqrt(mp.fac(k))
    return h


@dataclass
class BKSemiAnalyticResult:
    """Result from semi-analytic B_K computation."""
    H_eta_over_i: mp.mpf    # H_η(i)/i
    H_0_over_i: mp.mpf      # H_0(i)/i (baseline)
    Delta: mp.mpf           # Δ(η) = H_η(i)/i - H_0(i)/i
    eta: mp.mpf


def _arb_to_mpf(x: arb) -> mp.mpf:
    """Convert arb midpoint to mpmath mpf via string."""
    s = str(x.mid())
    # str(arb) may include '[... +/- ...]'; extract the numeric part
    if s.startswith('['):
        s = s[1:]
    idx = s.find('+/-')
    if idx >= 0:
        s = s[:idx].strip()
    return mp.mpf(s)


class GaussLegendre:
    """Gauss-Legendre quadrature on [-1, 1] with caching.

    Uses certified arb.legendre_p_root via the gauss_legendre module,
    then converts to mpmath for use in the semi-analytic pipeline.
    """

    _cache: dict[tuple[int, int], tuple[list, list]] = {}

    def __init__(self, p: int, dps: int):
        self.p = p
        self.dps = dps
        key = (p, dps)
        if key not in GaussLegendre._cache:
            # Use ~3.32 bits per decimal digit, with some headroom
            prec = max(128, int(dps * 3.5) + 64)
            arb_nodes, arb_weights = certify_gl_nodes_weights(p, prec=prec)
            # str(arb) output depends on flint_ctx.prec, so set it high
            # for the conversion to mpmath
            old_prec = flint_ctx.prec
            flint_ctx.prec = prec
            old_dps = mp.dps
            mp.dps = dps + 20
            nodes = [_arb_to_mpf(x) for x in arb_nodes]
            weights = [_arb_to_mpf(w) for w in arb_weights]
            mp.dps = old_dps
            flint_ctx.prec = old_prec
            GaussLegendre._cache[key] = (nodes, weights)
        self.nodes, self.weights = GaussLegendre._cache[key]

    def integrate(self, f, a, b):
        """Integrate f over [a, b] using GL quadrature."""
        mid = (a + b) / 2
        half = (b - a) / 2
        result = sum(self.weights[k] * f(mid + half * self.nodes[k])
                     for k in range(self.p))
        return result * half


def E_inner_integral(t: mp.mpf, s: mp.mpf, gh: GaussHermite1D) -> mpc:
    """
    Compute E(t,s) via split integral with GL quadrature on each half.

    Uses mp.quad to split at t accurately.
    """
    dps = gh.dps
    mp.dps = dps
    sqrt2 = mp.sqrt(2)
    sqrt2pi = mp.sqrt(2 * pi)

    def integrand(x):
        arg = (s - mpc(0, 1) * x) / sqrt2
        return mp.exp(-x**2) * mp.erf(arg)

    # Split at t, use finite bounds (e^{-15²} ≈ 10^{-98})
    I_neg = mp.quad(integrand, [-15, t])
    I_pos = mp.quad(integrand, [t, 15])

    return -(I_pos - I_neg) / sqrt2pi


# Keep for backward compat
E_inner_integral_optimized = None


def compute_C_S(t: mp.mpf, s: mp.mpf, gh: GaussHermite1D) -> tuple[mp.mpf, mp.mpf]:
    """
    Compute C(t,s) and S(t,s) from E(t,s).

    C(t,s) = E[sign(X-t)sign(Y-s)cos(XY)] = Re(E(t,s))
    S(t,s) = E[sign(X-t)sign(Y-s)sin(XY)] = Im(E(t,s))
    """
    E_val = E_inner_integral(t, s, gh)
    return mp.re(E_val), mp.im(E_val)


def compute_H_0_over_i(gh: GaussHermite1D) -> mp.mpf:
    """
    Compute H_0(i)/i = π S(0,0) E[cos(UV)]

    For U,V ~ N(0,1): E[cos(UV)] = 1/√2 (from characteristic function).
    C(0,0) = 0 by symmetry.
    """
    dps = gh.dps
    mp.dps = dps

    # Compute S(0,0) via split quadrature (accurate)
    C_00, S_00 = compute_C_S(mp.mpf('0'), mp.mpf('0'), gh)

    # E[cos(UV)] via 2D GH (smooth integrand, accurate)
    u_nodes = gh.gaussian_nodes
    weights = gh.weights
    n = gh.n_points
    factor = gh.gaussian_factor  # 1/√π

    E_sin_uv = mp.mpf('0')
    E_cos_uv = mp.mpf('0')

    for i in range(n):
        u = u_nodes[i]
        w_u = weights[i]
        for j in range(n):
            v = u_nodes[j]
            w_v = weights[j]
            uv = u * v
            E_sin_uv += w_u * w_v * mp.sin(uv)
            E_cos_uv += w_u * w_v * mp.cos(uv)

    E_sin_uv *= factor * factor
    E_cos_uv *= factor * factor

    # H_0(i)/i = π [C(0,0) E[sin(UV)] + S(0,0) E[cos(UV)]]
    result = pi * (C_00 * E_sin_uv + S_00 * E_cos_uv)

    return result


def _physicist_hermite(n: int, z):
    """Physicist's Hermite polynomial H_n(z) via recurrence."""
    if n == 0:
        return mp.mpf('1')
    H_prev, H_curr = mp.mpf('1'), 2 * z
    for k in range(1, n):
        H_next = 2 * z * H_curr - 2 * k * H_prev
        H_prev, H_curr = H_curr, H_next
    return H_curr


def _taylor_coeffs_g(s, K: int):
    """
    Taylor coefficients of g(x,s) = e^{-x²} erf((s-ix)/√2) around x=0.

    Returns c[0], ..., c[K] where g(x,s) = Σ c[k] x^k + O(x^{K+1}).

    Uses:
      e^{-x²} = Σ (-1)^m x^{2m} / m!   (a[n] coefficients)
      erf(z_0 + z_1 x) with z_0=s/√2, z_1=-i/√2:
        b[n] = z_1^n / n! × erf^{(n)}(z_0)
      where erf^{(n)}(z) = (2/√π) (-1)^{n-1} H_{n-1}(z) e^{-z²} for n≥1.
    """
    sqrt2 = mp.sqrt(2)
    z0 = s / sqrt2
    z1 = mpc(0, -1) / sqrt2
    exp_z0_sq = mp.exp(-z0**2)

    # Compute b[n] = Taylor coeffs of erf(z0 + z1*x)
    b = [None] * (K + 1)
    b[0] = mp.erf(z0)
    two_over_sqrtpi = 2 / mp.sqrt(pi)
    z1_power = mpc(1)
    for n in range(1, K + 1):
        z1_power *= z1
        Hn_minus_1 = _physicist_hermite(n - 1, z0)
        erf_deriv_n = two_over_sqrtpi * ((-1) ** (n - 1)) * Hn_minus_1 * exp_z0_sq
        b[n] = z1_power * erf_deriv_n / mp.fac(n)

    # Compute a[n] = Taylor coeffs of e^{-x²}: a[2m] = (-1)^m / m!, a[odd] = 0
    a = [mpc(0)] * (K + 1)
    for m in range(K // 2 + 1):
        if 2 * m <= K:
            a[2 * m] = mp.mpf((-1) ** m) / mp.fac(m)

    # Convolve: c[n] = Σ_{j=0}^{n} a[j] * b[n-j]
    c = [mpc(0)] * (K + 1)
    for n in range(K + 1):
        for j in range(n + 1):
            c[n] += a[j] * b[n - j]

    return c


def precompute_E_matrix_taylor(
    eta: mp.mpf,
    gh: GaussHermite1D,
    P: Callable = None,
    Q: Callable = None,
    odd_symmetry: bool = True,
    K: int = None,
    verbose: bool = False,
) -> tuple[list[list[mpc]], list[mp.mpf], list[mp.mpf]]:
    """
    Fast E matrix via Taylor expansion of E(t,s) around t=0.

    E(t,s) = E(0,s) + (2/√(2π)) Σ_{k=0}^{K} [c_k(s) / (k+1)] t^{k+1}

    where c_k(s) are Taylor coefficients of g(x,s) = e^{-x²} erf((s-ix)/√2).

    Much faster than composite GL for small eta (all t values near 0).
    """
    if P is None:
        P = h3
    if Q is None:
        Q = h3

    dps = gh.dps
    mp.dps = dps
    n = gh.n_points
    u_nodes = gh.gaussian_nodes
    sqrt2pi = mp.sqrt(2 * pi)

    # Precompute t and s arrays
    t_vals = [eta * P(u_nodes[i]) for i in range(n)]
    s_vals = [-eta * Q(u_nodes[j]) for j in range(n)]

    t_max = max(abs(t) for t in t_vals)

    # Auto-choose K if not specified: need (t_max)^{K+1} / (K+1)! < 10^{-(dps+10)}
    if K is None:
        K = 10
        target = mp.power(10, -(dps + 10))
        while K < 200:
            term = t_max ** (K + 1) / mp.fac(K + 1)
            if term < target:
                break
            K += 5
    if verbose:
        print(f"  Taylor expansion: K={K} terms, t_max={mp.nstr(t_max, 5)}")

    n_s = (n + 1) // 2 if odd_symmetry else n

    # Compute E(0, s_j) for each s via mp.quad (split at 0)
    sqrt2 = mp.sqrt(2)
    E_0 = [None] * n_s
    if verbose:
        print(f"  Computing E(0, s_j) for {n_s} s-values via mp.quad...")

    for j in range(n_s):
        s = s_vals[j]

        def integrand(x, _s=s):
            return mp.exp(-x**2) * mp.erf((_s - mpc(0, 1) * x) / sqrt2)

        I_neg = mp.quad(integrand, [-15, 0])
        I_pos = mp.quad(integrand, [0, 15])
        E_0[j] = -(I_pos - I_neg) / sqrt2pi

    if verbose:
        print(f"  Computing Taylor coefficients for {n_s} s-values...")

    # Compute Taylor coefficients c_k(s_j) for each s
    taylor_coeffs = [None] * n_s
    for j in range(n_s):
        taylor_coeffs[j] = _taylor_coeffs_g(s_vals[j], K)

    if verbose:
        print(f"  Building E matrix from Taylor series...")

    # Build E matrix
    E_matrix = [[None for _ in range(n)] for _ in range(n)]
    two_over_sqrt2pi = 2 / sqrt2pi

    for j in range(n_s):
        c = taylor_coeffs[j]
        e0 = E_0[j]
        for i in range(n):
            t = t_vals[i]
            # E(t,s) = E(0,s) + (2/√(2π)) × Σ_{k=0}^K c[k]/(k+1) × t^{k+1}
            correction = mpc(0)
            t_power = t  # t^{k+1} for k=0
            for k in range(K + 1):
                correction += c[k] / (k + 1) * t_power
                t_power *= t
            E_matrix[i][j] = e0 + two_over_sqrt2pi * correction

    # Fill symmetric entries
    if odd_symmetry:
        for j in range(n_s):
            j_sym = n - 1 - j
            if j_sym <= j:
                continue
            for i in range(n):
                i_sym = n - 1 - i
                E_matrix[i][j_sym] = E_matrix[i_sym][j]

    return E_matrix, t_vals, s_vals


def precompute_E_matrix(
    eta: mp.mpf,
    gh: GaussHermite1D,
    gl_order: int = 30,
    verbose: bool = False,
    P: Callable = None,
    Q: Callable = None,
    odd_symmetry: bool = True,
) -> tuple[list[list[mpc]], list[mp.mpf], list[mp.mpf]]:
    """
    Precompute E(t_i, s_j) matrix for all (i,j) pairs.

    Auto-selects method:
    - Taylor expansion when t_max < 1 (fast, O(K) terms per s)
    - Composite GL when t values are spread out (slower, needs many panels)

    Args:
        eta: Perturbation parameter.
        gh: Gauss-Hermite quadrature object.
        gl_order: Gauss-Legendre order per panel.
        verbose: Print progress.
        P: Function for f_η(x1,x2) = sign(x2 - η P(x1)). Defaults to h3.
        Q: Function for g_η(y1,y2) = sign(y2 + η Q(y1)). Defaults to h3.
        odd_symmetry: If True, exploit E(-t,-s) = E(t,s) (valid when P, Q are odd).
    """
    if P is None:
        P = h3
    if Q is None:
        Q = h3

    # Check t_max to decide method
    dps = gh.dps
    mp.dps = dps
    u_nodes = gh.gaussian_nodes
    n = gh.n_points
    t_max = max(abs(eta * P(u_nodes[i])) for i in range(n))

    # Force Taylor path for complex eta (composite GL requires real-valued sorting)
    eta_is_complex = isinstance(eta, mpc)

    # Use Taylor when t_max < 1 or eta is complex
    if t_max < 1 or eta_is_complex:
        if verbose:
            reason = "complex η" if eta_is_complex else f"t_max = {mp.nstr(t_max, 5)} < 1"
            print(f"  Using Taylor expansion ({reason})")
        return precompute_E_matrix_taylor(
            eta, gh, P=P, Q=Q, odd_symmetry=odd_symmetry, verbose=verbose,
        )

    if verbose:
        print(f"  Using composite GL (t_max = {mp.nstr(t_max, 5)} >= 1)")

    dps = gh.dps
    mp.dps = dps

    n = gh.n_points
    u_nodes = gh.gaussian_nodes
    sqrt2 = mp.sqrt(2)
    sqrt2pi = mp.sqrt(2 * pi)

    # Precompute t and s arrays: t_i = η P(u_i), s_j = -η Q(v_j)
    t_vals = [eta * P(u_nodes[i]) for i in range(n)]
    s_vals = [-eta * Q(u_nodes[j]) for j in range(n)]

    # Sort t values and keep track of original indices
    t_with_idx = sorted(enumerate(t_vals), key=lambda x: x[1])
    sorted_indices = [idx for idx, _ in t_with_idx]
    t_sorted = [t for _, t in t_with_idx]

    # GL quadrature nodes/weights on [-1, 1]
    if verbose:
        print(f"  Computing GL({gl_order}) nodes...")
    gl = GaussLegendre(gl_order, dps)

    # Build panel boundaries: [-L, t_sorted[0], t_sorted[1], ..., t_sorted[n-1], L]
    L = mp.mpf('15')  # e^{-15²} ≈ 10^{-98}

    # Deduplicate very close t values (within machine precision)
    raw_boundaries = [-L]
    for t in t_sorted:
        if t > raw_boundaries[-1]:
            raw_boundaries.append(t)
    raw_boundaries.append(L)

    # Subdivide large panels: GL(p) needs panels of width ≤ ~1 for high precision
    max_panel_width = mp.mpf('1')
    boundaries = [raw_boundaries[0]]
    for m in range(len(raw_boundaries) - 1):
        a = raw_boundaries[m]
        b = raw_boundaries[m + 1]
        width = b - a
        if width > max_panel_width:
            n_sub = int(mp.ceil(width / max_panel_width))
            for k in range(1, n_sub):
                boundaries.append(a + k * width / n_sub)
        boundaries.append(b)

    # Map original t indices to boundary positions
    # For each t_sorted[k], find which boundary it corresponds to
    t_to_boundary = {}
    for k, t in enumerate(t_sorted):
        # Find the boundary index for this t
        for b_idx, b_val in enumerate(boundaries):
            if b_val >= t:
                t_to_boundary[sorted_indices[k]] = b_idx
                break

    # Initialize E matrix
    E_matrix = [[None for _ in range(n)] for _ in range(n)]

    # Exploit symmetry: E(-t,-s) = E(t,s) when P, Q are odd
    n_s = (n + 1) // 2 if odd_symmetry else n

    if verbose:
        sym_str = f"{n_s} s-values with symmetry" if odd_symmetry else f"{n} s-values (no symmetry)"
        print(f"  Precomputing E matrix ({n}x{n}, {sym_str})")
        print(f"  {len(boundaries)-1} GL panels, GL order {gl_order}")

    for j in range(n_s):
        s = s_vals[j]

        # I_full via GH (smooth integrand, exponential convergence)
        I_full = sum(gh.weights[k] * mp.erf((s - mpc(0, 1) * gh.nodes[k]) / sqrt2)
                     for k in range(n))

        # Compute panel integrals via GL and build CDF at boundaries
        # Use midpoint rule for tiny panels (error O(width³) is negligible)
        min_gl_width = mp.power(10, -dps // 3)
        panel_integrals = []
        def _integrand(x, _s=s):
            return mp.exp(-x**2) * mp.erf((_s - mpc(0, 1) * x) / sqrt2)
        for m in range(len(boundaries) - 1):
            a = boundaries[m]
            b = boundaries[m + 1]
            width = b - a
            if width <= 0:
                panel_integrals.append(mpc(0))
                continue
            if width < min_gl_width:
                # Midpoint rule: error O(width³ × f'') is negligible
                panel_integrals.append(width * _integrand((a + b) / 2))
            else:
                I_panel = gl.integrate(_integrand, a, b)
                panel_integrals.append(I_panel)

        # CDF at boundary[m] = sum of panels 0..m-1
        cdf_at_boundary = [mpc(0)]
        for m in range(len(boundaries) - 1):
            cdf_at_boundary.append(cdf_at_boundary[-1] + panel_integrals[m])

        # For each t_i, look up CDF(t_i) from the boundary map
        for i in range(n):
            b_idx = t_to_boundary[i]
            cdf_val = cdf_at_boundary[b_idx]

            # E(t,s) = (2·CDF(t) - I_full) / √(2π)
            E_matrix[i][j] = (2 * cdf_val - I_full) / sqrt2pi

        if verbose and (j + 1) % 25 == 0:
            print(f"    s-values: {j+1}/{n_s}", end='\r')

    if verbose:
        print(f"    s-values: {n_s}/{n_s} (done" +
              (", filling symmetry...)" if odd_symmetry else ")"))

    # Fill symmetric entries: E_matrix[i][n-1-j] = E_matrix[n-1-i][j]
    if odd_symmetry:
        for j in range(n_s):
            j_sym = n - 1 - j
            if j_sym <= j:
                continue
            for i in range(n):
                i_sym = n - 1 - i
                E_matrix[i][j_sym] = E_matrix[i_sym][j]

    return E_matrix, t_vals, s_vals


def precompute_erf_and_cumsum(s, gh):
    """Deprecated: kept for API compatibility."""
    sqrt2 = mp.sqrt(2)
    n = gh.n_points
    f_vals = [mp.erf((s - mpc(0, 1) * gh.nodes[k]) / sqrt2) for k in range(n)]
    I_full = sum(gh.weights[k] * f_vals[k] for k in range(n))
    return f_vals, I_full, None


def compute_G_complex(eta, gh: GaussHermite1D, verbose: bool = False,
                      gl_order: int = 30,
                      P: Callable = None, Q: Callable = None,
                      odd_symmetry: bool = True) -> mpc:
    """
    Compute the full complex G(η) for possibly complex η.

    G(η) = π · factor² · Σ_{i,j} w_i w_j · E(ηP(u_i), -ηQ(v_j)) · exp(i·u_i·v_j)

    For real η, Im(G(η)) = H_η(i)/i (the quantity used in B_K).
    G(η) is entire in η, so this function works for complex η values
    needed by the Cauchy integral method.

    Returns:
        Full complex value G(η).
    """
    dps = gh.dps
    mp.dps = dps

    if eta == 0:
        # G(0) = π · factor² · Σ w_i w_j · E(0,0) · exp(i·u_i·v_j)
        C_00, S_00 = compute_C_S(mp.mpf('0'), mp.mpf('0'), gh)
        E_00 = mpc(C_00, S_00)
        u_nodes = gh.gaussian_nodes
        weights = gh.weights
        n = gh.n_points
        factor = gh.gaussian_factor

        result = mpc(0)
        for i in range(n):
            u = u_nodes[i]
            w_u = weights[i]
            for j in range(n):
                v = u_nodes[j]
                w_v = weights[j]
                uv = u * v
                exp_iuv = mpc(mp.cos(uv), mp.sin(uv))
                result += w_u * w_v * E_00 * exp_iuv
        result *= factor * factor * pi
        return result

    # Precompute E matrix (works for complex eta)
    E_matrix, _, _ = precompute_E_matrix(
        eta, gh, gl_order=gl_order, verbose=verbose,
        P=P, Q=Q, odd_symmetry=odd_symmetry,
    )

    u_nodes = gh.gaussian_nodes
    weights = gh.weights
    n = gh.n_points
    factor = gh.gaussian_factor

    if verbose:
        print("  Computing G(η) (full complex)...")

    result = mpc(0)
    for i in range(n):
        u = u_nodes[i]
        w_u = weights[i]
        for j in range(n):
            v = u_nodes[j]
            w_v = weights[j]
            E_val = E_matrix[i][j]
            uv = u * v
            exp_iuv = mpc(mp.cos(uv), mp.sin(uv))
            result += w_u * w_v * E_val * exp_iuv
    result *= factor * factor * pi
    return result


def compute_H_over_i(eta: mp.mpf, gh: GaussHermite1D, verbose: bool = False,
                     gl_order: int = 30,
                     P: Callable = None, Q: Callable = None,
                     odd_symmetry: bool = True) -> mp.mpf:
    """
    Compute H_η(i)/i = π E_{u,v}[sin(uv) C(t,s) + cos(uv) S(t,s)]

    where t = η P(u), s = -η Q(v).
    """
    dps = gh.dps
    mp.dps = dps

    if eta == 0:
        return compute_H_0_over_i(gh)

    # Precompute E matrix
    E_matrix, _, _ = precompute_E_matrix(
        eta, gh, gl_order=gl_order, verbose=verbose,
        P=P, Q=Q, odd_symmetry=odd_symmetry,
    )

    u_nodes = gh.gaussian_nodes
    weights = gh.weights
    n = gh.n_points
    factor = gh.gaussian_factor

    if verbose:
        print("  Computing outer integral...")

    result = mp.mpf('0')

    for i in range(n):
        u = u_nodes[i]
        w_u = weights[i]
        for j in range(n):
            v = u_nodes[j]
            w_v = weights[j]
            E_val = E_matrix[i][j]
            uv = u * v
            integrand = mp.sin(uv) * mp.re(E_val) + mp.cos(uv) * mp.im(E_val)
            result += w_u * w_v * integrand

    result *= factor * factor * pi
    return result


def compute_Delta(eta: mp.mpf, dps: int = 100, gl_order: int = 30,
                  verbose: bool = False,
                  P: Callable = None, Q: Callable = None,
                  odd_symmetry: bool = True) -> BKSemiAnalyticResult:
    """
    Compute Δ(η) = H_η(i)/i - H_0(i)/i using semi-analytic integration.

    Args:
        P: Function for f_η(x1,x2) = sign(x2 - η P(x1)). Defaults to h3.
        Q: Function for g_η(y1,y2) = sign(y2 + η Q(y1)). Defaults to h3.
        odd_symmetry: If True, exploit E(-t,-s)=E(t,s) (valid when P, Q odd).
    """
    mp.dps = dps

    gh = GaussHermite1D(dps=dps)

    if verbose:
        print(f"Computing Δ(η) for η = {mp.nstr(eta, 10)}")
        print(f"Using {gh.n_points} GH nodes, {dps} dps, GL order {gl_order}")
        print("Computing H_0(i)/i (baseline)...")

    H_0 = compute_H_0_over_i(gh)

    if verbose:
        print(f"  H_0(i)/i = {mp.nstr(H_0, 20)}")
        expected = mp.atanh(1 / mp.sqrt(2))
        print(f"  atanh(1/√2) = {mp.nstr(expected, 20)}")
        print(f"  |diff| = {mp.nstr(abs(H_0 - expected), 5)}")
        print(f"Computing H_η(i)/i (composite GL + symmetry)...")

    H_eta = compute_H_over_i(eta, gh, verbose=verbose, gl_order=gl_order,
                             P=P, Q=Q, odd_symmetry=odd_symmetry)

    if verbose:
        print(f"  H_η(i)/i = {mp.nstr(H_eta, 20)}")

    Delta = H_eta - H_0

    if verbose:
        print(f"  Δ(η) = {mp.nstr(Delta, 20)}")

    return BKSemiAnalyticResult(
        H_eta_over_i=H_eta,
        H_0_over_i=H_0,
        Delta=Delta,
        eta=eta,
    )


def compute_Delta_direct(eta: mp.mpf, dps: int = 100, gl_order: int = 30,
                         verbose: bool = False,
                         P: Callable = None, Q: Callable = None,
                         odd_symmetry: bool = True) -> BKSemiAnalyticResult:
    """
    Compute Δ(η) by directly computing the difference integrand.

    Δ(η) = π E_{u,v}[sin(uv) ΔC + cos(uv) ΔS]
    where ΔC = C(t,s) - C(0,0), ΔS = S(t,s) - S(0,0).
    """
    mp.dps = dps

    gh = GaussHermite1D(dps=dps)

    if verbose:
        print(f"Computing Δ(η) directly for η = {mp.nstr(eta, 10)}")

    # Precompute C(0,0) and S(0,0)
    C_00, S_00 = compute_C_S(mp.mpf('0'), mp.mpf('0'), gh)

    if verbose:
        print(f"  C(0,0) = {mp.nstr(C_00, 15)}")
        print(f"  S(0,0) = {mp.nstr(S_00, 15)}")

    # Precompute E matrix
    E_matrix, _, _ = precompute_E_matrix(
        eta, gh, gl_order=gl_order, verbose=verbose,
        P=P, Q=Q, odd_symmetry=odd_symmetry,
    )

    u_nodes = gh.gaussian_nodes
    weights = gh.weights
    n = gh.n_points
    factor = gh.gaussian_factor

    Delta_sum = mp.mpf('0')

    for i in range(n):
        u = u_nodes[i]
        w_u = weights[i]
        for j in range(n):
            v = u_nodes[j]
            w_v = weights[j]
            E_val = E_matrix[i][j]
            uv = u * v
            integrand = (mp.sin(uv) * (mp.re(E_val) - C_00)
                         + mp.cos(uv) * (mp.im(E_val) - S_00))
            Delta_sum += w_u * w_v * integrand

    Delta = Delta_sum * factor * factor * pi

    H_0 = compute_H_0_over_i(gh)
    H_eta = H_0 + Delta

    if verbose:
        print(f"  Δ(η) = {mp.nstr(Delta, 20)}")

    return BKSemiAnalyticResult(
        H_eta_over_i=H_eta,
        H_0_over_i=H_0,
        Delta=Delta,
        eta=eta,
    )


def verify_quadrature():
    """Verify that the outer quadrature gives correct Gaussian moments."""
    mp.dps = 50
    gh = GaussHermite1D(dps=50)

    u_nodes = gh.gaussian_nodes
    weights = gh.weights
    factor = gh.gaussian_factor

    E_1 = sum(w for w in weights) * factor
    print(f"E[1]   = {mp.nstr(E_1, 15)} (expected: 1)")

    E_U2 = sum(w * u**2 for w, u in zip(weights, u_nodes)) * factor
    print(f"E[U²]  = {mp.nstr(E_U2, 15)} (expected: 1)")

    E_U4 = sum(w * u**4 for w, u in zip(weights, u_nodes)) * factor
    print(f"E[U⁴]  = {mp.nstr(E_U4, 15)} (expected: 3)")

    E_U6 = sum(w * u**6 for w, u in zip(weights, u_nodes)) * factor
    print(f"E[U⁶]  = {mp.nstr(E_U6, 15)} (expected: 15)")


def test_baseline():
    """Test the baseline computation H_0(i)/i against known value atanh(1/√2)."""
    mp.dps = 50

    print("=" * 70)
    print("Testing semi-analytic B_K computation (composite GL)")
    print("=" * 70)

    print("\nVerifying Gaussian quadrature moments:")
    verify_quadrature()

    gh = GaussHermite1D(dps=50)

    # Test E(0,0)
    E_00 = E_inner_integral(mp.mpf('0'), mp.mpf('0'), gh)
    print(f"\nE(0,0) via split quadrature:")
    print(f"  Re = {mp.nstr(mp.re(E_00), 20)}")
    print(f"  Im = {mp.nstr(mp.im(E_00), 20)}")

    # Test H_0(i)/i
    print("\nComputing H_0(i)/i...")
    H_0 = compute_H_0_over_i(gh)
    expected = mp.atanh(1 / mp.sqrt(2))
    print(f"H_0(i)/i         = {mp.nstr(H_0, 20)}")
    print(f"atanh(1/√2)      = {mp.nstr(expected, 20)}")
    print(f"|diff|            = {mp.nstr(abs(H_0 - expected), 5)}")


if __name__ == '__main__':
    test_baseline()
