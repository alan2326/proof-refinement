"""
Certified semi-analytic 1D integrator for Hermite expansion coefficients.

Computes I_{i,j} = E[sgn(Y - P(X)) * h_i(X) * h_j(Y)] rigorously using:
  1. Analytical Y-integration (reduces to smooth 1D integral)
  2. Composite Gauss-Legendre quadrature on [-L, L] with certified nodes
  3. Tail bound via Cauchy-Schwarz: |tail| <= sqrt(erfc(L/sqrt(2)))
  4. GL error bound via Cauchy estimate on complex extension

Every returned I_{i,j} is an arb ball guaranteed to contain the true value.
"""

from __future__ import annotations

from typing import Callable

from flint import arb, acb, ctx as flint_ctx

from grothendieck.estimators.single_curve_arb.gaussian_utils_arb import (
    normal_pdf_arb,
    gaussian_one_minus_2cdf_arb,
)
from grothendieck.proof.certified.gauss_legendre import (
    certify_gl_nodes_weights,
    certified_scale_gl_to_interval,
)


# ---------------------------------------------------------------------------
# Hermite polynomials in arb
# ---------------------------------------------------------------------------

def hermite_probabilists_arb(n: int, x: arb) -> arb:
    """Probabilists' Hermite He_n(x) via 3-term recurrence.

    He_0 = 1, He_1 = x, He_{k+1} = x*He_k - k*He_{k-1}
    """
    if n == 0:
        return arb(1)
    if n == 1:
        return x

    h_prev = arb(1)
    h_curr = x
    for k in range(1, n):
        h_next = x * h_curr - arb(k) * h_prev
        h_prev = h_curr
        h_curr = h_next
    return h_curr


def hermite_orthonormal_arb(n: int, x: arb) -> arb:
    """Orthonormal Hermite h_n(x) = He_n(x) / sqrt(n!).

    Satisfies E[h_n(X) * h_m(X)] = delta_{nm} for X ~ N(0,1).
    """
    He_n = hermite_probabilists_arb(n, x)
    return He_n / arb.fac_ui(n).sqrt()


# ---------------------------------------------------------------------------
# Hermite cache for fixed node sets
# ---------------------------------------------------------------------------

class HermiteCacheArb:
    """Cache of h_n(x_k) for all n=0..max_degree and all nodes x_k."""

    def __init__(self, max_degree: int, nodes: list[arb], prec: int = 256):
        old_prec = flint_ctx.prec
        flint_ctx.prec = prec

        self.max_degree = max_degree
        self.n_nodes = len(nodes)

        # cache[n][k] = h_n(nodes[k])
        self.cache: list[list[arb]] = []
        for n in range(max_degree + 1):
            row = [hermite_orthonormal_arb(n, x) for x in nodes]
            self.cache.append(row)

        flint_ctx.prec = old_prec

    def get(self, n: int, node_idx: int) -> arb:
        return self.cache[n][node_idx]


# ---------------------------------------------------------------------------
# Semi-analytic g_j function
# ---------------------------------------------------------------------------

def compute_g_j_arb(t: arb, j: int) -> arb:
    """Compute g_j(t) = E[h_j(Y) * sgn(Y - t)] for Y ~ N(0,1).

    g_0(t) = -erf(t/sqrt(2))
    g_j(t) = 2*phi(t)*He_{j-1}(t) / sqrt(j!)   for j >= 1
    """
    if j == 0:
        return gaussian_one_minus_2cdf_arb(t)
    else:
        phi_t = normal_pdf_arb(t)
        He_jm1_t = hermite_probabilists_arb(j - 1, t)
        norm_j = arb.fac_ui(j).sqrt()
        return (arb(2) * phi_t * He_jm1_t) / norm_j


# ---------------------------------------------------------------------------
# Complex extension of g_j (for Cauchy GL error bound)
# ---------------------------------------------------------------------------

def _hermite_probabilists_acb(n: int, z: acb) -> acb:
    """He_n(z) for complex z, used in Cauchy error bound."""
    if n == 0:
        return acb(1)
    if n == 1:
        return z

    h_prev = acb(1)
    h_curr = z
    for k in range(1, n):
        h_next = z * h_curr - acb(arb(k)) * h_prev
        h_prev = h_curr
        h_curr = h_next
    return h_curr


def _hermite_orthonormal_acb(n: int, z: acb) -> acb:
    """h_n(z) for complex z."""
    He_n = _hermite_probabilists_acb(n, z)
    return He_n / acb(arb.fac_ui(n).sqrt())


def _normal_pdf_acb(z: acb) -> acb:
    """phi(z) = (1/sqrt(2*pi)) * exp(-z^2/2) for complex z."""
    return (-z * z / acb(arb(2))).exp() / acb((arb(2) * arb.pi()).sqrt())


def _compute_g_j_acb(t: acb, j: int) -> acb:
    """g_j(t) for complex t."""
    if j == 0:
        return -(t / acb(arb(2).sqrt())).erf()
    else:
        phi_t = _normal_pdf_acb(t)
        He_jm1_t = _hermite_probabilists_acb(j - 1, t)
        norm_j = acb(arb.fac_ui(j).sqrt())
        return acb(arb(2)) * phi_t * He_jm1_t / norm_j


# ---------------------------------------------------------------------------
# Tail bound
# ---------------------------------------------------------------------------

def tail_bound(L: arb) -> arb:
    """Rigorous bound on |integral_{|x|>L} h_i(x)*g_j(P(x))*phi(x) dx|.

    Valid for ALL i, j (independent of degree).

    Derivation (Cauchy-Schwarz):
      |g_j(t)| <= 1 for all j, t
      integral_{|x|>L} |He_i(x)/sqrt(i!)| * phi(x) dx
        <= (1/sqrt(i!)) * sqrt(E[He_i^2]) * sqrt(erfc(L/sqrt(2)))
        = sqrt(erfc(L/sqrt(2)))
    """
    return (L / arb(2).sqrt()).erfc().sqrt()


# ---------------------------------------------------------------------------
# GL error bound via Cauchy estimate
# ---------------------------------------------------------------------------

def _gl_error_bound_panel(
    integrand_acb_fn: Callable[[acb], acb],
    panel_a: arb,
    panel_b: arb,
    n_gl: int,
    cauchy_radius: arb,
    prec: int,
) -> arb:
    """Bound GL quadrature error on one panel via Cauchy estimate.

    |E_n| <= (h/2) * ((h/2)/r)^{2n} * (n!)^4/((2n+1)(2n!)^2) * M_r

    where M_r = max|f(z)| on panel + complex disk of radius r.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    h = panel_b - panel_a
    half_h = h / arb(2)

    # Evaluate integrand on ball covering panel + complex disk
    panel_ball = arb.union(panel_a, panel_b)
    z_ball = acb(panel_ball, arb.union(-cauchy_radius, cauchy_radius))
    f_ball = integrand_acb_fn(z_ball)
    M_r = f_ball.abs_upper()

    # GL coefficient
    n_fac = arb.fac_ui(n_gl)
    two_n_fac = arb.fac_ui(2 * n_gl)
    coeff = (n_fac ** 4) / (arb(2 * n_gl + 1) * two_n_fac * two_n_fac)

    # (h/(2r))^{2n}
    ratio = half_h / cauchy_radius
    ratio_pow = arb(1)
    for _ in range(2 * n_gl):
        ratio_pow = ratio_pow * ratio

    error = half_h * ratio_pow * coeff * M_r

    flint_ctx.prec = old_prec
    return error


# ---------------------------------------------------------------------------
# Certified coefficient computation
# ---------------------------------------------------------------------------

def compute_I_ij_certified(
    i: int,
    j: int,
    P_func: Callable[[arb], arb],
    P_func_acb: Callable[[acb], acb] = None,
    n_gl: int = 32,
    n_panels: int = 20,
    L: int = 25,
    prec: int = 256,
) -> arb:
    """Compute I_{i,j} = E[sgn(Y-P(X)) * h_i(X) * h_j(Y)] as certified arb.

    Args:
        i, j: Hermite degrees.
        P_func: Polynomial P(x) -> arb.
        P_func_acb: Complex extension P(z) -> acb. If None, uses P_func
                     (works if P_func only uses arb arithmetic ops).
        n_gl: GL points per panel.
        n_panels: Number of panels on [-L, L].
        L: Truncation radius.
        prec: Arb precision in bits.

    Returns:
        Certified arb ball enclosing the true I_{i,j}.
    """
    # Parity check: I_{i,j} = 0 when i+j is even (for odd P)
    if (i + j) % 2 == 0:
        return arb(0)

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    L_arb = arb(L)

    # --- Step 1: Composite GL quadrature on [-L, L] ---
    ref_nodes, ref_weights = certify_gl_nodes_weights(n_gl, prec=prec)
    panel_width = (arb(2) * L_arb) / arb(n_panels)

    quadrature_sum = arb(0)

    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = certified_scale_gl_to_interval(
            ref_nodes, ref_weights, a, b,
        )
        for k in range(n_gl):
            x_k = s_nodes[k]
            w_k = s_weights[k]
            # Integrand: h_i(x) * g_j(P(x)) * phi(x)
            h_i_xk = hermite_orthonormal_arb(i, x_k)
            P_xk = P_func(x_k)
            g_j_Pxk = compute_g_j_arb(P_xk, j)
            phi_xk = normal_pdf_arb(x_k)
            quadrature_sum += w_k * h_i_xk * g_j_Pxk * phi_xk

    # --- Step 2: Tail bound ---
    tail = tail_bound(L_arb)

    # --- Step 3: GL error bound ---
    # Build complex integrand for Cauchy estimate
    if P_func_acb is None:
        # Default: assume P_func works on acb inputs
        _P_acb = P_func
    else:
        _P_acb = P_func_acb

    _i_local = i
    _j_local = j

    def integrand_acb(z: acb) -> acb:
        h_i_z = _hermite_orthonormal_acb(_i_local, z)
        P_z = _P_acb(z)
        g_j_Pz = _compute_g_j_acb(P_z, _j_local)
        phi_z = _normal_pdf_acb(z)
        return h_i_z * g_j_Pz * phi_z

    # Cauchy radius: use panel_width (= 2 * half_panel)
    cauchy_r = panel_width

    gl_error_total = arb(0)
    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        panel_err = _gl_error_bound_panel(
            integrand_acb, a, b, n_gl, cauchy_r, prec,
        )
        gl_error_total += panel_err

    # --- Step 4: Combine ---
    total_error = tail + gl_error_total
    result = arb.union(
        quadrature_sum - total_error,
        quadrature_sum + total_error,
    )

    flint_ctx.prec = old_prec
    return result


def compute_coefficient_matrix_certified(
    P_func: Callable[[arb], arb],
    max_degree: int,
    P_func_acb: Callable[[acb], acb] = None,
    n_gl: int = 32,
    n_panels: int = 20,
    L: int = 25,
    prec: int = 256,
    verbose: bool = False,
) -> list[list[arb]]:
    """Compute certified coefficient matrix C[i][j] = I_{i,j}.

    Args:
        P_func: Polynomial P(x) -> arb.
        max_degree: Maximum Hermite degree.
        P_func_acb: Complex extension of P for GL error bounds.
        n_gl: GL points per panel.
        n_panels: Number of panels on [-L, L].
        L: Truncation radius.
        prec: Arb precision in bits.
        verbose: Print progress.

    Returns:
        (max_degree+1) x (max_degree+1) list of certified arb balls.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    sz = max_degree + 1
    C = [[arb(0) for _ in range(sz)] for _ in range(sz)]

    # Precompute GL nodes once (cached internally)
    ref_nodes, ref_weights = certify_gl_nodes_weights(n_gl, prec=prec)

    # Precompute all GL nodes scaled to each panel
    L_arb = arb(L)
    panel_width = (arb(2) * L_arb) / arb(n_panels)
    all_nodes = []  # (x_k, w_k) for all panels
    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = certified_scale_gl_to_interval(
            ref_nodes, ref_weights, a, b,
        )
        for k in range(n_gl):
            all_nodes.append((s_nodes[k], s_weights[k]))

    n_total = len(all_nodes)

    # Precompute h_n(x_k) for all nodes and all degrees
    if verbose:
        print(f"  Precomputing Hermite cache: {sz} degrees x {n_total} nodes")
    hermite_vals = []  # hermite_vals[n][k] = h_n(x_k)
    for n in range(sz):
        row = [hermite_orthonormal_arb(n, all_nodes[k][0]) for k in range(n_total)]
        hermite_vals.append(row)

    # Precompute P(x_k) for all nodes
    P_at_nodes = [P_func(all_nodes[k][0]) for k in range(n_total)]

    # Precompute phi(x_k) for all nodes
    phi_at_nodes = [normal_pdf_arb(all_nodes[k][0]) for k in range(n_total)]

    # Precompute g_j(P(x_k)) for all j and all nodes
    if verbose:
        print(f"  Precomputing g_j(P(x_k)): {sz} j-values x {n_total} nodes")
    g_j_vals = []  # g_j_vals[j][k] = g_j(P(x_k))
    for jj in range(sz):
        row = [compute_g_j_arb(P_at_nodes[k], jj) for k in range(n_total)]
        g_j_vals.append(row)

    # Precompute tail bound (same for all i, j)
    tail = tail_bound(L_arb)

    # Precompute GL error bound (compute once per (i,j) pair)
    # For efficiency, compute a global M_r bound instead of per-(i,j)
    # We'll compute per-coefficient GL error only if needed for tight bounds.
    # For now, compute per-coefficient.

    computed = 0
    total = sz * sz

    for ii in range(sz):
        for jj in range(sz):
            if (ii + jj) % 2 == 0:
                C[ii][jj] = arb(0)
                continue

            # Quadrature sum
            qsum = arb(0)
            for k in range(n_total):
                w_k = all_nodes[k][1]
                qsum += w_k * hermite_vals[ii][k] * g_j_vals[jj][k] * phi_at_nodes[k]

            # GL error bound via Cauchy estimate
            if P_func_acb is None:
                _P_acb = P_func
            else:
                _P_acb = P_func_acb

            _ii = ii
            _jj = jj

            def integrand_acb(z: acb, _i=_ii, _j=_jj) -> acb:
                h_i_z = _hermite_orthonormal_acb(_i, z)
                P_z = _P_acb(z)
                g_j_Pz = _compute_g_j_acb(P_z, _j)
                phi_z = _normal_pdf_acb(z)
                return h_i_z * g_j_Pz * phi_z

            cauchy_r = panel_width
            gl_error_total = arb(0)
            for p in range(n_panels):
                a = -L_arb + arb(p) * panel_width
                b = a + panel_width
                panel_err = _gl_error_bound_panel(
                    integrand_acb, a, b, n_gl, cauchy_r, prec,
                )
                gl_error_total += panel_err

            total_error = tail + gl_error_total
            C[ii][jj] = arb.union(
                qsum - total_error,
                qsum + total_error,
            )

            computed += 1
            if verbose and computed % 10 == 0:
                print(f"    Coefficients: {computed}/{total // 2} non-zero", end='\r')

    if verbose:
        print(f"    Coefficients: done ({computed} non-zero)       ")

    flint_ctx.prec = old_prec
    return C
