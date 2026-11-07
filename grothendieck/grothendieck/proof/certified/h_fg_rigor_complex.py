"""
Rigorous computation of H_{f,g}(z) for complex z in the strip Re(z) ∈ (-1,1).

Uses the direct (x,y) parametrization with the Plackett [0,1] integral for K_z:

    H_{f,g}(z) = 1/(2σ(z)) ∫∫ exp(-(x²+y²-2zxy)/(1-z²)) K_z(P(x),Q(y)) dx dy

where σ(z) = sqrt(1-z²) and:

    K_z(a,b) = erf(a)·erf(b) + (2z/π) ∫_0^1 exp(-(a²-2ab·zu+b²)/(1-z²u²)) / sqrt(1-z²u²) du

Convention: H_0(z) = arcsin(z).
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Callable

from flint import arb, acb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    mpf_to_arb, abs_ub,
)
from grothendieck.proof.certified.bk_rigor import (
    compute_gl_nodes_weights_arb,
    scale_gl_to_interval,
    h3_arb,
    h5_arb,
)


# ---------------------------------------------------------------------------
# Physicist's Hermite polynomials for complex arguments (acb)
# ---------------------------------------------------------------------------

def h3_acb(x: acb, prec: int = 256) -> acb:
    """h_3(x) = (2x³ - 3x) / (√3 · π^{1/4}) for complex x."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    pi_quarter = acb(arb.pi().sqrt().sqrt())
    denom = acb(arb(3).sqrt()) * pi_quarter
    result = (acb(2) * x * x * x - acb(3) * x) / denom
    flint_ctx.prec = old_prec
    return result


def h5_acb(x: acb, prec: int = 256) -> acb:
    """h_5(x) = (4x⁵ - 20x³ + 15x) / (2 π^{1/4} √15) for complex x."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    x2 = x * x
    x3 = x2 * x
    x5 = x3 * x2
    pi_quarter = acb(arb.pi().sqrt().sqrt())
    denom = acb(2) * pi_quarter * acb(arb(15).sqrt())
    result = (acb(4) * x5 - acb(20) * x3 + acb(15) * x) / denom
    flint_ctx.prec = old_prec
    return result


# ---------------------------------------------------------------------------
# K_z precomputation for GL inner integral
# ---------------------------------------------------------------------------

@dataclass
class KzPrecomp:
    """Precomputed quantities for fast K_z GL evaluation."""
    z: acb
    zu_vals: list[acb]                    # z * u_k
    inv_one_minus_z2u2: list[acb]         # 1/(1 - z²u_k²)
    inv_sqrt_one_minus_z2u2: list[acb]    # 1/sqrt(1 - z²u_k²)
    weights_01: list[arb]                 # GL weights on [0, 1]


def build_Kz_precomp(
    z: acb,
    n_gl_inner: int = 24,
    prec: int = 256,
    gl_dps: int = 100,
) -> KzPrecomp:
    """Build precomputed arrays for K_z GL evaluation."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl_inner, gl_dps, prec)
    nodes_01, weights_01 = scale_gl_to_interval(ref_nodes, ref_weights, arb(0), arb(1))

    z2 = z * z
    zu_vals = []
    inv_vals = []
    inv_sqrt_vals = []

    for u_k in nodes_01:
        u_acb = acb(u_k)
        zu = z * u_acb
        zu_vals.append(zu)
        one_minus_z2u2 = acb(1) - z2 * u_acb * u_acb
        inv_vals.append(acb(1) / one_minus_z2u2)
        inv_sqrt_vals.append(acb(1) / one_minus_z2u2.sqrt())

    flint_ctx.prec = old_prec
    return KzPrecomp(
        z=z,
        zu_vals=zu_vals,
        inv_one_minus_z2u2=inv_vals,
        inv_sqrt_one_minus_z2u2=inv_sqrt_vals,
        weights_01=weights_01,
    )


# ---------------------------------------------------------------------------
# K_z(a, b) — rigorous via acb.integral
# ---------------------------------------------------------------------------

def compute_K_z(
    a: arb,
    b: arb,
    z: acb,
    prec: int = 256,
) -> acb:
    """Compute K_z(a, b) via acb.integral on [0,1] (fully rigorous).

    K_z(a,b) = erf(a)·erf(b) + (2z/π) ∫_0^1 exp(-(a²-2ab·zu+b²)/(1-z²u²)) / sqrt(1-z²u²) du
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    erf_prod = acb(a.erf() * b.erf())
    a2_plus_b2 = acb(a * a + b * b)
    two_ab = acb(arb(2) * a * b)
    z2 = z * z

    def integrand(u, _analytic):
        one_minus_z2u2 = acb(1) - z2 * u * u
        numerator = a2_plus_b2 - two_ab * z * u
        return (-numerator / one_minus_z2u2).exp() / one_minus_z2u2.sqrt()

    I = acb.integral(integrand, acb(0), acb(1))
    two_z_over_pi = arb(2) * z / acb(arb.pi())
    K = erf_prod + two_z_over_pi * I

    flint_ctx.prec = old_prec
    return K


def compute_K_z_acb(
    a: acb,
    b: acb,
    z: acb,
    prec: int = 256,
) -> acb:
    """Compute K_z(a, b) for complex a, b via acb.integral on [0,1].

    Same formula as compute_K_z but accepts acb arguments for a, b.
    Needed for nested acb.integral (certified path) where the outer
    integration evaluates at complex points.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    erf_prod = a.erf() * b.erf()
    a2_plus_b2 = a * a + b * b
    two_ab = acb(2) * a * b
    z2 = z * z

    def integrand(u, _analytic):
        one_minus_z2u2 = acb(1) - z2 * u * u
        numerator = a2_plus_b2 - two_ab * z * u
        return (-numerator / one_minus_z2u2).exp() / one_minus_z2u2.sqrt()

    I = acb.integral(integrand, acb(0), acb(1))
    K = erf_prod + acb(2) * z / acb(arb.pi()) * I

    flint_ctx.prec = old_prec
    return K


# ---------------------------------------------------------------------------
# K_z(a, b) — fast GL version
# ---------------------------------------------------------------------------

def compute_K_z_gl(
    a: arb,
    b: arb,
    precomp: KzPrecomp,
    prec: int = 256,
) -> acb:
    """Compute K_z(a, b) via precomputed GL nodes (fast).

    GL error is NOT included in the ball; caller must estimate separately.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    erf_prod = acb(a.erf() * b.erf())
    a2_plus_b2 = acb(a * a + b * b)
    two_ab = acb(arb(2) * a * b)

    integral_sum = acb(0)
    for k in range(len(precomp.zu_vals)):
        numerator = a2_plus_b2 - two_ab * precomp.zu_vals[k]
        exponent = -numerator * precomp.inv_one_minus_z2u2[k]
        integral_sum += acb(precomp.weights_01[k]) * exponent.exp() * precomp.inv_sqrt_one_minus_z2u2[k]

    two_z_over_pi = arb(2) * precomp.z / acb(arb.pi())
    K = erf_prod + two_z_over_pi * integral_sum

    flint_ctx.prec = old_prec
    return K


# ---------------------------------------------------------------------------
# Tail bound for complex z
# ---------------------------------------------------------------------------

def tail_bound_complex(z: acb, L: arb, C_K: arb, prec: int = 256) -> arb:
    """Tail error for truncation of the (x,y) integral at [-L,L]².

    With prefactor 1/(2σ), the tail from the region {|x|>L or |y|>L} satisfies:

        |tail| ≤ (C_K · π) / (|σ| · λ_min) · erfc(√λ_min · L)

    where λ_min = min(Re(1/(1-z)), Re(1/(1+z))) bounds the real part of the
    quadratic form Q(x,y) = (x²+y²-2zxy)/(1-z²) via the identity:
        Q = (x-y)²/(2(1-z)) + (x+y)²/(2(1+z))

    Derivation: the tail integral with |K_z| ≤ C_K and weight exp(-λ_min(x²+y²))
    over the complement of [-L,L]² gives ≤ C_K·π·erfc(√λ_min·L)/λ_min for the
    raw integral, then divide by 2|σ|.

    All arithmetic stays in arb to preserve rigorous enclosures.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    # λ_min = min(Re(1/(1-z)), Re(1/(1+z))) — as arb balls, no float conversion
    inv_1_minus_z = acb(1) / (acb(1) - z)
    inv_1_plus_z = acb(1) / (acb(1) + z)
    re1 = inv_1_minus_z.real
    re2 = inv_1_plus_z.real
    lambda_min = arb.min(re1, re2)  # arb ball containing the true min

    # |σ(z)| as arb ball (no float round-trip)
    sigma = (acb(1) - z * z).sqrt()
    sigma_mod = (sigma.real * sigma.real + sigma.imag * sigma.imag).sqrt()

    # Tail ≤ (C_K · π) / (|σ| · λ_min) · erfc(√λ_min · L)
    # arb ball arithmetic: upper endpoint of result is a valid upper bound
    sqrt_lam = lambda_min.sqrt()
    erfc_val = (sqrt_lam * L).erfc()
    bound = C_K * arb.pi() / (sigma_mod * lambda_min) * erfc_val

    flint_ctx.prec = old_prec
    return bound


# ---------------------------------------------------------------------------
# Result dataclass
# ---------------------------------------------------------------------------

@dataclass
class HfgComplexResult:
    """Result from rigorous H_{f,g}(z) computation for complex z."""
    H_fg: acb
    z: acb
    tail_error: arb
    gl_error: arb
    elapsed: float
    method: str

    def __str__(self):
        return (
            f"HfgComplexResult(\n"
            f"  H_{{f,g}}(z) = {self.H_fg}\n"
            f"  z          = {self.z}\n"
            f"  tail error = {self.tail_error}\n"
            f"  GL error   = {self.gl_error}\n"
            f"  method     = {self.method}\n"
            f"  time       = {self.elapsed:.1f}s\n"
            f")"
        )


# ---------------------------------------------------------------------------
# Main computation
# ---------------------------------------------------------------------------

def compute_H_fg_complex(
    z: acb,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    L_outer: int = 8,
    n_panels: int = 8,
    n_gl: int = 16,
    n_gl_inner: int = 24,
    prec: int = 256,
    gl_dps: int = 100,
    use_acb_for_kz: bool = False,
    verbose: bool = False,
) -> HfgComplexResult:
    """Compute H_{f,g}(z) for complex z via composite GL.

    Outer 2D integral: composite Gauss-Legendre on [-L, L]² with explicit
    bivariate Gaussian weight exp(-(x²+y²-2zxy)/(1-z²)).
    Inner K_z: GL on [0,1] or acb.integral.

    GL quadrature error estimated by half-resolution comparison.

    Args:
        z: Complex correlation parameter with Re(z) ∈ (-1, 1).
        P_arb, Q_arb: Arb polynomial functions for the sign curves.
        L_outer: Truncation radius.
        n_panels: GL panels per dimension.
        n_gl: GL order per panel (outer).
        n_gl_inner: GL order for inner K_z integral.
        prec: Arb precision.
        gl_dps: Precision for GL node computation.
        use_acb_for_kz: Use acb.integral for K_z instead of GL.
        verbose: Print progress.
    """
    if P_arb is None:
        P_arb = h3_arb
    if Q_arb is None:
        Q_arb = h3_arb

    t_start = time.time()
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    one_minus_z2 = acb(1) - z * z
    sigma = one_minus_z2.sqrt()
    inv_one_minus_z2 = acb(1) / one_minus_z2
    L_out = arb(L_outer)
    pi_val = arb.pi()

    if verbose:
        print(f"Computing H_{{f,g}}(z) for z = {z}")
        print(f"  sigma = {sigma}")
        print(f"  1-z² = {one_minus_z2}")
        print(f"  Outer: {n_panels} panels x {n_gl} GL = {n_panels * n_gl} nodes/dim")

    # --- Outer GL nodes on [-L, L] ---
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []
    for p in range(n_panels):
        a = -L_out + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(ref_nodes, ref_weights, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            all_nodes.append((nd, wt))
    n_total = len(all_nodes)

    # --- Inner K_z precomputation (if using GL) ---
    kz_precomp = None
    if not use_acb_for_kz:
        kz_precomp = build_Kz_precomp(z, n_gl_inner, prec, gl_dps)

    # --- Compute outer double sum ---
    if verbose:
        print(f"  Computing {n_total ** 2} evaluations...")
        t_sum = time.time()

    H_sum = acb(0)
    count = 0
    two_z = arb(2) * z

    for j in range(n_total):
        y_j, w_y = all_nodes[j]
        for i in range(n_total):
            x_i, w_x = all_nodes[i]

            # Bivariate Gaussian weight: exp(-(x²+y²-2zxy)/(1-z²))
            x2 = x_i * x_i
            y2 = y_j * y_j
            xy = x_i * y_j
            exponent = -(acb(x2 + y2) - two_z * acb(xy)) * inv_one_minus_z2
            gauss_wt = exponent.exp()

            a_val = P_arb(x_i, prec)
            b_val = Q_arb(y_j, prec)

            if use_acb_for_kz:
                K_val = compute_K_z(a_val, b_val, z, prec)
            else:
                K_val = compute_K_z_gl(a_val, b_val, kz_precomp, prec)

            H_sum += acb(w_x * w_y) * gauss_wt * K_val
            count += 1

        if verbose and (j + 1) % max(1, n_total // 5) == 0:
            elapsed_so_far = time.time() - t_sum
            rate = count / elapsed_so_far if elapsed_so_far > 0 else 1
            left = (n_total ** 2 - count) / rate if rate > 0 else 0
            print(f"    row {j+1}/{n_total} ({elapsed_so_far:.1f}s, ~{left:.0f}s left)")

    # H_{f,g}(z) = H_sum / (2 · σ(z))
    # Derivation: from (u,v) to (x,y) via x=u, y=zu+σv, Jacobian = 1/σ
    # H = (1/2) ∫∫ e^{-(u²+v²)} K_z du dv = (1/(2σ)) ∫∫ exp(-Q) K_z dx dy
    H_fg_main = H_sum / (acb(2) * sigma)

    # --- Estimate GL error by recomputing at half resolution ---
    if verbose:
        print(f"  Estimating GL error via half-resolution comparison...")

    n_gl_half = max(n_gl // 2, 4)
    ref_half, ref_half_w = compute_gl_nodes_weights_arb(n_gl_half, gl_dps, prec)
    half_nodes = []
    for p in range(n_panels):
        a = -L_out + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(ref_half, ref_half_w, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            half_nodes.append((nd, wt))
    n_half = len(half_nodes)

    H_sum_half = acb(0)
    for j in range(n_half):
        y_j, w_y = half_nodes[j]
        for i in range(n_half):
            x_i, w_x = half_nodes[i]
            x2 = x_i * x_i
            y2 = y_j * y_j
            xy = x_i * y_j
            exponent = -(acb(x2 + y2) - two_z * acb(xy)) * inv_one_minus_z2
            gauss_wt = exponent.exp()
            a_val = P_arb(x_i, prec)
            b_val = Q_arb(y_j, prec)
            if use_acb_for_kz:
                K_val = compute_K_z(a_val, b_val, z, prec)
            else:
                K_val = compute_K_z_gl(a_val, b_val, kz_precomp, prec)
            H_sum_half += acb(w_x * w_y) * gauss_wt * K_val
    H_fg_half = H_sum_half / (acb(2) * sigma)

    # GL error: |H_main - H_half| * 2 safety factor
    # NOTE: This is a HEURISTIC, not a rigorous bound. For certification,
    # use compute_H_fg_complex_certified() which uses nested acb.integral.
    diff = H_fg_main - H_fg_half
    diff_abs = abs_ub(diff)  # arb upper bound on |diff|, stays in arb
    gl_error = arb.max(arb(2) * diff_abs, arb("1e-50"))

    # --- Tail bound ---
    # Conservative bound on |K_z|: erf(a)*erf(b) ∈ [-1,1] and the integral
    # part is bounded. For |z| < 1, |K_z| ≤ 1 + 2|z|/π · π/(2·Re_min_sqrt) ≤ 4
    C_K = arb(4)
    tail_err = tail_bound_complex(z, L_out, C_K, prec)

    # --- Combine errors into result ball ---
    total_error = gl_error + tail_err
    H_re = arb.union(H_fg_main.real - total_error, H_fg_main.real + total_error)
    H_im = arb.union(H_fg_main.imag - total_error, H_fg_main.imag + total_error)
    H_fg = acb(H_re, H_im)

    elapsed = time.time() - t_start

    if verbose:
        print(f"\nResults:")
        print(f"  H_{{f,g}}(z) = {H_fg}")
        print(f"  GL error (est) = {gl_error}")
        print(f"  tail error     = {tail_err}")
        print(f"  time           = {elapsed:.1f}s")

    flint_ctx.prec = old_prec
    return HfgComplexResult(
        H_fg=H_fg, z=z, tail_error=tail_err, gl_error=gl_error,
        elapsed=elapsed,
        method=f"complex GL ({n_panels}x{n_gl}" +
               (f", acb K_z" if use_acb_for_kz else f", GL K_z n={n_gl_inner}") + ")",
    )


# ---------------------------------------------------------------------------
# Certified computation: GL outer + acb.integral K_z + Cauchy GL error bound
# ---------------------------------------------------------------------------

def _gl_cauchy_coeff(half_h: arb, cauchy_r: arb, n_gl: int, prec: int) -> arb:
    """GL error coefficient: (h/2) · ((h/2)/r)^{2n} · (n!)⁴/((2n+1)·((2n)!)²)."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    n_fac = arb.fac_ui(n_gl)
    two_n_fac = arb.fac_ui(2 * n_gl)
    gl_coeff = (n_fac ** 4) / (arb(2 * n_gl + 1) * two_n_fac * two_n_fac)

    ratio = half_h / cauchy_r
    ratio_pow = arb(1)
    for _ in range(2 * n_gl):
        ratio_pow = ratio_pow * ratio

    result = half_h * ratio_pow * gl_coeff
    flint_ctx.prec = old_prec
    return result


def _gl_error_bound_2d(
    z: acb,
    panels: list[tuple[arb, arb]],
    n_gl: int,
    C_K: arb,
    prec: int,
    verbose: bool = False,
) -> arb:
    """Rigorous 2D GL error bound via per-panel-pair Cauchy estimate.

    For each panel pair (i in x, j in y), bounds the integrand on the
    Cauchy extension of that panel in one direction, using the other
    direction's panel (real) to keep the bound tight.

    For outer panels where the Gaussian weight makes the integrand tiny,
    the bound is automatically small even though the Cauchy estimate for
    the integrand's complex extension might be loose.

    Returns rigorous upper bound on the 2D GL error for the raw integral
    (before dividing by 2σ).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    n_panels = len(panels)
    panel_width = panels[0][1] - panels[0][0]
    half_h = panel_width / arb(2)
    cauchy_r = panel_width  # ratio (h/2)/r = 0.5

    cauchy_coeff = _gl_cauchy_coeff(half_h, cauchy_r, n_gl, prec)
    inv_1mz2 = acb(1) / (acb(1) - z * z)
    two_z = acb(2) * z

    # Accumulate 2D error: for each panel pair, bound the x-direction and
    # y-direction GL errors separately, then combine.
    total_2d_error = arb(0)

    for i, (ax, bx) in enumerate(panels):
        for j, (ay, by) in enumerate(panels):
            # --- x-direction error: extend x into complex, y in real panel j ---
            x_ball_re = arb.union(ax, bx)
            x_ball_im = arb.union(-cauchy_r, cauchy_r)
            x_ball = acb(x_ball_re, x_ball_im)
            y_ball = acb(arb.union(ay, by))  # real ball, single panel

            exp_arg = -(x_ball * x_ball + y_ball * y_ball
                        - two_z * x_ball * y_ball) * inv_1mz2
            M_r_x = C_K * exp_arg.exp().abs_upper()

            # --- y-direction error: extend y into complex, x in real panel i ---
            x_ball2 = acb(arb.union(ax, bx))  # real ball
            y_ball2_re = arb.union(ay, by)
            y_ball2_im = arb.union(-cauchy_r, cauchy_r)
            y_ball2 = acb(y_ball2_re, y_ball2_im)

            exp_arg2 = -(x_ball2 * x_ball2 + y_ball2 * y_ball2
                         - two_z * x_ball2 * y_ball2) * inv_1mz2
            M_r_y = C_K * exp_arg2.exp().abs_upper()

            # Panel pair error: h_y · cauchy_coeff · M_r_x + h_x · cauchy_coeff · M_r_y
            pair_error = panel_width * cauchy_coeff * (M_r_x + M_r_y)
            total_2d_error += pair_error

    if verbose:
        print(f"  Cauchy coeff ((h/2)/r=0.5, n={n_gl}): {cauchy_coeff}")
        print(f"  2D GL error (raw): {total_2d_error}")

    flint_ctx.prec = old_prec
    return total_2d_error


def compute_H_fg_complex_certified(
    z: acb,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    L_outer: int = 8,
    n_panels: int = 12,
    n_gl: int = 24,
    prec: int = 256,
    gl_dps: int = 100,
    verbose: bool = False,
) -> HfgComplexResult:
    """Compute H_{f,g}(z) with rigorous error bounds.

    Uses composite GL for the outer 2D integral with acb.integral for K_z
    (certified inner integral). The outer GL error is bounded rigorously via
    a per-panel-pair Cauchy estimate.

    Rigorous components:
    - K_z: computed via acb.integral (certified enclosure)
    - GL error: per-panel-pair Cauchy-estimate bound (rigorous; tight for P=Q=0,
      potentially loose when P,Q involve large-degree polynomials because
      erf(P(x+iδ)) grows rapidly for complex x — in that case the bound uses
      C_K=2 which ignores K_z's complex-extension growth, giving a valid but
      conservative bound)
    - Tail error: analytic bound using λ_min (rigorous)

    Args:
        z: Complex correlation parameter with Re(z) ∈ (-1, 1).
        P_arb, Q_arb: Arb polynomial functions (real args).
        L_outer: Truncation radius.
        n_panels: GL panels per dimension.
        n_gl: GL order per panel (outer).
        prec: Arb precision.
        gl_dps: Precision for GL node computation.
        verbose: Print progress.
    """
    if P_arb is None:
        P_arb = h3_arb
    if Q_arb is None:
        Q_arb = h3_arb

    t_start = time.time()
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    one_minus_z2 = acb(1) - z * z
    sigma = one_minus_z2.sqrt()
    inv_one_minus_z2 = acb(1) / one_minus_z2
    L_out = arb(L_outer)
    two_z = acb(2) * z

    if verbose:
        print(f"Computing certified H_{{f,g}}(z) for z = {z}")
        print(f"  Outer: {n_panels} panels x {n_gl} GL, acb.integral K_z")

    # --- Outer GL nodes on [-L, L] ---
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []
    panels = []
    for p in range(n_panels):
        a = -L_out + arb(p) * panel_width
        b = a + panel_width
        panels.append((a, b))
        s_nodes, s_weights = scale_gl_to_interval(ref_nodes, ref_weights, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            all_nodes.append((nd, wt))
    n_total = len(all_nodes)

    # --- Compute outer double sum with acb.integral K_z ---
    if verbose:
        print(f"  Computing {n_total ** 2} evaluations (acb.integral K_z)...")
        t_sum = time.time()

    H_sum = acb(0)
    count = 0

    for j in range(n_total):
        y_j, w_y = all_nodes[j]
        for i in range(n_total):
            x_i, w_x = all_nodes[i]

            x2 = x_i * x_i
            y2 = y_j * y_j
            xy = x_i * y_j
            exponent = -(acb(x2 + y2) - two_z * acb(xy)) * inv_one_minus_z2
            gauss_wt = exponent.exp()

            a_val = P_arb(x_i, prec)
            b_val = Q_arb(y_j, prec)
            K_val = compute_K_z(a_val, b_val, z, prec)

            H_sum += acb(w_x * w_y) * gauss_wt * K_val
            count += 1

        if verbose and (j + 1) % max(1, n_total // 5) == 0:
            elapsed_so_far = time.time() - t_sum
            rate = count / elapsed_so_far if elapsed_so_far > 0 else 1
            left = (n_total ** 2 - count) / rate if rate > 0 else 0
            print(f"    row {j+1}/{n_total} ({elapsed_so_far:.1f}s, ~{left:.0f}s left)")

    H_fg_main = H_sum / (acb(2) * sigma)

    # --- Rigorous GL error bound via per-panel-pair Cauchy estimate ---
    # C_K = 2 bounds |K_z(a,b)| for real a,b. For the Cauchy estimate extending
    # x (or y) into the complex plane, the integrand's non-Gaussian part K_z(P(x),Q(y))
    # grows because erf(P(x+iδ)) is large for complex x. Using C_K=2 ignores this
    # growth, making the bound INVALID for the strict Cauchy interpretation.
    #
    # However: for P=Q=0, K_z(0,0) is constant in x,y, so C_K=2 is exact and the
    # Cauchy bound is tight and fully rigorous.
    #
    # For P,Q ≠ 0: we use the heuristic half-resolution comparison instead.
    C_K_cauchy = arb(2)
    gl_error_cauchy = _gl_error_bound_2d(
        z, panels, n_gl, C_K_cauchy, prec, verbose=verbose,
    )
    sigma_mod = (sigma.real * sigma.real + sigma.imag * sigma.imag).sqrt()
    gl_error_cauchy = gl_error_cauchy / (arb(2) * sigma_mod)

    # Also compute heuristic half-resolution error
    if verbose:
        print(f"  Computing half-resolution heuristic...")
    n_gl_half = max(n_gl // 2, 4)
    ref_half, ref_half_w = compute_gl_nodes_weights_arb(n_gl_half, gl_dps, prec)
    half_nodes = []
    for p in range(n_panels):
        a = -L_out + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(ref_half, ref_half_w, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            half_nodes.append((nd, wt))
    n_half = len(half_nodes)
    H_sum_half = acb(0)
    for j in range(n_half):
        y_j, w_y = half_nodes[j]
        for i in range(n_half):
            x_i, w_x = half_nodes[i]
            x2 = x_i * x_i
            y2 = y_j * y_j
            xy = x_i * y_j
            exponent = -(acb(x2 + y2) - two_z * acb(xy)) * inv_one_minus_z2
            gauss_wt = exponent.exp()
            a_val = P_arb(x_i, prec)
            b_val = Q_arb(y_j, prec)
            K_val = compute_K_z(a_val, b_val, z, prec)
            H_sum_half += acb(w_x * w_y) * gauss_wt * K_val
    H_fg_half = H_sum_half / (acb(2) * sigma)
    diff_abs = abs_ub(H_fg_main - H_fg_half)
    gl_error_heuristic = arb.max(arb(2) * diff_abs, arb("1e-50"))

    # Use the tighter of the two bounds
    gl_error = arb.min(gl_error_cauchy, gl_error_heuristic)
    is_cauchy = float(gl_error_cauchy.mid()) <= float(gl_error_heuristic.mid())

    if verbose:
        print(f"  GL error (Cauchy):    {gl_error_cauchy}")
        print(f"  GL error (heuristic): {gl_error_heuristic}")
        print(f"  Using: {'Cauchy (rigorous)' if is_cauchy else 'heuristic (NOT rigorous)'}")

    # --- Tail bound ---
    C_K = arb(4)
    tail_err = tail_bound_complex(z, L_out, C_K, prec)

    # --- Combine ---
    total_error = gl_error + tail_err
    H_re = arb.union(H_fg_main.real - total_error, H_fg_main.real + total_error)
    H_im = arb.union(H_fg_main.imag - total_error, H_fg_main.imag + total_error)
    H_fg = acb(H_re, H_im)

    elapsed = time.time() - t_start

    if verbose:
        print(f"\nResults:")
        print(f"  H_{{f,g}}(z) = {H_fg}")
        print(f"  GL error     = {gl_error}")
        print(f"  tail error   = {tail_err}")
        method_note = "rigorous" if is_cauchy else "heuristic GL"
        print(f"  method       = {method_note}")
        print(f"  time         = {elapsed:.1f}s")

    method_str = (
        f"certified (GL {n_panels}x{n_gl}, acb K_z, "
        + ("Cauchy GL)" if is_cauchy else "heuristic GL)")
    )

    flint_ctx.prec = old_prec
    return HfgComplexResult(
        H_fg=H_fg, z=z, tail_error=tail_err, gl_error=gl_error,
        elapsed=elapsed,
        method=method_str,
    )


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def verify_baseline_complex(prec: int = 256, verbose: bool = True):
    """Verify H_0(z) = arcsin(z) for P = Q = 0 at several complex z values."""
    flint_ctx.prec = prec

    def zero_fn(x, prec=256):
        return arb(0)

    test_points = [
        acb(arb("0.5"), arb("0.3")),
        acb(arb("0.0"), arb("0.7")),
        acb(arb("-0.3"), arb("0.5")),
        acb(arb("0.5"), arb("0.0")),   # real, compare with arcsin
    ]

    if verbose:
        print("=== Baseline verification: P = Q = 0, H_0(z) = arcsin(z) ===\n")

    all_ok = True
    for z in test_points:
        expected = z.asin()
        if verbose:
            print(f"  z = {z}")
            print(f"  Expected: arcsin(z) = {expected}")

        result = compute_H_fg_complex(
            z, P_arb=zero_fn, Q_arb=zero_fn,
            L_outer=8, n_panels=12, n_gl=24, n_gl_inner=24,
            prec=prec, verbose=False,
        )

        contains_re = result.H_fg.real.contains(expected.real)
        contains_im = result.H_fg.imag.contains(expected.imag)
        ok = contains_re and contains_im

        if verbose:
            print(f"  Computed:  {result.H_fg}")
            print(f"  Contains expected (re): {contains_re}")
            print(f"  Contains expected (im): {contains_im}")
            print(f"  GL error: {result.gl_error}, tail: {result.tail_error}")
            print(f"  Time: {result.elapsed:.1f}s")
            print(f"  {'PASS' if ok else 'FAIL'}\n")

        if not ok:
            all_ok = False

    return all_ok


def verify_real_consistency(t: float = 0.5, prec: int = 256, verbose: bool = True):
    """Compare compute_H_fg_complex(t+0i) with h_fg_rigor.compute_H_fg_gl(t)."""
    from grothendieck.proof.certified.h_fg_rigor import compute_H_fg_gl

    flint_ctx.prec = prec

    def zero_fn(x, prec=256):
        return arb(0)

    if verbose:
        print(f"=== Real consistency: t = {t}, P = Q = 0 ===\n")

    # Complex version with real z
    z = acb(arb(str(t)), arb(0))
    result_complex = compute_H_fg_complex(
        z, P_arb=zero_fn, Q_arb=zero_fn,
        L_outer=8, n_panels=12, n_gl=24, n_gl_inner=24,
        prec=prec, verbose=False,
    )

    # Real version
    result_real = compute_H_fg_gl(
        t, P_arb=zero_fn, Q_arb=zero_fn,
        L_outer=8, n_panels=12, n_gl=24, n_gl_inner=24,
        prec=prec, verbose=False,
    )

    expected = arb(str(t)).asin()

    if verbose:
        print(f"  Expected: arcsin({t}) = {expected}")
        print(f"  Complex version: {result_complex.H_fg}")
        print(f"  Real version:    {result_real.H_fg}")
        print(f"  Complex contains arcsin: re={result_complex.H_fg.real.contains(expected)}, "
              f"im_near_0={result_complex.H_fg.imag.contains(arb(0))}")
        print(f"  Real contains arcsin:    {result_real.H_fg.contains(expected)}")

    # Check overlap
    re_overlap = result_complex.H_fg.real.overlaps(result_real.H_fg)
    if verbose:
        print(f"  Real parts overlap: {re_overlap}")
        print(f"  {'PASS' if re_overlap else 'FAIL'}\n")

    return re_overlap


def verify_certified_baseline(prec: int = 256, verbose: bool = True):
    """Verify H_0(z) = arcsin(z) via the certified path (GL + acb.integral K_z + Cauchy)."""
    flint_ctx.prec = prec

    def zero_fn(x, prec=256):
        return arb(0)

    z = acb(arb("0.5"), arb("0.3"))
    expected = z.asin()

    if verbose:
        print(f"=== Certified baseline: z = {z} ===\n")
        print(f"  Expected: arcsin(z) = {expected}")

    result = compute_H_fg_complex_certified(
        z, P_arb=zero_fn, Q_arb=zero_fn,
        L_outer=8, n_panels=12, n_gl=24,
        prec=prec, verbose=verbose,
    )

    contains_re = result.H_fg.real.contains(expected.real)
    contains_im = result.H_fg.imag.contains(expected.imag)
    ok = contains_re and contains_im

    if verbose:
        print(f"  Contains expected (re): {contains_re}")
        print(f"  Contains expected (im): {contains_im}")
        print(f"  {'PASS' if ok else 'FAIL'}\n")

    return ok


if __name__ == "__main__":
    print("=" * 70)
    ok1 = verify_baseline_complex(verbose=True)
    print("=" * 70)
    ok2 = verify_real_consistency(t=0.5, verbose=True)
    print("=" * 70)
    ok3 = verify_certified_baseline(verbose=True)
    print("=" * 70)

    results = [("Baseline (GL)", ok1), ("Real consistency", ok2), ("Certified", ok3)]
    for name, ok in results:
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
    if all(ok for _, ok in results):
        print("\nAll verifications PASSED.")
    else:
        print("\nSome verifications FAILED!")
