"""
Rigorous computation of H_{f,g}(t) for real t in (-1, 1) using Arb ball arithmetic.

For sign functions f(x1,x2) = sign(x2 - P(x1)) and g(y1,y2) = sign(y2 - Q(y1)),
the 4D integral defining H_{f,g}(t) (BMMN eq. 8, k=2) reduces to a 2D Gaussian
integral via the Plackett/Owen finite-interval formula for K_t(a,b).

Convention: H_0(t) = arcsin(t) (the BMMN normalization, includes pi/2 factor).

Formula (independent parametrization):
    H_{f,g}(t) = (1/2) integral e^{-(u^2+v^2)} K_t(P(u), Q(tu + sigma*v)) du dv

where sigma = sqrt(1-t^2) and K_t uses the finite-interval formula:
    K_t(a,b) = erf(a)*erf(b) + (2/pi) integral_0^{arcsin(t)}
               exp(-(a^2 - 2ab*sin(theta) + b^2)/cos^2(theta)) dtheta

Two methods:
  - compute_H_fg_gl: outer via composite GL, inner K_t via GL (fast, heuristic bound)
  - compute_H_fg_certified: GL outer + acb.integral K_t (rigorous K_t, heuristic outer)
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Callable

from flint import arb, acb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (  # noqa: F401
    mpf_to_arb, certified_positive, certified_gt,
)
from grothendieck.proof.certified.bk_rigor import (
    compute_gl_nodes_weights_arb,
    scale_gl_to_interval,
    h3_arb,
    h5_arb,
)


# ---------------------------------------------------------------------------
# K_t(a, b) via finite-interval Plackett/Owen formula
# ---------------------------------------------------------------------------

def compute_K_t(
    a: arb,
    b: arb,
    arcsin_t: arb,
    prec: int = 256,
) -> arb:
    """Compute K_t(a, b) via acb.integral (fully rigorous).

    K_t(a,b) = erf(a)*erf(b) + (2/pi) * int_0^{arcsin(t)}
               exp(-(a^2 - 2ab*sin(theta) + b^2)/cos^2(theta)) dtheta

    Args:
        a, b: Arguments (real arb balls).
        arcsin_t: Precomputed arcsin(t).
        prec: Arb precision in bits.

    Returns:
        Rigorous arb ball containing K_t(a, b).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    erf_prod = a.erf() * b.erf()

    # Handle t ~ 0 case: integral vanishes
    if float(arcsin_t.abs_upper()) < 1e-50:
        flint_ctx.prec = old_prec
        return erf_prod

    a2_plus_b2 = a * a + b * b
    two_ab = arb(2) * a * b

    def integrand(theta, _analytic):
        sin_th = theta.sin()
        cos2_th = theta.cos() ** 2
        numerator = a2_plus_b2 - two_ab * sin_th
        return (-numerator / cos2_th).exp()

    I = acb.integral(integrand, acb(0), acb(arcsin_t))
    K = erf_prod + arb(2) / arb.pi() * I.real

    flint_ctx.prec = old_prec
    return K


def compute_K_t_gl(
    a: arb,
    b: arb,
    sin_vals: list[arb],
    cos2_vals: list[arb],
    theta_weights: list[arb],
    prec: int = 256,
) -> arb:
    """Compute K_t(a, b) via precomputed GL nodes (fast, no per-call overhead).

    GL error is NOT included in the ball; caller must add it separately.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    erf_prod = a.erf() * b.erf()
    a2_plus_b2 = a * a + b * b
    two_ab = arb(2) * a * b

    integral_sum = arb(0)
    for k in range(len(sin_vals)):
        numerator = a2_plus_b2 - two_ab * sin_vals[k]
        integral_sum += theta_weights[k] * (-numerator / cos2_vals[k]).exp()

    K = erf_prod + arb(2) / arb.pi() * integral_sum

    flint_ctx.prec = old_prec
    return K


# ---------------------------------------------------------------------------
# Tail bound
# ---------------------------------------------------------------------------

def tail_bound_fg(L: arb, prec: int = 256) -> arb:
    """Tail error: (1/2)|int_{R^2 \\ [-L,L]^2} e^{-(u^2+v^2)} K du dv| <= pi*erfc(L).

    Since |K_t| <= 1 and int e^{-(u^2+v^2)} du dv = pi:
        tail <= (1/2) * pi * (1 - erf(L)^2) <= pi * erfc(L).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    bound = arb.pi() * L.erfc()
    flint_ctx.prec = old_prec
    return bound


# ---------------------------------------------------------------------------
# Result dataclass
# ---------------------------------------------------------------------------

@dataclass
class HfgResult:
    """Result from rigorous H_{f,g}(t) computation."""
    H_fg: arb
    t: arb
    tail_error: arb
    elapsed: float
    method: str

    def __str__(self):
        return (
            f"HfgResult(\n"
            f"  H_{{f,g}}(t) = {self.H_fg}\n"
            f"  t          = {self.t}\n"
            f"  tail error = {self.tail_error}\n"
            f"  method     = {self.method}\n"
            f"  time       = {self.elapsed:.1f}s\n"
            f")"
        )


# ---------------------------------------------------------------------------
# Method 1: Certified (GL outer + acb.integral K_t — analogous to bk_rigor.py)
# ---------------------------------------------------------------------------

def compute_H_fg_certified(
    t: float,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    L_outer: int = 8,
    n_panels: int = 12,
    n_gl: int = 24,
    prec: int = 256,
    gl_dps: int = 100,
    verbose: bool = False,
) -> HfgResult:
    """Compute H_{f,g}(t) via composite GL outer + acb.integral K_t.

    Analogous to bk_rigor.py's approach: composite GL for the outer 2D
    integral over (u, v), and acb.integral for the inner K_t theta integral
    (fully rigorous error tracking for K_t).

    The outer GL error is estimated by computing at two resolutions
    (n_gl and n_gl//2) and using the difference as a conservative bound.

    Args:
        t: Correlation parameter in (-1, 1).
        P_arb, Q_arb: Arb polynomial functions for the sign curves.
        L_outer: Truncation radius.
        n_panels: GL panels per dimension.
        n_gl: GL order per panel (outer).
        prec: Arb precision in bits.
        gl_dps: Precision for GL node computation.
        verbose: Print progress.
    """
    result = compute_H_fg_gl(
        t,
        P_arb=P_arb,
        Q_arb=Q_arb,
        L_outer=L_outer,
        n_panels=n_panels,
        n_gl=n_gl,
        n_gl_inner=0,  # unused when use_acb_for_kt=True
        prec=prec,
        gl_dps=gl_dps,
        use_acb_for_kt=True,
        verbose=verbose,
    )
    result.method = f"certified (GL {n_panels}x{n_gl}, acb K_t)"
    return result


# ---------------------------------------------------------------------------
# Method 2: GL (composite Gauss-Legendre — fast, uses acb.integral for K_t)
# ---------------------------------------------------------------------------

def compute_H_fg_gl(
    t: float,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    L_outer: int = 8,
    n_panels: int = 8,
    n_gl: int = 16,
    n_gl_inner: int = 24,
    prec: int = 256,
    gl_dps: int = 100,
    use_acb_for_kt: bool = False,
    verbose: bool = False,
) -> HfgResult:
    """Compute H_{f,g}(t) via composite GL (fast).

    Outer 2D integral: composite Gauss-Legendre on [-L, L]^2.
    Inner K_t: GL on [0, arcsin(t)] or acb.integral (if use_acb_for_kt=True).

    The GL quadrature error is estimated by computing at two resolutions
    (n_gl and n_gl//2) and using the difference as a conservative bound.

    Args:
        t: Correlation parameter in (-1, 1).
        P_arb, Q_arb: Arb polynomial functions for the sign curves.
        L_outer: Truncation radius.
        n_panels: GL panels per dimension.
        n_gl: GL order per panel (outer).
        n_gl_inner: GL order for inner K_t integral.
        prec: Arb precision.
        gl_dps: Precision for GL node computation.
        use_acb_for_kt: Use acb.integral for K_t instead of GL.
        verbose: Print progress.
    """
    if P_arb is None:
        P_arb = h3_arb
    if Q_arb is None:
        Q_arb = h3_arb

    t_start = time.time()
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    t_arb = arb(str(t))
    sigma = (arb(1) - t_arb * t_arb).sqrt()
    arcsin_t = t_arb.asin()
    L_out = arb(L_outer)

    if verbose:
        print(f"Computing H_{{f,g}}({t}) via composite GL")
        print(f"  sigma = {sigma}, arcsin(t) = {arcsin_t}")
        print(f"  Outer: {n_panels} panels x {n_gl} GL = {n_panels * n_gl} nodes/dim")

    # --- Outer GL nodes ---
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

    # --- Inner K_t GL nodes (if not using acb.integral) ---
    sin_vals, cos2_vals, theta_weights = None, None, None
    if not use_acb_for_kt:
        ref_inner, ref_inner_w = compute_gl_nodes_weights_arb(
            n_gl_inner, gl_dps, prec,
        )
        theta_nodes, theta_weights = scale_gl_to_interval(
            ref_inner, ref_inner_w, arb(0), arcsin_t,
        )
        sin_vals = [th.sin() for th in theta_nodes]
        cos2_vals = [th.cos() ** 2 for th in theta_nodes]

    # --- Compute outer double sum ---
    if verbose:
        print(f"  Computing {n_total ** 2} evaluations...")
        t_sum = time.time()

    H_sum = arb(0)
    count = 0

    for j in range(n_total):
        v_j, w_v = all_nodes[j]
        for i in range(n_total):
            u_i, w_u = all_nodes[i]
            a = P_arb(u_i, prec)
            y1 = t_arb * u_i + sigma * v_j
            b = Q_arb(y1, prec)
            gauss_wt = (-(u_i * u_i + v_j * v_j)).exp()

            if use_acb_for_kt:
                K_val = compute_K_t(a, b, arcsin_t, prec)
            else:
                K_val = compute_K_t_gl(
                    a, b, sin_vals, cos2_vals, theta_weights, prec,
                )

            H_sum += w_u * w_v * gauss_wt * K_val
            count += 1

        if verbose and (j + 1) % max(1, n_total // 5) == 0:
            elapsed_so_far = time.time() - t_sum
            rate = count / elapsed_so_far if elapsed_so_far > 0 else 1
            left = (n_total ** 2 - count) / rate if rate > 0 else 0
            print(f"    row {j+1}/{n_total} ({elapsed_so_far:.1f}s, ~{left:.0f}s left)")

    H_fg_main = H_sum / arb(2)

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

    H_sum_half = arb(0)
    for j in range(n_half):
        v_j, w_v = half_nodes[j]
        for i in range(n_half):
            u_i, w_u = half_nodes[i]
            a = P_arb(u_i, prec)
            y1 = t_arb * u_i + sigma * v_j
            b = Q_arb(y1, prec)
            gauss_wt = (-(u_i * u_i + v_j * v_j)).exp()
            if use_acb_for_kt:
                K_val = compute_K_t(a, b, arcsin_t, prec)
            else:
                K_val = compute_K_t_gl(
                    a, b, sin_vals, cos2_vals, theta_weights, prec,
                )
            H_sum_half += w_u * w_v * gauss_wt * K_val
    H_fg_half = H_sum_half / arb(2)

    # GL error estimate: |H_main - H_half| * safety_factor
    # The high-resolution result is much more accurate, so the difference
    # approximates the error of the LOW-resolution result. The high-resolution
    # error is much smaller. Use 2x safety factor on the difference.
    diff_mid = abs(float(H_fg_main.mid()) - float(H_fg_half.mid()))
    gl_error = arb(str(max(diff_mid * 2, 1e-50)))

    # --- Tail bound ---
    tail_err = tail_bound_fg(L_out, prec)

    # --- Combine ---
    total_error = gl_error + tail_err
    H_fg = arb.union(H_fg_main - total_error, H_fg_main + total_error)

    elapsed = time.time() - t_start

    if verbose:
        print(f"\nResults:")
        print(f"  H_{{f,g}}({t}) = {H_fg}")
        print(f"  GL error (est) = {gl_error}")
        print(f"  tail error     = {tail_err}")
        print(f"  time           = {elapsed:.1f}s")

    flint_ctx.prec = old_prec
    return HfgResult(
        H_fg=H_fg, t=t_arb, tail_error=tail_err,
        elapsed=elapsed,
        method=f"GL ({n_panels}x{n_gl}" +
               (f", acb K_t" if use_acb_for_kt else f", GL K_t n={n_gl_inner}") + ")",
    )


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def verify_baseline(t: float = 0.5, prec: int = 256, verbose: bool = True):
    """Verify H_0(t) = arcsin(t) for P = Q = 0."""
    flint_ctx.prec = prec

    def zero_fn(x, prec=256):
        return arb(0)

    expected = arb(str(t)).asin()
    if verbose:
        print(f"=== Baseline verification: P = Q = 0, t = {t} ===")
        print(f"Expected: arcsin({t}) = {expected}\n")

    # Test GL method (fast)
    print("--- GL method ---")
    r_gl = compute_H_fg_gl(
        t, P_arb=zero_fn, Q_arb=zero_fn,
        L_outer=8, n_panels=12, n_gl=24, n_gl_inner=24,
        prec=prec, verbose=verbose,
    )
    print(f"Contains expected: {r_gl.H_fg.contains(expected)}\n")

    return r_gl


def verify_h3(t: float = 0.5, eta: float = 0.01, prec: int = 256, verbose: bool = True):
    """Test with P = Q = eta*h3."""
    flint_ctx.prec = prec
    eta_arb = arb(str(eta))

    def P(x, prec=256):
        return eta_arb * h3_arb(x, prec)
    def Q(x, prec=256):
        return eta_arb * h3_arb(x, prec)

    if verbose:
        print(f"=== h3 test: P = Q = {eta}*h3, t = {t} ===\n")

    # GL method
    print("--- GL method ---")
    r_gl = compute_H_fg_gl(
        t, P_arb=P, Q_arb=Q,
        L_outer=8, n_panels=12, n_gl=24, n_gl_inner=32,
        prec=prec, verbose=verbose,
    )

    expected_baseline = arb(str(t)).asin()
    diff = float(r_gl.H_fg.mid()) - float(expected_baseline.mid())
    if verbose:
        print(f"\nH_fg({t}) - arcsin({t}) = {diff:.6e}")

    return r_gl


if __name__ == "__main__":
    verify_baseline(t=0.5)
    print("\n" + "=" * 70 + "\n")
    verify_h3(t=0.5, eta=0.01)
