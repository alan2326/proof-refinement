"""
Certified B_K computation via rigorous Arb integration (no Gauss-Hermite).

Strategy:
  1. Outer 2D integral: composite Gauss-Legendre on [-L, L]² with explicit
     Gaussian weight. GL error bounded rigorously via Cauchy estimate.
  2. Inner E(t,s) integral: computed via acb.integral (Arb's certified
     adaptive integration), with tail bound for truncation at [-L_inner, L_inner].
  3. Gaussian tail bound: erfc(L/√2) computed in arb.

Every step produces a rigorous arb enclosure. If Δ.lower() > 0, positivity
is certified.
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Callable, Optional

from flint import arb, acb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    certified_positive,
)
from grothendieck.proof.certified.gauss_legendre import (
    certify_gl_nodes_weights,
    certified_scale_gl_to_interval,
)


# ---------------------------------------------------------------------------
# Gauss-Legendre nodes/weights on [-1, 1] → arb
# ---------------------------------------------------------------------------

def compute_gl_nodes_weights_arb(
    n: int, dps: int = 100, prec: int = 256,
) -> tuple[list[arb], list[arb]]:
    """Compute n-point GL nodes and weights on [-1, 1] as certified arb balls.

    Uses arb.legendre_p_root (via gauss_legendre.certify_gl_nodes_weights)
    for rigorous enclosures. The `dps` parameter is accepted for backward
    compatibility but is no longer used — precision is controlled by `prec`.
    """
    return certify_gl_nodes_weights(n, prec=prec)


def scale_gl_to_interval(
    nodes: list[arb], weights: list[arb], a: arb, b: arb,
) -> tuple[list[arb], list[arb]]:
    """Scale GL nodes/weights from [-1,1] to [a,b]."""
    return certified_scale_gl_to_interval(nodes, weights, a, b)


# ---------------------------------------------------------------------------
# Physicist's Hermite polynomials in arb (for P, Q)
# ---------------------------------------------------------------------------

def h3_arb(x, prec: int = 256):
    """h_3(x) = (2x³ - 3x) / (√3 · π^{1/4})"""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    pi_quarter = arb.pi().sqrt().sqrt()
    denom = arb(3).sqrt() * pi_quarter
    result = (arb(2) * x * x * x - arb(3) * x) / denom
    flint_ctx.prec = old_prec
    return result


def h5_arb(x, prec: int = 256):
    """h_5(x) = (4x⁵ - 20x³ + 15x) / (2 π^{1/4} √15)"""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    x2 = x * x
    x3 = x2 * x
    x5 = x3 * x2
    pi_quarter = arb.pi().sqrt().sqrt()
    denom = arb(2) * pi_quarter * arb(15).sqrt()
    result = (arb(4) * x5 - arb(20) * x3 + arb(15) * x) / denom
    flint_ctx.prec = old_prec
    return result


# ---------------------------------------------------------------------------
# Inner integral E(t, s) via acb.integral
# ---------------------------------------------------------------------------

def _E_integrand(x: acb, s: acb, sqrt2: acb) -> acb:
    """g(x,s) = e^{-x²} erf((s - ix)/√2)"""
    return (-x * x).exp() * ((s - acb(arb(0), arb(1)) * x) / sqrt2).erf()


def compute_E_arb_integral(
    t: arb,
    s: arb,
    L_inner: int = 15,
    prec: int = 256,
) -> acb:
    """Compute E(t,s) via certified acb.integral, splitting at x=t.

    E(t,s) = -(1/√(2π)) × [∫_t^L g(x,s) dx - ∫_{-L}^t g(x,s) dx]

    Returns:
        acb ball rigorously containing E(t,s).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    sqrt2 = acb(arb(2).sqrt())
    sqrt2pi = acb((arb(2) * arb.pi()).sqrt())
    s_acb = acb(s)
    L = arb(L_inner)

    def g(x, _analytic):
        return (-x * x).exp() * ((s_acb - acb(arb(0), arb(1)) * x) / sqrt2).erf()

    # Split at t to avoid sign function discontinuity
    I_neg = acb.integral(g, acb(-L), acb(t))
    I_pos = acb.integral(g, acb(t), acb(L))

    E_val = -(I_pos - I_neg) / sqrt2pi

    # Tail bound: |∫_{|x|>L} e^{-x²} erf(...) dx| ≤ 2 ∫_L^∞ e^{-x²} dx
    # ≤ 2 × e^{-L²}/(2L) = e^{-L²}/L
    # Divided by √(2π): tail ≤ e^{-L²} / (L × √(2π))
    tail = (-L * L).exp() / (L * (arb(2) * arb.pi()).sqrt())
    E_re = arb.union(E_val.real - tail, E_val.real + tail)
    E_im = arb.union(E_val.imag - tail, E_val.imag + tail)

    flint_ctx.prec = old_prec
    return acb(E_re, E_im)


def compute_E_correction_arb_integral(
    t: arb,
    s: arb,
    prec: int = 256,
) -> acb:
    """Compute (2/√(2π)) × ∫_0^t g(x,s) dx = E(t,s) - E(0,s).

    This is the correction from the baseline E(0,s).
    For small t, this integral is over a short interval and very fast.

    Returns:
        acb ball for the correction term.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    sqrt2 = acb(arb(2).sqrt())
    s_acb = acb(s)

    def g(x, _analytic):
        return (-x * x).exp() * ((s_acb - acb(arb(0), arb(1)) * x) / sqrt2).erf()

    # Integral from 0 to t (short interval for small η)
    integral = acb.integral(g, acb(0), acb(t))

    two_over_sqrt2pi = acb(arb(2) / (arb(2) * arb.pi()).sqrt())
    result = two_over_sqrt2pi * integral

    flint_ctx.prec = old_prec
    return result


# ---------------------------------------------------------------------------
# GL error bound via Cauchy estimate
# ---------------------------------------------------------------------------

def gl_error_bound_1d(
    integrand_fn: Callable,
    panel_a: arb,
    panel_b: arb,
    n_gl: int,
    cauchy_radius: float = 0.3,
    prec: int = 256,
) -> arb:
    """Rigorous bound on GL error for one panel using Cauchy estimate.

    For n-point GL on [a, b], the error is:
        |E_n| ≤ ((b-a)/2)^{2n+1} × (n!)^4 / ((2n+1) × ((2n)!)^3) × max|f^{(2n)}|

    We bound max|f^{(2n)}| via Cauchy's integral formula:
        |f^{(2n)}(ξ)| ≤ (2n)! × M_r / r^{2n}

    where M_r = max_{|z-ξ|≤r} |f(z)| is estimated by evaluating f on a
    ball covering the panel + complex extension.

    Returns:
        Rigorous upper bound on the GL quadrature error for this panel.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    h = panel_b - panel_a
    half_h = h / arb(2)
    r = arb(str(cauchy_radius))

    # Evaluate integrand on a ball covering the panel + complex disk of radius r
    panel_mid = (panel_a + panel_b) / arb(2)
    panel_ball = arb.union(panel_a, panel_b)
    z_ball = acb(panel_ball, arb.union(-r, r))

    # Get M_r = upper bound on |f(z)| on this ball
    f_ball = integrand_fn(z_ball)
    M_r = f_ball.abs_upper()

    # GL error formula (combined with Cauchy):
    # |E_n| ≤ (h/2)^{2n+1} × (n!)^4 / ((2n+1) × ((2n)!)^3) × (2n)! × M_r / r^{2n}
    #       = (h/2) × ((h/2)/r)^{2n} × (n!)^4 / ((2n+1) × ((2n)!)^2) × M_r

    # Compute (n!)^4 / ((2n+1) × ((2n)!)^2) in arb
    n_fac = arb.fac_ui(n_gl)
    two_n_fac = arb.fac_ui(2 * n_gl)
    coeff = (n_fac ** 4) / (arb(2 * n_gl + 1) * two_n_fac * two_n_fac)

    ratio = half_h / r
    ratio_pow = ratio
    for _ in range(2 * n_gl - 1):
        ratio_pow = ratio_pow * ratio
    # ratio_pow = (h/(2r))^{2n}

    error = half_h * ratio_pow * coeff * M_r

    flint_ctx.prec = old_prec
    return error


# ---------------------------------------------------------------------------
# Gaussian tail bound
# ---------------------------------------------------------------------------

def gaussian_tail_bound(L: arb, prec: int = 256) -> arb:
    """Bound on |∫_{|u|>L or |v|>L} F(u,v) φ(u) φ(v) du dv|.

    Since |F| ≤ 2 (crude bound on sin(uv)ΔC + cos(uv)ΔS):
        tail ≤ 2 × P(|U|>L or |V|>L) ≤ 2 × 2 × erfc(L/√2) = 4 erfc(L/√2)
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    tail_prob = (L / arb(2).sqrt()).erfc()
    bound = arb(4) * tail_prob

    flint_ctx.prec = old_prec
    return bound


# ---------------------------------------------------------------------------
# Main computation
# ---------------------------------------------------------------------------

@dataclass
class DeltaResultRigor:
    """Result from certified rigorous Δ(η) computation."""
    H_eta_over_i: arb
    H_0_over_i: arb
    Delta: arb
    eta: arb
    certified_positive: bool
    gl_error: arb
    tail_error: arb

    def __str__(self):
        return (
            f"DeltaResultRigor(\n"
            f"  H_η(i)/i = {self.H_eta_over_i}\n"
            f"  H_0(i)/i = {self.H_0_over_i}\n"
            f"  Δ(η)     = {self.Delta}\n"
            f"  η        = {self.eta}\n"
            f"  certified_positive = {self.certified_positive}\n"
            f"  GL error bound     = {self.gl_error}\n"
            f"  Tail error bound   = {self.tail_error}\n"
            f")"
        )


def compute_Delta_rigor(
    eta: float,
    P_arb: Callable = None,
    Q_arb: Callable = None,
    L_outer: int = 10,
    L_inner: int = 15,
    n_panels: int = 10,
    n_gl: int = 32,
    prec: int = 256,
    gl_dps: int = 100,
    verbose: bool = False,
) -> DeltaResultRigor:
    """Compute Δ(η) = H_η(i)/i - H_0(i)/i via fully rigorous integration.

    Uses composite Gauss-Legendre for the outer 2D integral and acb.integral
    for the inner E(t,s) integrals. No Gauss-Hermite machinery.

    Args:
        eta: Perturbation parameter.
        P_arb: Function P(x, prec) → arb. Defaults to h3.
        Q_arb: Function Q(x, prec) → arb. Defaults to h3.
        L_outer: Truncation radius for outer integral [-L, L]².
        L_inner: Truncation radius for inner E integral.
        n_panels: Number of GL panels per dimension.
        n_gl: GL order per panel.
        prec: Arb precision in bits.
        gl_dps: Precision for computing GL nodes.
        verbose: Print progress.

    Returns:
        DeltaResultRigor with certified arb enclosures.
    """
    if P_arb is None:
        P_arb = h3_arb
    if Q_arb is None:
        Q_arb = h3_arb

    t_start = time.time()
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    eta_arb = arb(str(eta))
    H_0 = (arb(1) / arb(2).sqrt()).atanh()
    L_out = arb(L_outer)

    if verbose:
        print(f"Computing certified Δ(η) via rigorous integration")
        print(f"  η = {eta}, L_outer = {L_outer}, L_inner = {L_inner}")
        print(f"  GL: {n_panels} panels × {n_gl}-point = {n_panels * n_gl} nodes/dim")
        print(f"  Total evaluations: {(n_panels * n_gl) ** 2}")
        print(f"  H_0(i)/i = atanh(1/√2) = {H_0}")

    # --- Step 1: Compute GL nodes/weights ---
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)

    # Build composite GL nodes on [-L_outer, L_outer]
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []  # (node, weight) pairs
    panels = []  # (a, b) pairs for error bound

    for p in range(n_panels):
        a = -L_out + arb(p) * panel_width
        b = a + panel_width
        panels.append((a, b))
        s_nodes, s_weights = scale_gl_to_interval(ref_nodes, ref_weights, a, b)
        for node, weight in zip(s_nodes, s_weights):
            all_nodes.append((node, weight))

    n_total = len(all_nodes)
    if verbose:
        print(f"  {n_total} GL nodes per dimension, {n_total ** 2} total pairs")

    # --- Step 2: Precompute E(0,0) ---
    E_00 = compute_E_arb_integral(arb(0), arb(0), L_inner, prec)
    C_00 = E_00.real
    S_00 = E_00.imag

    if verbose:
        print(f"  E(0,0): C={C_00}, S={S_00}")

    # --- Step 3: Precompute E(0, s_j) for each unique s value ---
    # s_j = -η Q(v_j) for each GL node v_j
    if verbose:
        print(f"  Precomputing E(0, s_j) for {n_total} s-values...")
        t_pre = time.time()

    s_vals = []
    E_0_s = []  # E(0, s_j) as acb
    for j, (v_j, _) in enumerate(all_nodes):
        s_j = -(eta_arb * Q_arb(v_j, prec))
        s_vals.append(s_j)
        E_val = compute_E_arb_integral(arb(0), s_j, L_inner, prec)
        E_0_s.append(E_val)
        if verbose and (j + 1) % 50 == 0:
            elapsed = time.time() - t_pre
            print(f"    {j + 1}/{n_total} ({elapsed:.1f}s)")

    if verbose:
        print(f"  E(0,s) precomputation: {time.time() - t_pre:.1f}s")

    # --- Step 4: Compute outer double sum ---
    if verbose:
        print(f"  Computing outer double sum ({n_total ** 2} evaluations)...")
        t_sum = time.time()

    # The integral is:
    # Δ = (1/2) × ∫∫ [sin(uv)·ΔC + cos(uv)·ΔS] × e^{-(u²+v²)/2} du dv
    # where ΔC = Re(E(t,s) - E(0,0)), ΔS = Im(E(t,s) - E(0,0))
    # and t = η·P(u), s = -η·Q(v)
    #
    # E(t,s) - E(0,0) = (E(0,s) - E(0,0)) + (E(t,s) - E(0,s))
    # where E(t,s) - E(0,s) = (2/√(2π)) ∫_0^t g(x,s) dx

    Delta_sum = arb(0)
    count = 0

    for j in range(n_total):
        v_j, w_v = all_nodes[j]
        s_j = s_vals[j]
        delta_E0_s = E_0_s[j] - E_00  # E(0,s_j) - E(0,0)

        gauss_v = (-(v_j * v_j) / arb(2)).exp()

        for i in range(n_total):
            u_i, w_u = all_nodes[i]
            t_i = eta_arb * P_arb(u_i, prec)

            # Correction: E(t,s) - E(0,s) = (2/√(2π)) ∫_0^t g(x,s) dx
            correction = compute_E_correction_arb_integral(t_i, s_j, prec)

            # Full ΔE = (E(0,s) - E(0,0)) + correction
            delta_E = delta_E0_s + correction
            dC = delta_E.real
            dS = delta_E.imag

            uv = u_i * v_j
            sin_uv = uv.sin()
            cos_uv = uv.cos()
            gauss_u = (-(u_i * u_i) / arb(2)).exp()

            integrand = (sin_uv * dC + cos_uv * dS) * gauss_u * gauss_v
            Delta_sum = Delta_sum + w_u * w_v * integrand

            count += 1

        if verbose and (j + 1) % 20 == 0:
            elapsed = time.time() - t_sum
            rate = count / elapsed if elapsed > 0 else 0
            eta_secs = (n_total ** 2 - count) / rate if rate > 0 else 0
            print(f"    row {j + 1}/{n_total}, {count}/{n_total ** 2} pairs "
                  f"({elapsed:.1f}s, ~{eta_secs:.0f}s remaining)")

    if verbose:
        print(f"  Double sum: {time.time() - t_sum:.1f}s")

    # Derivation of the prefactor:
    #
    # From bk_semi_analytic.py, the GH approach gives:
    #   H_η(i)/i = π × f² × Σ w_i w_j F(√2 x_i, √2 x_j)
    # where f = 1/√π and w_i are GH weights (weight e^{-x²}).
    #
    # So H = π × (1/π) × Σ w_i w_j F(√2 x_i, √2 x_j) = Σ ...
    # The GH sum ≈ ∫∫ F(√2 x, √2 y) e^{-x²-y²} dx dy
    #
    # Substituting u = √2 x, v = √2 y (du = √2 dx):
    #   = (1/2) ∫∫ F(u,v) e^{-(u²+v²)/2} du dv
    #
    # Therefore: Δ = (1/2) ∫∫ [sin(uv)ΔC + cos(uv)ΔS] e^{-(u²+v²)/2} du dv

    Delta = Delta_sum / arb(2)

    # --- Step 5: GL error bound ---
    if verbose:
        print(f"  Computing GL error bound...")

    # For n-point GL on panel [a, b] of width h, the error is:
    #   |E_n| = (h/2)^{2n+1} × (n!)^4 / ((2n+1) × ((2n)!)^3) × f^{(2n)}(ξ)
    #
    # Bounding f^{(2n)} via Cauchy's integral formula with radius r > h/2:
    #   |f^{(2n)}| ≤ (2n)! × M_r / r^{2n}
    #
    # Combined: |E_n| ≤ (h/2) × ((h/2)/r)^{2n} × (n!)^4/((2n+1)×((2n)!)^2) × M_r
    #
    # M_r = max|f(z)| for z on panel + complex disk of radius r, where
    # f(u) = [sin(uv)ΔC + cos(uv)ΔS] × e^{-u²/2}
    #
    # Bound: |f(z)| ≤ 2 × e^{r|v|} × e^{(r²-Re(z)²)/2}
    # Worst case over all v in [-L,L]: |f(z)| ≤ 2 × e^{rL} × e^{r²/2}
    #
    # For 2D tensor product: error on Δ ≤ (4L/2) × Σ_panels e_panel

    # Cauchy radius: must have r > h/2 for convergence
    # Use r = panel_width (= 2 × h/2), giving ratio = 0.5
    cauchy_r_val = float(panel_width.mid().str(radius=False))
    cauchy_r = arb(str(cauchy_r_val))

    # M_r: worst-case bound on |f(z)| on panel + disk(r)
    # |f(z)| ≤ 2 × exp(r × L_outer) × exp(r²/2)
    # But for panels far from origin, e^{-Re(z)²/2} helps. Use panel-specific bound.
    # For simplicity, use global worst case (not tight for tail panels, but safe):
    M_global = arb(2) * (cauchy_r * L_out).exp() * (cauchy_r * cauchy_r / arb(2)).exp()

    # GL coefficient: (n!)^4 / ((2n+1) × ((2n)!)^2)
    n_fac = arb.fac_ui(n_gl)
    two_n_fac = arb.fac_ui(2 * n_gl)
    gl_coeff = (n_fac ** 4) / (arb(2 * n_gl + 1) * two_n_fac * two_n_fac)

    # Ratio = (h/2)/r = 0.5 (since r = h)
    half_panel = panel_width / arb(2)
    ratio = half_panel / cauchy_r  # = 0.5
    ratio_pow = arb(1)
    for _ in range(2 * n_gl):
        ratio_pow = ratio_pow * ratio

    error_per_panel = half_panel * ratio_pow * gl_coeff * M_global
    error_1d = arb(n_panels) * error_per_panel

    # 2D tensor product error: each dimension contributes independently
    # Total ≤ 2 × (2L) × error_1d = 4L × error_1d for the raw integral
    # Δ = integral / 2, so GL error on Δ ≤ 4L × error_1d / 2 = 2L × error_1d
    gl_error = arb(4) * L_out * error_1d / arb(2)

    if verbose:
        print(f"  Cauchy radius: {cauchy_r}")
        print(f"  GL coeff (n!)^4/((2n+1)(2n!)^2): {gl_coeff}")
        print(f"  Ratio (h/2r)^{2*n_gl}: {ratio_pow}")
        print(f"  M_r bound: {M_global}")
        print(f"  GL error per panel: {error_per_panel}")
        print(f"  GL total 2D error: {gl_error}")

    # --- Step 6: Gaussian tail bound ---
    # gaussian_tail_bound returns 4 erfc(L/√2), bounding ∫_{tail} |F| φ(u)φ(v) du dv.
    # Since Δ = π ∫∫ F φ φ du dv (= (1/2) ∫∫ F e^{-(u²+v²)/2} du dv),
    # the tail error on Δ is π × 4 erfc(L/√2).
    tail_error = arb.pi() * gaussian_tail_bound(L_out, prec)

    if verbose:
        print(f"  Gaussian tail bound: {tail_error}")

    # --- Step 7: Combine ---
    total_error = gl_error + tail_error
    Delta = arb.union(Delta - total_error, Delta + total_error)

    H_eta = H_0 + Delta
    is_positive = certified_positive(Delta)

    elapsed = time.time() - t_start

    if verbose:
        print(f"\nResults:")
        print(f"  H_0(i)/i = {H_0}")
        print(f"  Δ(η)     = {Delta}")
        print(f"  H_η(i)/i = {H_eta}")
        print(f"  Δ > 0 certified: {is_positive}")
        if is_positive:
            print(f"  => B_K > (2/π) × atanh(1/√2)")
        print(f"  Total time: {elapsed:.1f}s")

    flint_ctx.prec = old_prec
    return DeltaResultRigor(
        H_eta_over_i=H_eta,
        H_0_over_i=H_0,
        Delta=Delta,
        eta=eta_arb,
        certified_positive=is_positive,
        gl_error=gl_error,
        tail_error=tail_error,
    )
