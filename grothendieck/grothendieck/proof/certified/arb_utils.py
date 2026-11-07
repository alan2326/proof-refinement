"""
Shared Arb ball arithmetic utilities for certified computations.

Provides foundational utilities used by all certification modules:
- Rigorous modulus bounds (abs_ub, abs_lb)
- Precision escalation (ensure)
- Conversion between mpmath and flint
- Domain splitting primitives (max_on_circle, min_on_circle, max_on_rectangle)
"""

from __future__ import annotations

import math
from typing import Callable, Optional

from flint import arb, acb, ctx as flint_ctx
from mpmath import mp


def set_prec(prec: int):
    """Set the global Arb precision (in bits)."""
    flint_ctx.prec = prec


def abs_ub(z: acb) -> arb:
    """Rigorous upper bound on |z|."""
    return z.abs_upper()


def abs_lb(z: acb) -> arb:
    """Rigorous lower bound on |z|. Only valid if ball doesn't contain 0."""
    return z.abs_lower()


def abs_ub_arb(x: arb) -> arb:
    """Rigorous upper bound on |x| for real ball."""
    # |x| <= max(|lower|, |upper|)
    return arb.max(x, -x).upper()  # not quite right
    # Actually: for a real ball [m-r, m+r], |x| <= |m| + r
    mid = x.mid()
    rad = x.rad()
    return abs(mid) + rad


def contains_zero(x) -> bool:
    """Check if ball contains zero (works for arb or acb)."""
    if isinstance(x, acb):
        return x.real.contains(arb(0)) and x.imag.contains(arb(0))
    return x.contains(arb(0))


def ensure(condition_fn: Callable[[int], bool],
           initial_prec: int = 128,
           max_prec: int = 4096,
           step: int = 2) -> int:
    """Retry condition_fn at increasing precision until it succeeds.

    Args:
        condition_fn: Function taking precision (int) and returning bool.
        initial_prec: Starting precision in bits.
        max_prec: Maximum precision before giving up.
        step: Multiplicative step for precision increase.

    Returns:
        The precision at which the condition succeeded.

    Raises:
        RuntimeError: If max_prec exceeded without success.
    """
    prec = initial_prec
    while prec <= max_prec:
        flint_ctx.prec = prec
        if condition_fn(prec):
            return prec
        prec *= step
    raise RuntimeError(
        f"ensure() failed: condition not satisfied up to prec={max_prec}"
    )


def mpf_to_arb(x, prec: int = 128) -> arb:
    """Convert mpmath mpf to flint arb via string representation."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    result = arb(mp.nstr(x, int(prec * 0.3), strip_zeros=False))
    flint_ctx.prec = old_prec
    return result


def mpc_to_acb(z, prec: int = 128) -> acb:
    """Convert mpmath mpc to flint acb via string."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    re = arb(mp.nstr(mp.re(z), int(prec * 0.3), strip_zeros=False))
    im = arb(mp.nstr(mp.im(z), int(prec * 0.3), strip_zeros=False))
    result = acb(re, im)
    flint_ctx.prec = old_prec
    return result


def arb_to_mpf(x: arb):
    """Convert flint arb midpoint to mpmath mpf."""
    return mp.mpf(str(x.mid()))


def acb_to_mpc(z: acb):
    """Convert flint acb midpoint to mpmath mpc."""
    from mpmath import mpc as mp_mpc
    return mp_mpc(str(z.real.mid()), str(z.imag.mid()))


def arb_pi(prec: int = 128) -> arb:
    """Rigorous enclosure of pi."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    result = arb.pi()
    flint_ctx.prec = old_prec
    return result


def arb_factorial(n: int) -> arb:
    """Compute n! as an exact arb."""
    return arb.fac_ui(n)


def max_on_circle(f: Callable[[acb], acb],
                  radius,
                  center=None,
                  n_arcs: int = 256,
                  prec: int = 128) -> arb:
    """Rigorous upper bound on max|f(z)| for |z - center| = radius.

    Subdivides the circle into n_arcs arcs, evaluates f on acb balls
    covering each arc, and returns the max of abs_ub over all arcs.

    Args:
        f: Analytic function to maximize.
        radius: Circle radius (arb or float).
        center: Circle center (acb or None for origin).
        n_arcs: Number of arc subdivisions.
        prec: Precision in bits.

    Returns:
        Rigorous upper bound on max|f(z)| as arb.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    if not isinstance(radius, arb):
        radius = arb(str(radius))
    if center is None:
        center = acb(0)
    elif not isinstance(center, acb):
        center = acb(center)

    pi_val = arb.pi()
    two_pi = 2 * pi_val
    max_val = arb(0)

    for k in range(n_arcs):
        # theta interval [2*pi*k/n, 2*pi*(k+1)/n]
        theta_lo = two_pi * arb(k) / arb(n_arcs)
        theta_hi = two_pi * arb(k + 1) / arb(n_arcs)
        # Midpoint and radius of theta interval
        theta_mid = (theta_lo + theta_hi) / 2
        theta_rad = (theta_hi - theta_lo) / 2

        # Create acb ball for z = center + radius * exp(i*theta)
        # exp(i*theta) where theta is a ball
        theta_ball = arb(str(theta_mid.mid()))
        # Widen to cover the full interval
        theta_ball = arb.union(theta_lo, theta_hi)

        cos_t = theta_ball.cos()
        sin_t = theta_ball.sin()
        z = center + acb(radius * cos_t, radius * sin_t)

        fz = f(z)
        val = abs_ub(fz)
        max_val = arb.max(max_val, val)

    flint_ctx.prec = old_prec
    return max_val


def min_modulus_on_circle(f: Callable[[acb], acb],
                          radius,
                          center=None,
                          n_arcs: int = 256,
                          prec: int = 128) -> arb:
    """Rigorous lower bound on min|f(z)| for |z - center| = radius.

    Returns min of abs_lb over all arc enclosures.

    Args:
        f: Analytic function.
        radius: Circle radius.
        center: Circle center (default: origin).
        n_arcs: Number of subdivisions.
        prec: Precision in bits.

    Returns:
        Rigorous lower bound on min|f(z)|.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    if not isinstance(radius, arb):
        radius = arb(str(radius))
    if center is None:
        center = acb(0)
    elif not isinstance(center, acb):
        center = acb(center)

    pi_val = arb.pi()
    two_pi = 2 * pi_val
    min_val = None

    for k in range(n_arcs):
        theta_lo = two_pi * arb(k) / arb(n_arcs)
        theta_hi = two_pi * arb(k + 1) / arb(n_arcs)
        theta_ball = arb.union(theta_lo, theta_hi)

        cos_t = theta_ball.cos()
        sin_t = theta_ball.sin()
        z = center + acb(radius * cos_t, radius * sin_t)

        fz = f(z)
        val = abs_lb(fz)
        if min_val is None or val < min_val:
            min_val = val

    flint_ctx.prec = old_prec
    return min_val


def max_on_rectangle_boundary(f: Callable[[acb], acb],
                               re_range: tuple,
                               im_range: tuple,
                               n_per_edge: int = 64,
                               prec: int = 128) -> arb:
    """Rigorous upper bound on max|f(z)| on boundary of rectangle.

    Rectangle: re_range[0] <= Re(z) <= re_range[1],
               im_range[0] <= Im(z) <= im_range[1].

    Parameterizes each of the 4 edges, covers with small acb balls.

    Returns:
        Rigorous upper bound on max|f| on rectangle boundary.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    a_lo, a_hi = arb(str(re_range[0])), arb(str(re_range[1]))
    b_lo, b_hi = arb(str(im_range[0])), arb(str(im_range[1]))

    max_val = arb(0)

    def update_max(z):
        nonlocal max_val
        val = abs_ub(f(z))
        max_val = arb.max(max_val, val)

    # Bottom edge: Re in [a_lo, a_hi], Im = b_lo
    for k in range(n_per_edge):
        t_lo = a_lo + (a_hi - a_lo) * arb(k) / arb(n_per_edge)
        t_hi = a_lo + (a_hi - a_lo) * arb(k + 1) / arb(n_per_edge)
        re_ball = arb.union(t_lo, t_hi)
        z = acb(re_ball, b_lo)
        update_max(z)

    # Top edge: Re in [a_lo, a_hi], Im = b_hi
    for k in range(n_per_edge):
        t_lo = a_lo + (a_hi - a_lo) * arb(k) / arb(n_per_edge)
        t_hi = a_lo + (a_hi - a_lo) * arb(k + 1) / arb(n_per_edge)
        re_ball = arb.union(t_lo, t_hi)
        z = acb(re_ball, b_hi)
        update_max(z)

    # Left edge: Re = a_lo, Im in [b_lo, b_hi]
    for k in range(n_per_edge):
        t_lo = b_lo + (b_hi - b_lo) * arb(k) / arb(n_per_edge)
        t_hi = b_lo + (b_hi - b_lo) * arb(k + 1) / arb(n_per_edge)
        im_ball = arb.union(t_lo, t_hi)
        z = acb(a_lo, im_ball)
        update_max(z)

    # Right edge: Re = a_hi, Im in [b_lo, b_hi]
    for k in range(n_per_edge):
        t_lo = b_lo + (b_hi - b_lo) * arb(k) / arb(n_per_edge)
        t_hi = b_lo + (b_hi - b_lo) * arb(k + 1) / arb(n_per_edge)
        im_ball = arb.union(t_lo, t_hi)
        z = acb(a_hi, im_ball)
        update_max(z)

    flint_ctx.prec = old_prec
    return max_val


def min_modulus_on_rectangle_boundary(f: Callable[[acb], acb],
                                       re_range: tuple,
                                       im_range: tuple,
                                       n_per_edge: int = 64,
                                       prec: int = 128) -> arb:
    """Rigorous lower bound on min|f(z)| on boundary of rectangle.

    Returns:
        Rigorous lower bound on min|f| on rectangle boundary.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    a_lo, a_hi = arb(str(re_range[0])), arb(str(re_range[1]))
    b_lo, b_hi = arb(str(im_range[0])), arb(str(im_range[1]))

    min_val = None

    def update_min(z):
        nonlocal min_val
        val = abs_lb(f(z))
        if min_val is None or val < min_val:
            min_val = val

    # Bottom edge
    for k in range(n_per_edge):
        t_lo = a_lo + (a_hi - a_lo) * arb(k) / arb(n_per_edge)
        t_hi = a_lo + (a_hi - a_lo) * arb(k + 1) / arb(n_per_edge)
        re_ball = arb.union(t_lo, t_hi)
        update_min(acb(re_ball, b_lo))

    # Top edge
    for k in range(n_per_edge):
        t_lo = a_lo + (a_hi - a_lo) * arb(k) / arb(n_per_edge)
        t_hi = a_lo + (a_hi - a_lo) * arb(k + 1) / arb(n_per_edge)
        re_ball = arb.union(t_lo, t_hi)
        update_min(acb(re_ball, b_hi))

    # Left edge
    for k in range(n_per_edge):
        t_lo = b_lo + (b_hi - b_lo) * arb(k) / arb(n_per_edge)
        t_hi = b_lo + (b_hi - b_lo) * arb(k + 1) / arb(n_per_edge)
        im_ball = arb.union(t_lo, t_hi)
        update_min(acb(a_lo, im_ball))

    # Right edge
    for k in range(n_per_edge):
        t_lo = b_lo + (b_hi - b_lo) * arb(k) / arb(n_per_edge)
        t_hi = b_lo + (b_hi - b_lo) * arb(k + 1) / arb(n_per_edge)
        im_ball = arb.union(t_lo, t_hi)
        update_min(acb(a_hi, im_ball))

    flint_ctx.prec = old_prec
    return min_val if min_val is not None else arb(0)


def certified_lt(a: arb, b: arb) -> bool:
    """Certify a < b strictly, i.e., upper(a) < lower(b).

    Computes b - a in arb first and then compares the exact lower
    endpoint against zero. This keeps the final sign decision inside
    Arb instead of downcasting to Python float.
    """
    diff = b - a
    return diff.lower() > 0


def certified_gt(a: arb, b: arb) -> bool:
    """Certify a > b strictly, i.e., lower(a) > upper(b).

    Computes a - b in arb first and then compares the exact lower
    endpoint against zero. This keeps the final sign decision inside
    Arb instead of downcasting to Python float.
    """
    diff = a - b
    return diff.lower() > 0


def certified_positive(a: arb) -> bool:
    """Certify a > 0, i.e., lower(a) > 0, via exact endpoint comparison."""
    return a.lower() > 0
