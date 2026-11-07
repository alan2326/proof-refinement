"""
Step 1: Certify analytic invertibility of F_p on r*D.

Produces certified (r, p, delta, B) such that F_p(z) = (1-p)H_0(z) + p*H_eta(z)
has an analytic inverse on r_outer*D (where r_outer = (1+r)/2) via Rouche's
theorem on the rectangle Omega(delta, B) = {z : |Re z| < 1-delta, |Im z| < B}.

Certifying at r_outer (not just r) is needed because the C_r formula requires
F_p^{-1} to be defined on a circle of radius (1+r)/2. The rectangle Omega
is auto-chosen to contain sin(r_outer*D).

Certification steps:
  1. Compute r_outer = (1+r)/2
  2. Auto-choose delta, B to tightly contain sin(r_outer*D) in Omega
  3. Verify sin(r_outer*D) subset Omega(delta, B)
  4. Compute Rouche margin m = min_{dOmega} (|H_0(z)| - r_outer) > 0
  5. Compute perturbation bound M_d = sup_{dOmega} |H_eta(z) - H_0(z)|
     using triangle inequality + Lemma 4.2 for |H_eta| bound
  6. Choose p = m/(2*M_d) with safety factor

Rigor notes:
  - All geometry comparisons via certified_lt/certified_positive (no float)
  - Max tracking via arb.max; min tracking via arb.min (no float conversion)
  - Lemma 4.2 hypothesis (1 - a^2 > 0) checked per rectangle segment
  - Precision changes wrapped in try/finally to prevent leaks on exceptions
  - First-quadrant reduction guarded by certified r < pi/2 check
"""

from __future__ import annotations

from typing import Callable, Optional

from flint import arb, acb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    abs_ub, abs_lb, certified_lt, certified_positive, set_prec,
)
from grothendieck.proof.certified.compute_m_rho import (
    _H_eta_bound_lemma42,
)


# ────────────────────────────────────────────────────────
# Helpers: rectangle boundary scans (pure arb, no float)
# ────────────────────────────────────────────────────────

def _iter_rect_boundary(delta, B, n_per_edge, prec):
    """Yield acb balls covering dOmega(delta, B).

    Omega = {|Re z| < 1-delta, |Im z| < B}.
    Yields one acb ball per segment, covering all 4 edges.
    """
    one = arb(1)
    re_bound = one - delta
    n = n_per_edge

    # Left/right edges: Re z = +/-(1-delta), Im z in [-B, B]
    for sign_re in [one, -one]:
        a = sign_re * re_bound
        for k in range(n):
            b_lo = -B + arb(2) * B * arb(k) / arb(n)
            b_hi = -B + arb(2) * B * arb(k + 1) / arb(n)
            yield acb(a, arb.union(b_lo, b_hi))

    # Top/bottom edges: Im z = +/-B, Re z in [-(1-delta), 1-delta]
    for sign_im in [one, -one]:
        b = sign_im * B
        for k in range(n):
            a_lo = -re_bound + arb(2) * re_bound * arb(k) / arb(n)
            a_hi = -re_bound + arb(2) * re_bound * arb(k + 1) / arb(n)
            yield acb(arb.union(a_lo, a_hi), b)


def _max_on_rect(func, delta, B, n_per_edge=512, prec=128):
    """Max of func(z: acb) -> arb on dOmega. Uses arb.max tracking."""
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        max_val = arb(0)
        for z in _iter_rect_boundary(delta, B, n_per_edge, prec):
            max_val = arb.max(max_val, func(z))
        return max_val
    finally:
        flint_ctx.prec = old_prec


def _min_on_rect(func, delta, B, n_per_edge=512, prec=128):
    """Min of func(z: acb) -> arb on dOmega.

    Accumulates via arb.min (no float conversion). The result's lower
    endpoint is a rigorous lower bound on min_k func(z_k).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        result = None
        for z in _iter_rect_boundary(delta, B, n_per_edge, prec):
            val = func(z)
            result = val if result is None else arb.min(result, val)
        return result if result is not None else arb(0)
    finally:
        flint_ctx.prec = old_prec


# ────────────────────────────────────────────────────────
# sin(r*D) containment
# ────────────────────────────────────────────────────────

def _compute_max_re_sin_on_disk(r, n_arcs=512, prec=128):
    """Rigorous upper bound on max|Re(sin z)| for |z| <= r.

    Uses exp(i*theta) parameterization on |z|=r. By the maximum principle,
    max over disk = max on boundary. By symmetry, max|Re(sin z)| is
    attained in the first quadrant where Re(sin z) >= 0, so we scan
    theta in [0, pi/2] and track Re(sin z) via arb.max.

    Requires r < pi/2 (certified).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        # Guard the first-quadrant reduction
        if not certified_lt(r, arb.pi() / arb(2)):
            raise ValueError(
                f"_compute_max_re_sin_on_disk requires r < pi/2; got r = {r}"
            )

        half_pi = arb.pi() / arb(2)
        max_val = arb(0)

        for k in range(n_arcs):
            theta_lo = half_pi * arb(k) / arb(n_arcs)
            theta_hi = half_pi * arb(k + 1) / arb(n_arcs)
            theta = arb.union(theta_lo, theta_hi)

            z = acb(0, theta).exp() * r
            re_sin = z.sin().real
            # In the first quadrant, Re(sin z) = sin(x)*cosh(y) >= 0
            max_val = arb.max(max_val, re_sin)

        return max_val
    finally:
        flint_ctx.prec = old_prec


def _choose_delta_B(r, prec=128, verbose=False):
    """Auto-choose delta, B for Omega(delta, B) containing sin(r*D).

    Strategy:
      - Compute max_re = max|Re(sin z)| on |z|<=r
      - gap = 1 - max_re
      - delta = gap/3 (keeps 1-delta safely above max_re)
      - B = sinh(r) + gap/3

    Returns (delta, B) as arb.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        max_re = _compute_max_re_sin_on_disk(r, n_arcs=1024, prec=prec)
        gap = arb(1) - max_re

        if not certified_positive(gap):
            raise ValueError(
                f"Cannot certify max|Re(sin z)| < 1 for r={r}; "
                f"r may be too large (need r < pi/2)"
            )

        delta = gap / arb(3)
        B = r.sinh() + gap / arb(3)

        if verbose:
            print(f"  Auto-chose delta = {delta}, B = {B}")
            print(f"    max|Re(sin z)| for r_outer = {max_re}")
            print(f"    gap = 1 - max_re = {gap}")
            print(f"    1-delta = {arb(1) - delta}")

        return delta, B
    finally:
        flint_ctx.prec = old_prec


def certify_sin_r_disk_in_omega(r, delta, B, prec=128):
    """Certify sin(r*D) subset Omega(delta, B).

    Checks (all via certified_lt):
      1. sinh(r) < B
      2. max|Re(sin z)| < 1-delta for |z| <= r
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        result = {
            'imaginary_check': False,
            'real_check': False,
            'sinh_r': None,
            'max_re_sin': None,
            'threshold_re': None,
            'threshold_im': None,
        }

        sinh_r = r.sinh()
        result['sinh_r'] = sinh_r
        result['threshold_im'] = B
        result['imaginary_check'] = certified_lt(sinh_r, B)

        threshold_re = arb(1) - delta
        result['threshold_re'] = threshold_re
        max_re = _compute_max_re_sin_on_disk(r, n_arcs=512, prec=prec)
        result['max_re_sin'] = max_re
        result['real_check'] = certified_lt(max_re, threshold_re)

        return result
    finally:
        flint_ctx.prec = old_prec


# ────────────────────────────────────────────────────────
# Rouche margin and perturbation bound
# ────────────────────────────────────────────────────────

def compute_rouche_margin_omega(r, delta, B, n_per_edge=512, prec=128):
    """Compute Rouche margin m = min_{dOmega} (|H_0(z)| - r).

    H_0(z) = arcsin(z). Returns rigorous lower bound on m.
    Uses arb.min accumulation (no float) so the result's lower endpoint
    is a rigorous lower bound on the true minimum.
    """
    min_abs_arcsin = _min_on_rect(
        lambda z: abs_lb(z.asin()),
        delta, B, n_per_edge, prec,
    )
    return min_abs_arcsin - r


def _max_H_eta_on_rect_lemma42(delta, B, n_per_edge=512, prec=128):
    """Rigorous upper bound on max|H_eta(z)| on dOmega(delta,B) via Lemma 4.2.

    Checks 1-a^2 > 0 per segment (guaranteed since delta > 0
    implies |Re z| <= 1-delta < 1 on dOmega).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        one = arb(1)
        max_val = arb(0)

        for z in _iter_rect_boundary(delta, B, n_per_edge, prec):
            a = z.real   # Re(w) — arb ball
            b = z.imag   # Im(w) — arb ball

            # Check Lemma 4.2 hypothesis: 1 - a^2 > 0
            if not certified_positive(one - a ** 2):
                raise ValueError(
                    f"Lemma 4.2 hypothesis 1-a^2 > 0 failed: a = {a}"
                )

            bound = _H_eta_bound_lemma42(a, b, prec)
            max_val = arb.max(max_val, bound)

        return max_val
    finally:
        flint_ctx.prec = old_prec


def compute_perturbation_bound_omega(
    delta, B, n_per_edge=512, prec=128, verbose=False,
):
    """Compute M_d = sup_{dOmega} |H_eta(z) - H_0(z)| via triangle inequality.

    M_d <= max|H_eta(z)| + max|H_0(z)| on dOmega.
    Uses Lemma 4.2 for |H_eta| and direct evaluation for |arcsin|.
    """
    max_H_eta = _max_H_eta_on_rect_lemma42(delta, B, n_per_edge, prec)
    max_H_0 = _max_on_rect(
        lambda z: abs_ub(z.asin()),
        delta, B, n_per_edge, prec,
    )

    M_partial = max_H_eta + max_H_0

    if verbose:
        print(f"  max|H_0| on dOmega = {max_H_0}")
        print(f"  max|H_eta| on dOmega (Lemma 4.2) = {max_H_eta}")
        print(f"  M_d = max|H_eta| + max|H_0| = {M_partial}")

    return M_partial


# ────────────────────────────────────────────────────────
# p selection and main pipeline
# ────────────────────────────────────────────────────────

def choose_p(m, M_partial, safety=0.5):
    """Choose p = safety * m / (2 * M_d)."""
    return arb(str(safety)) * m / (arb(2) * M_partial)


def certify_invertibility(
    r=0.92,
    eta=0.01,
    h_eta_series=None,
    prec=128,
    verbose=False,
    **kwargs,
):
    """Full pipeline: auto-choose Omega(delta, B), verify Rouche, choose p.

    Certifies invertibility at r_outer = (1+r)/2, not just r. This is
    needed because C_r requires F_p^{-1} to be defined on a circle of
    radius (1+r)/2. The returned delta, B define an Omega that contains
    sin(r_outer * D), and p is valid up to r_outer.

    Returns dict with: r, r_outer, delta, B, margin, M_partial, p, and checks.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        r_arb = arb(str(r))
        r_outer = (arb(1) + r_arb) / arb(2)

        if verbose:
            print(f"Step 1: Certifying analytic invertibility")
            print(f"  r = {r}, r_outer = (1+r)/2 = {r_outer}")

        # Auto-choose delta, B based on r_outer (the larger radius)
        delta, B = _choose_delta_B(r_outer, prec, verbose)

        if verbose:
            print(f"  Omega = {{|Re z| < {arb(1)-delta}, |Im z| < {B}}}")

        # Verify containment at r_outer
        check = certify_sin_r_disk_in_omega(r_outer, delta, B, prec)

        if verbose:
            print(f"  sinh(r_outer) = {check['sinh_r']} < B? {check['imaginary_check']}")
            print(f"  max|Re sin| = {check['max_re_sin']} < 1-delta? {check['real_check']}")

        if not (check['imaginary_check'] and check['real_check']):
            raise RuntimeError(
                f"Containment check failed at r_outer={r_outer}: "
                f"im={check['imaginary_check']}, re={check['real_check']}"
            )

        # Rouche margin at r_outer (not r!)
        if verbose:
            print(f"  Computing Rouche margin on dOmega (target: r_outer={r_outer})...")

        m = compute_rouche_margin_omega(r_outer, delta, B, prec=prec)

        if verbose:
            print(f"  Rouche margin m = min|arcsin| - r_outer = {m}")
            print(f"  m > 0? {certified_positive(m)}")

        if not certified_positive(m):
            raise RuntimeError(
                f"Rouche margin not certified positive at r_outer={r_outer}: m = {m}"
            )

        # Perturbation bound via Lemma 4.2
        if verbose:
            print(f"  Computing perturbation bound M_d on dOmega...")

        M_partial = compute_perturbation_bound_omega(
            delta, B, prec=prec, verbose=verbose,
        )

        # Choose p
        p = choose_p(m, M_partial)

        if verbose:
            print(f"  Chosen p = {p}")

        # Verify Rouche condition: p * M_d < m
        rouche_lhs = p * M_partial
        rouche_ok = certified_lt(rouche_lhs, m)

        if verbose:
            print(f"  Rouche check: p*M_d = {rouche_lhs} < m = {m}? {rouche_ok}")

        return {
            'r': r_arb,
            'r_outer': r_outer,
            'delta': delta,
            'B': B,
            'n': 0,
            'containment_check': check,
            'margin': m,
            'M_partial': M_partial,
            'p': p,
            'rouche_ok': rouche_ok,
            'all_checks_passed': (check['imaginary_check'] and check['real_check']
                                  and certified_positive(m) and rouche_ok),
        }
    finally:
        flint_ctx.prec = old_prec
