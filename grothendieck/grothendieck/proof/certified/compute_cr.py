"""
Step 2: Compute the certified constant C_r.

C_r = (8 M^2 R / (1-r)^2) * (1 + 16R/(1-r)^3)

where:
  M = max{|H_0(w)|, |H_eta(w)|, |H_0'(w)|, |H_eta'(w)|} on domain Omega
  R = upper bound on |F_p^{-1}(zeta)| for |zeta| <= r_outer = (1+r)/2

C_r controls the O(p^2) error in the Taylor expansion of F_p^{-1}.

Rigor notes:
  - |H_0| and |H_0'| evaluated directly via acb.asin and acb.rsqrt on dOmega
  - |H_eta| bounded via Lemma 4.2 (formula 43) on dOmega
  - |H_eta'| bounded via Cauchy inequality on enlarged rectangle
  - R bounded by sqrt((1-delta)^2 + B^2): valid because Step 1 certifies
    Rouche at r_outer = (1+r)/2, so F_p^{-1} maps r_outer*D into Omega
  - All tracking via arb.max; no float conversions for geometry
  - Precision changes wrapped in try/finally
"""

from __future__ import annotations

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    abs_ub, certified_positive,
)
from grothendieck.proof.certified.compute_m_rho import (
    _H_eta_bound_lemma42,
)
from grothendieck.proof.certified.certify_invertibility import (
    _iter_rect_boundary,
    _max_on_rect,
    _max_H_eta_on_rect_lemma42,
)


def compute_M_rigorous(
    r: arb,
    delta: arb,
    B: arb,
    n_per_edge: int = 512,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute M = max{|H_0|, |H_eta|, |H_0'|, |H_eta'|} on Omega(delta, B).

    - |H_0| = |arcsin(z)|: evaluated directly on dOmega
    - |H_eta|: Lemma 4.2 on dOmega
    - |H_0'| = |1/sqrt(1-z^2)|: evaluated directly on dOmega
    - |H_eta'|: Cauchy inequality on enlarged rectangle Omega(delta-d, B+d)
      with d = delta/4, giving max|H_eta'| <= max|H_eta|_{dOmega_d} / d
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        # 1. max|H_0| = max|arcsin| on dOmega
        max_H0 = _max_on_rect(
            lambda z: abs_ub(z.asin()),
            delta, B, n_per_edge, prec,
        )

        # 2. max|H_eta| on dOmega via Lemma 4.2
        max_H_eta = _max_H_eta_on_rect_lemma42(delta, B, n_per_edge, prec)

        # 3. max|H_0'| = max|1/sqrt(1-z^2)| on dOmega
        max_H0_prime = _max_on_rect(
            lambda z: abs_ub((acb(1) - z * z).rsqrt()),
            delta, B, n_per_edge, prec,
        )

        # 4. max|H_eta'| via Cauchy inequality on enlarged rectangle
        # Enlarge by d = delta/4: Omega_d has |Re z| < 1 - delta + d = 1 - 3*delta/4
        # Need 1 - 3*delta/4 < 1, i.e. delta > 0 (always true)
        d = delta / arb(4)
        delta_inner = delta - d     # = 3*delta/4  (delta for the ENLARGED rect)
        B_outer = B + d             # enlarged imaginary bound

        if not certified_positive(delta_inner):
            raise ValueError(
                f"Cannot form enlarged rectangle: delta_inner = {delta_inner}"
            )

        max_H_eta_outer = _max_H_eta_on_rect_lemma42(
            delta_inner, B_outer, n_per_edge, prec,
        )
        max_H_eta_prime = max_H_eta_outer / d

        # M = max of all four
        M = arb.max(
            arb.max(max_H0, max_H_eta),
            arb.max(max_H0_prime, max_H_eta_prime),
        )

        if verbose:
            print(f"  max|H_0| on dOmega = {max_H0}")
            print(f"  max|H_eta| on dOmega (Lemma 4.2) = {max_H_eta}")
            print(f"  max|H_0'| on dOmega = {max_H0_prime}")
            print(f"  max|H_eta'| on dOmega (Cauchy, d={d}) = {max_H_eta_prime}")
            print(f"  M = {M}")

        return M
    finally:
        flint_ctx.prec = old_prec


def compute_R_rigorous(
    delta: arb,
    B: arb,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Rigorous upper bound on R = max_{|zeta|<=r_outer} |F_p^{-1}(zeta)|.

    By the Rouche argument (Step 1, certified at r_outer = (1+r)/2),
    F_p maps Omega(delta, B) bijectively onto a domain containing
    r_outer * D. Hence F_p^{-1}(zeta) lies within Omega for all
    |zeta| <= r_outer.

    Therefore: |F_p^{-1}(zeta)| <= max distance from origin to Omega's
    boundary = sqrt((1-delta)^2 + B^2) (at the rectangle corners).

    This bound is valid BECAUSE certify_invertibility certified the Rouche
    condition at r_outer, not just r. Without that, this bound is not justified.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        re_bound = arb(1) - delta
        R = (re_bound ** 2 + B ** 2).sqrt()

        if verbose:
            print(f"  R = sqrt((1-delta)^2 + B^2) = {R}")

        return R
    finally:
        flint_ctx.prec = old_prec


def compute_Cr(M: arb, R: arb, r: arb, prec: int = 128) -> arb:
    """Compute C_r = 8*M^2*R / (1-r)^2 * (1 + 16*R/(1-r)^3).

    All operations in ball arithmetic for rigorous upper bound.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        one_minus_r = arb(1) - r
        one_minus_r_sq = one_minus_r ** 2
        one_minus_r_cube = one_minus_r_sq * one_minus_r

        term1 = arb(8) * M ** 2 * R / one_minus_r_sq
        term2 = arb(1) + arb(16) * R / one_minus_r_cube

        return term1 * term2
    finally:
        flint_ctx.prec = old_prec


def compute_Cr_full(
    r: arb,
    delta: arb,
    B: arb,
    h_eta_series: arb_series = None,
    prec: int = 128,
    verbose: bool = False,
) -> dict:
    """Full C_r computation pipeline.

    Assumes delta and B come from certify_invertibility, which certified
    the Rouche condition at r_outer = (1+r)/2. This justifies using
    R = sqrt((1-delta)^2 + B^2) as a bound on |F_p^{-1}|.

    Returns dict with M, R, C_r values.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        if verbose:
            print(f"Step 2: Computing C_r")
            print(f"  Omega: delta={delta}, B={B}")

        M = compute_M_rigorous(r, delta, B, prec=prec, verbose=verbose)
        R = compute_R_rigorous(delta, B, prec=prec, verbose=verbose)
        Cr = compute_Cr(M, R, r, prec)

        if verbose:
            print(f"  C_r = 8*M^2*R/(1-r)^2 * (1 + 16R/(1-r)^3) = {Cr}")

        return {
            'M': M,
            'R': R,
            'C_r': Cr,
        }
    finally:
        flint_ctx.prec = old_prec
