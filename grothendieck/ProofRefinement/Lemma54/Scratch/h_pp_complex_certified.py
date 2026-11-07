"""Sharp rigorous H_η''(z) at acb point z, via Price's-theorem 2D integrand
+ rigorous Gaussian tail bound.

Price formula:
    H_η''(z) = (1 / (π·D)) · ∫∫ (1 + P'(x)Q'(y)) · exp(-S_z) ·
                                · (2z/D − S_z'(x,y)) dx dy

with
    D = 1 − z²
    A = x² + P² + y² + Q²
    B = xy + PQ
    S_z = (A − 2zB) / D
    S_z' = (2zA − 2(1+z²)B) / D²

For P=Q=0:  H_η''(z) = z/(1−z²)^{3/2} = arcsin''(z).

Tail bound:
    |integrand| ≤ |J| · exp(-Re S_z) · |2z/D − S_z'|
where each polynomial factor in (x², y²) gives finite Hermite-moment tail.

|2z/D − S_z'| ≤ 2|z|/|D| + (2|z|·|A| + 2(1+|z|²)·|B|) / |D|²
|A| ≤ x² + y² + |P²(x)| + |Q²(y)|
|B| ≤ |xy| + |P(x)·Q(y)|  ≤ (x²+y²)/2 + (P²+Q²)/2  (AM-GM)

For V26 (Q = -P, P = K_P·(4x³-3x)):
    |P²(x)| = K_P²·(16x⁶ + 24x⁴ + 9x²)   (rigorous over-bound; flips
                                            sign of -24x⁴ to +24x⁴)

Combining: gives a polynomial bound on |J·(2z/D - S_z')| in (x², y²) of
total bidegree ≤ 8.  Coefficients computed below in
`compute_J_DS_polynomial_bound_v26`.

Validation tests (run in __main__):
  • Test 1 (P=Q=0): H_η''(z) = z/(1-z²)^{3/2} at multiple z.
  • Test 2 (V26): cross-check vs h_eta_pp_integral.py heuristic GL.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Callable, List, Tuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

from grothendieck.proof.certified.bk_rigor import h3_arb
from chunk_constants_safe import safe_chunk_constants
from gaussian_tail_bounds import M_full, M_tail
from h_prime_complex_certified import (
    make_v26_P, make_v26_Pprime, zero_curve,
)


# ----------------------------------------------------------------------
# Polynomial expansion helpers
# ----------------------------------------------------------------------
def _multiply_poly_terms(
    p1: List[Tuple[int, int, arb]],
    p2: List[Tuple[int, int, arb]],
) -> List[Tuple[int, int, arb]]:
    """Multiply two (k, j, A) polynomial lists, summing duplicate (k,j)."""
    accum = {}
    for (k1, j1, A1) in p1:
        for (k2, j2, A2) in p2:
            key = (k1 + k2, j1 + j2)
            if key in accum:
                accum[key] = accum[key] + A1 * A2
            else:
                accum[key] = A1 * A2
    return [(k, j, A) for (k, j), A in accum.items()]


def _scale_poly(
    p: List[Tuple[int, int, arb]], scalar: arb,
) -> List[Tuple[int, int, arb]]:
    return [(k, j, A * scalar) for (k, j, A) in p]


def _add_polys(
    p1: List[Tuple[int, int, arb]],
    p2: List[Tuple[int, int, arb]],
) -> List[Tuple[int, int, arb]]:
    accum = {}
    for (k, j, A) in p1 + p2:
        key = (k, j)
        if key in accum:
            accum[key] = accum[key] + A
        else:
            accum[key] = A
    return [(k, j, A) for (k, j), A in accum.items()]


# ----------------------------------------------------------------------
# Polynomial bound on |J(x,y) · (2z/D − S_z'(x,y))| at fixed z
# ----------------------------------------------------------------------
def compute_J_DS_polynomial_bound_v26(
    eta_arb: arb, z_re_ub: arb, z_im_ub: arb, D_lb: arb,
) -> List[Tuple[int, int, arb]]:
    """Polynomial bound (list of (k, j, A_kj)) for V26 sign curves on
        |J(x,y) · (2z/D − S_z'(x,y))| ≤ Σ A_{kj} · x^{2k} · y^{2j}.

    Args:
        eta_arb: η for V26.
        z_re_ub: arb upper bound on |Re z|.
        z_im_ub: arb upper bound on |Im z|.
        D_lb:    arb lower bound on |D| = |1-z²|.

    Returns: list of (k, j, A_kj) with A_kj ≥ 0.
    """
    # |z| ≤ √(Re² + Im²) — but use z_abs_ub = |z|.upper() if available;
    # here we just bound |z| by the diagonal.
    z_abs_ub = (z_re_ub * z_re_ub + z_im_ub * z_im_ub).sqrt()
    one_plus_z2_ub = arb(1) + z_abs_ub * z_abs_ub
    inv_D = arb(1) / D_lb
    inv_D2 = inv_D * inv_D

    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P_sq = K_P * K_P

    # |J| ≤ 1 + |P'(x)·Q'(y)|.  For Q=-P: |P'(x)·Q'(y)| = |P'(x)|·|P'(y)|.
    # |P'(x)| ≤ K_P·(12x²+3) → |P'(x)·P'(y)| ≤ K_P²·(12x²+3)·(12y²+3)
    #                            = K_P²·(144 x²y² + 36 x² + 36 y² + 9)
    poly_J = [
        (0, 0, arb(1) + arb(9) * K_P_sq),
        (1, 0, arb(36) * K_P_sq),
        (0, 1, arb(36) * K_P_sq),
        (1, 1, arb(144) * K_P_sq),
    ]

    # Polynomial bound on |A| = x² + |P²(x)| + y² + |Q²(y)|
    #   |P²(x)| ≤ K_P² · (16x⁶ + 24x⁴ + 9x²)
    poly_A = [
        (0, 0, arb(0)),                         # constant
        (1, 0, arb(1) + arb(9) * K_P_sq),       # x²
        (0, 1, arb(1) + arb(9) * K_P_sq),       # y²
        (2, 0, arb(24) * K_P_sq),                # x⁴
        (0, 2, arb(24) * K_P_sq),                # y⁴
        (3, 0, arb(16) * K_P_sq),                # x⁶
        (0, 3, arb(16) * K_P_sq),                # y⁶
    ]

    # Polynomial bound on |B| = |xy + P·Q| ≤ |xy| + |P||Q|
    #   |xy| ≤ (x²+y²)/2 (AM-GM)
    #   |P(x)·Q(y)| = |P(x)|·|P(y)| ≤ (P²(x) + P²(y))/2 = K_P²·(...)
    #   |P²(x) + P²(y)|/2 ≤ K_P²·(16x⁶+24x⁴+9x²+16y⁶+24y⁴+9y²)/2
    half = arb(1) / arb(2)
    poly_B = [
        (1, 0, half),                                  # x²/2
        (0, 1, half),                                  # y²/2
        (1, 0, arb(9) * K_P_sq * half),                 # 4.5·K_P²·x²
        (0, 1, arb(9) * K_P_sq * half),                 # 4.5·K_P²·y²
        (2, 0, arb(24) * K_P_sq * half),                # 12·K_P²·x⁴
        (0, 2, arb(24) * K_P_sq * half),                # 12·K_P²·y⁴
        (3, 0, arb(16) * K_P_sq * half),                # 8·K_P²·x⁶
        (0, 3, arb(16) * K_P_sq * half),                # 8·K_P²·y⁶
    ]
    # Consolidate poly_B (combines the two x² entries)
    poly_B = _add_polys(poly_B, [])

    # |2z/D − S_z'| ≤ 2|z|/|D| + (2|z|·|A| + 2·(1+|z|²)·|B|)/|D|²
    # = c0 (constant) + cA·|A| + cB·|B|
    c0 = arb(2) * z_abs_ub * inv_D
    cA = arb(2) * z_abs_ub * inv_D2
    cB = arb(2) * one_plus_z2_ub * inv_D2

    # Build poly for "(c0 + cA·A + cB·B)" — the secondary factor
    poly_secondary = (
        [(0, 0, c0)]
        + _scale_poly(poly_A, cA)
        + _scale_poly(poly_B, cB)
    )
    poly_secondary = _add_polys(poly_secondary, [])

    # Full polynomial bound: poly_J × poly_secondary
    poly_total = _multiply_poly_terms(poly_J, poly_secondary)
    poly_total = _add_polys(poly_total, [])
    return poly_total


def compute_J_DS_polynomial_bound_zero(
    z_re_ub: arb, z_im_ub: arb, D_lb: arb,
) -> List[Tuple[int, int, arb]]:
    """For P=Q=0 (Test 1): J=1, A=x²+y², B=xy. |xy| ≤ (x²+y²)/2."""
    z_abs_ub = (z_re_ub * z_re_ub + z_im_ub * z_im_ub).sqrt()
    one_plus_z2_ub = arb(1) + z_abs_ub * z_abs_ub
    inv_D = arb(1) / D_lb
    inv_D2 = inv_D * inv_D
    half = arb(1) / arb(2)

    c0 = arb(2) * z_abs_ub * inv_D
    cA = arb(2) * z_abs_ub * inv_D2
    cB = arb(2) * one_plus_z2_ub * inv_D2

    # poly_A = x² + y², poly_B = (x²+y²)/2
    poly_secondary = [
        (0, 0, c0),
        (1, 0, cA + cB * half),
        (0, 1, cA + cB * half),
    ]
    return poly_secondary


# ----------------------------------------------------------------------
# Tail bound (uses gaussian_tail_bounds.compute_tail_bound_polynomial)
# ----------------------------------------------------------------------
def _compute_tail(
    poly_terms: List[Tuple[int, int, arb]],
    lambda_decay: arb, L: int,
) -> arb:
    """Closed-form arb upper bound on
        ∫∫_{|x|>L or |y|>L} J̃(x,y) · exp(-λ·(x²+y²)) dx dy.
    """
    L_arb = arb(L)
    tail = arb(0)
    for (k, j, A) in poly_terms:
        Mt_k = M_tail(k, lambda_decay, L_arb)
        Mf_k = M_full(k, lambda_decay)
        Mt_j = M_tail(j, lambda_decay, L_arb)
        Mf_j = M_full(j, lambda_decay)
        tail = tail + A * (Mt_k * Mf_j + Mf_k * Mt_j)
    return tail


# ----------------------------------------------------------------------
# Sharp rigorous H_η''(z) entry point
# ----------------------------------------------------------------------
def compute_H_eta_pp_certified(
    z: acb,
    P: Callable, Pp: Callable, Q: Callable, Qp: Callable,
    P_kind: str,                          # "v26" or "zero" — picks tail poly
    eta_arb: arb,
    L: int = 6,
    prec: int = 200,
    rel_acc_bits: int = 30,
    verbose: bool = False,
) -> acb:
    """Sharp rigorous H_η''(z) at acb-point z."""
    flint_ctx.prec = prec

    D = acb(1) - z * z
    inv_D = acb(1) / D
    inv_D2 = inv_D * inv_D
    z2 = z * z
    one_plus_z2 = acb(1) + z2
    L_acb = acb(arb(L))

    # ---------- Main: nested acb.integral on [-L, L]² ----------
    def outer(y, _analytic):
        Q_y = Q(y, prec)
        Qp_y = Qp(y, prec)
        y2 = y * y
        Q2 = Q_y * Q_y

        def inner(x, _analytic):
            P_x = P(x, prec)
            Pp_x = Pp(x, prec)
            A = x * x + P_x * P_x + y2 + Q2
            B = x * y + P_x * Q_y
            J = acb(1) + Pp_x * Qp_y
            S = (A - acb(2) * z * B) * inv_D
            Sprime = (acb(2) * z * A - acb(2) * one_plus_z2 * B) * inv_D2
            return J * (-S).exp() * (acb(2) * z * inv_D - Sprime)

        return acb.integral(inner, -L_acb, L_acb,
                            rel_tol=arb(2) ** (-rel_acc_bits))

    if verbose:
        t0 = time.time()
        print(f"  [H_η''] outer y on [-{L},{L}], rel_acc={rel_acc_bits}b…",
              flush=True)
    main = acb.integral(outer, -L_acb, L_acb,
                        rel_tol=arb(2) ** (-rel_acc_bits))
    if verbose:
        print(f"  [H_η''] done in {time.time() - t0:.1f}s", flush=True)

    H_pp_main = main / (acb(arb.pi()) * D)

    # ---------- Tail bound ----------
    _d_Z, alpha, beta, _z_ub = safe_chunk_constants(z)
    lambda_decay = arb.union(alpha, beta).lower()
    if not (lambda_decay > arb(0)):
        raise ValueError(f"lambda_decay non-positive at z={z}; "
                         f"alpha={alpha}, beta={beta}")

    z_re_ub = z.real.abs_upper()
    z_im_ub = z.imag.abs_upper()
    D_lb = D.abs_lower()
    if not (D_lb > arb(0)):
        raise ValueError(f"|D| not positive at z={z}")

    if P_kind == "v26":
        poly_terms = compute_J_DS_polynomial_bound_v26(
            eta_arb, z_re_ub, z_im_ub, D_lb)
    elif P_kind == "zero":
        poly_terms = compute_J_DS_polynomial_bound_zero(
            z_re_ub, z_im_ub, D_lb)
    else:
        raise ValueError(f"unknown P_kind: {P_kind}")

    tail_J_DS = _compute_tail(poly_terms, lambda_decay, L)
    pi_arb = arb.pi()
    tail_H_pp = tail_J_DS / (pi_arb * D_lb)

    if verbose:
        print(f"  [H_η''] λ_decay={lambda_decay.str(8)}, "
              f"tail_H_pp ≤ {tail_H_pp.str(6)}", flush=True)

    re = H_pp_main.real
    im = H_pp_main.imag
    return acb(arb.union(re - tail_H_pp, re + tail_H_pp),
                arb.union(im - tail_H_pp, im + tail_H_pp))


# ----------------------------------------------------------------------
# Validation
# ----------------------------------------------------------------------
def _test_zero_curve(prec: int = 100, rel_acc_bits: int = 22, L: int = 6):
    print("=" * 72, flush=True)
    print("TEST 1: P=Q=0 — H_η''(z) = z/(1-z²)^{3/2}", flush=True)
    print("=" * 72, flush=True)
    flint_ctx.prec = prec

    test_points = [
        ("origin",           acb(arb(0), arb(0))),
        ("real interior",    acb(arb("0.5"), arb(0))),
        ("complex interior", acb(arb("0.4"), arb("0.5"))),
    ]
    eta_arb = arb("0.01")
    all_pass = True
    for label, z in test_points:
        ref = z / ((acb(1) - z * z) * (acb(1) - z * z).sqrt())
        print(f"  -> {label}: z={z}", flush=True)
        try:
            t0 = time.time()
            result = compute_H_eta_pp_certified(
                z=z, P=zero_curve, Pp=zero_curve, Q=zero_curve, Qp=zero_curve,
                P_kind="zero", eta_arb=eta_arb,
                L=L, prec=prec, rel_acc_bits=rel_acc_bits, verbose=False,
            )
            dt = time.time() - t0
        except Exception as e:
            print(f"  ERROR: {e}", flush=True)
            import traceback
            traceback.print_exc()
            all_pass = False
            continue
        re_in = (result.real - ref.real).contains(arb(0))
        im_in = (result.imag - ref.imag).contains(arb(0))
        encloses = re_in and im_in
        diff = float((result - ref).abs_upper())
        status = "✓ ENCLOSES" if encloses else "✗ NO ENCLOSE"
        print(f"  {label:24s}  |err|={diff:.2e}  ({dt:.1f}s)  {status}",
              flush=True)
        if not encloses:
            all_pass = False
            print(f"    ref = {ref}", flush=True)
            print(f"    res = {result}", flush=True)
    print(flush=True)
    print("Test 1: " + ("✓ ALL ENCLOSURES" if all_pass else "✗ FAILURE"),
          flush=True)
    return all_pass


def _test_v26(prec: int = 100, rel_acc_bits: int = 22, L: int = 6):
    print(flush=True)
    print("=" * 72, flush=True)
    print("TEST 2: V26 P,Q at z=0.5 — H_η''(0.5) ≈ arcsin''(0.5) ± O(η²)",
          flush=True)
    print("=" * 72, flush=True)
    flint_ctx.prec = prec
    eta_arb = arb("0.01")
    P = make_v26_P(eta_arb, +1)
    Pp = make_v26_Pprime(eta_arb, +1)
    Q = make_v26_P(eta_arb, -1)
    Qp = make_v26_Pprime(eta_arb, -1)

    z = acb(arb("0.5"), arb(0))
    arcsin_pp_ref = z / ((acb(1) - z * z) * (acb(1) - z * z).sqrt())
    print(f"  arcsin''(0.5) = {arcsin_pp_ref.real.str(15)}", flush=True)

    t0 = time.time()
    result = compute_H_eta_pp_certified(
        z=z, P=P, Pp=Pp, Q=Q, Qp=Qp, P_kind="v26", eta_arb=eta_arb,
        L=L, prec=prec, rel_acc_bits=rel_acc_bits, verbose=True,
    )
    dt = time.time() - t0
    print(f"  H_η''(0.5) = {result}", flush=True)
    print(f"  time = {dt:.1f}s", flush=True)
    diff = (result.real - arcsin_pp_ref.real).abs_upper()
    print(f"  |H_η''(0.5) - arcsin''(0.5)| ≤ {float(diff):.2e}", flush=True)
    pass2 = float(diff) < 1e-2
    print(f"  Test 2: {'✓ PASS' if pass2 else '✗ FAIL'}", flush=True)
    return pass2


if __name__ == "__main__":
    PREC = 100
    REL_BITS = 22
    L_TEST = 6
    flint_ctx.prec = PREC
    print("\n" + "=" * 72, flush=True)
    print("Sharp H_η''(z) via Price-formula nested acb.integral + tail bound",
          flush=True)
    print("=" * 72, flush=True)
    print(f"prec={PREC}, rel_acc_bits={REL_BITS}, L={L_TEST}", flush=True)
    t0 = time.time()
    pass1 = _test_zero_curve(prec=PREC, rel_acc_bits=REL_BITS, L=L_TEST)
    pass2 = _test_v26(prec=PREC, rel_acc_bits=REL_BITS, L=L_TEST)
    t1 = time.time()
    print(flush=True)
    print("=" * 72, flush=True)
    print(f"SUMMARY ({t1 - t0:.0f}s):", flush=True)
    print(f"  Test 1 (P=Q=0):          {'✓' if pass1 else '✗'}", flush=True)
    print(f"  Test 2 (V26 vs arcsin''): {'✓' if pass2 else '✗'}", flush=True)
    print("=" * 72, flush=True)
    sys.exit(0 if pass1 and pass2 else 1)
