"""Sharp rigorous H_η'(z) at acb point z, via Price's-theorem 2D integrand.

Step 10.1.A of SESSION_HANDOFF.md plan: retire the K_z-based H_η evaluator
(structurally hard to bound, since erf grows like exp((Im P)²) on imaginary
axis); use the Price-derivative formula instead — no inner u-integral, just
a polynomial × Gaussian whose complex extension is bounded by exp(Re).

Formula:
    H_η'(z) = (1 / (π·(1-z²))) · ∫∫ (1 + P'(x)Q'(y)) · exp(-S_z(x,y)) dx dy

with
    A(x,y)   = x² + P(x)² + y² + Q(y)²
    B(x,y)   = xy + P(x)Q(y)
    S_z      = (A - 2zB) / (1 - z²)

For P=Q=0: H_η' = 1/√(1-z²) = arcsin'(z).

Identity used for tail bounds:
    S_z(x,y) = |u-w|²/(2(1-z)) + |u+w|²/(2(1+z))
where u=(x, P(x)), w=(y, Q(y)). For |Re z| < 1, both Re(1/(1-z)) and
Re(1/(1+z)) are positive, so:
    Re(S_z(x,y)) ≥ α'·(x-y)² + β'·(x+y)²  ≥ 2·min(α',β')·(x² + y²)
where α'=Re(1/(2(1-z))) = α/2, β'=Re(1/(2(1+z))) = β/2 (with α, β as
returned by `safe_chunk_constants`). So the tail decay rate is
    λ_decay = min(α, β).

Components:
1. `compute_H_eta_prime_certified(z, P, Pp, Q, Qp, ...)` — main entry.
   Computes nested acb.integral on [-L, L]² (FLINT-certified with rel_tol),
   then adds the rigorous tail bound for |x|>L or |y|>L.

2. `make_v26_P/Pprime` — V26 sign curves (variance-1 / probabilist's bridge).

3. Three validation tests (run in __main__):
   - Test 1: P=Q=0 → 1/√(1-z²) at multiple z in Ω.
   - Test 2: V26 P,Q at z=0.5+0i — cross-check vs h_eta_prime_integral.py.
   - Test 3: finite diff of H_η matches H_η' (sanity for normalisation).
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Callable

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

from grothendieck.proof.certified.bk_rigor import h3_arb
from chunk_constants_safe import safe_chunk_constants
from gaussian_tail_bounds import M_full, M_tail


# ----------------------------------------------------------------------
# V26 curves (acb-friendly: only polynomial arithmetic)
# ----------------------------------------------------------------------
def make_v26_P(eta_arb: arb, sign: int):
    """P(x) = sign · η · h₃(√2·x) / √2.  Accepts arb or acb input."""
    s = arb(sign)
    sqrt2 = arb(2).sqrt()
    def P(x, prec=256):
        return s * eta_arb * h3_arb(sqrt2 * x, prec) / sqrt2
    return P


def make_v26_Pprime(eta_arb: arb, sign: int):
    """P'(x) = sign · η · h₃'(√2·x) = sign · η · (6t² - 3)/(√3·π^{1/4}), t=√2·x.

    Accepts arb or acb input.
    """
    s = arb(sign)
    sqrt2 = arb(2).sqrt()
    def Pp(x, prec=256):
        t = sqrt2 * x
        pi_quarter = arb.pi().sqrt().sqrt()
        denom = arb(3).sqrt() * pi_quarter
        return s * eta_arb * (arb(6) * t * t - arb(3)) / denom
    return Pp


def zero_curve(_x, _prec=256):
    return acb(0)


# ----------------------------------------------------------------------
# Tail bound infrastructure
# ----------------------------------------------------------------------
def compute_J_polynomial_bound_v26(eta_arb: arb) -> list:
    """Polynomial upper bound on |J(x,y)| = |1 + P'(x)Q'(y)| for V26.

    V26 has Q = -P, so J = 1 - P'(x)·P'(y).

    P'(x) = (sign)·η·(6·(√2·x)² − 3)/(√3·π^{1/4}) = K_P · (12x² − 3)
    where K_P = η/(√3·π^{1/4}).

    For real x: |12x² − 3| ≤ 12x² + 3.
    So |P'(x)| ≤ K_P·(12x² + 3) and |J| ≤ 1 + K_P²·(12x² + 3)·(12y² + 3).

    Expanding: (12x² + 3)(12y² + 3) = 144 x²y² + 36 x² + 36 y² + 9.

    Polynomial bound: |J(x,y)| ≤ Σ A_{kj} x^{2k} y^{2j} with terms:
        (0,0): 1 + 9·K_P²
        (1,0): 36·K_P²
        (0,1): 36·K_P²
        (1,1): 144·K_P²
    """
    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P_sq = K_P * K_P
    return [
        (0, 0, arb(1) + arb(9) * K_P_sq),
        (1, 0, arb(36) * K_P_sq),
        (0, 1, arb(36) * K_P_sq),
        (1, 1, arb(144) * K_P_sq),
    ]


def compute_J_polynomial_bound_zero() -> list:
    """For Test 1 (P=Q=0): J ≡ 1, single term (0,0,1)."""
    return [(0, 0, arb(1))]


def compute_tail_bound(
    poly_terms: list,
    lambda_decay: arb,
    L: int,
) -> arb:
    """Closed-form arb upper bound on
        ∫∫_{|x|>L or |y|>L} J̃(x,y) · exp(-λ·(x²+y²)) dx dy
    where J̃(x,y) = Σ A_{kj} x^{2k} y^{2j} (poly_terms).

    Uses union bound: tail ≤ Σ_{kj} A_{kj} · (M_tail(k;λ,L)·M_full(j;λ)
                                            + M_full(k;λ)·M_tail(j;λ,L))
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
# Main entry: certified H_η'(z) via nested acb.integral + tail
# ----------------------------------------------------------------------
def compute_H_eta_prime_certified(
    z: acb,
    P: Callable, Pp: Callable,
    Q: Callable, Qp: Callable,
    J_poly_terms: list,
    L: int = 8,
    prec: int = 200,
    rel_acc_bits: int = 30,
    verbose: bool = False,
) -> acb:
    """Sharp rigorous H_η'(z) at acb-point z.

    Args:
        z: acb point (sharp; can be a ball, but tail bound assumes |Re z| < 1).
        P, Pp, Q, Qp: callables accepting (x, prec) → arb/acb. P,Q are the
            sign-curves; Pp = P', Qp = Q'.
        J_poly_terms: list of (k, j, A) for |J(x,y)| ≤ Σ A·x^{2k}·y^{2j}.
        L: integration half-width. Tail outside [-L,L]² is bounded analytically.
        prec: arb precision (bits).
        rel_acc_bits: target relative accuracy bits for FLINT acb.integral.
            Set lower (e.g. 20-30) for speed; higher (50+) for tightest bounds.
        verbose: print timings.

    Returns:
        acb whose interval contains H_η'(z), with both FLINT-certified
        quadrature error AND a rigorous tail bound for |x|>L or |y|>L.
    """
    flint_ctx.prec = prec

    one_minus_z2 = acb(1) - z * z
    inv_one_minus_z2 = acb(1) / one_minus_z2
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
            S = (A - acb(2) * z * B) * inv_one_minus_z2
            return J * (-S).exp()

        return acb.integral(inner, -L_acb, L_acb,
                            rel_tol=arb(2) ** (-rel_acc_bits))

    if verbose:
        t0 = time.time()
        print(f"  [acb.integral] outer y on [-{L},{L}], rel_acc={rel_acc_bits}b…")

    main = acb.integral(outer, -L_acb, L_acb,
                        rel_tol=arb(2) ** (-rel_acc_bits))

    if verbose:
        print(f"  [acb.integral] done in {time.time() - t0:.1f}s")

    H_prime_main = main / (acb(arb.pi()) * one_minus_z2)

    # ---------- Tail: closed-form Gaussian bound ----------
    # Decay rate: Re(S_z(x,y)) ≥ min(α,β)·(x²+y²) where α=Re(1/(1-z)),
    # β=Re(1/(1+z)).  See module docstring.
    _d_Z, alpha, beta, _z_ub = safe_chunk_constants(z)
    # Lower bound on min(α, β): take .lower() of arb.union which is a sharp
    # lower bound on each interval and hence on min.
    lambda_decay = arb.union(alpha, beta).lower()

    # Add positivity guard
    if not (lambda_decay > arb(0)):
        if verbose:
            print(f"  WARNING: lambda_decay = {lambda_decay} not strictly "
                  f"positive — z = {z} may not satisfy |Re z| < 1.")
        # Conservative: return main with infinite tail (signals user error)
        raise ValueError(f"z = {z} does not satisfy |Re z| < 1; "
                         f"alpha={alpha}, beta={beta}")

    tail_J = compute_tail_bound(J_poly_terms, lambda_decay, L)
    # Divide by π·|1-z²|_lb to get tail of H_η'(z) magnitude
    pi_arb = arb.pi()
    one_minus_z2_abs_lb = one_minus_z2.abs_lower()
    if not (one_minus_z2_abs_lb > arb(0)):
        raise ValueError(f"|1-z²| not strictly positive at z={z}")
    tail_H_prime = tail_J / (pi_arb * one_minus_z2_abs_lb)

    if verbose:
        print(f"  λ_decay = {lambda_decay.str(8)}, "
              f"tail_H_prime ≤ {tail_H_prime.str(6)}")

    # Inflate the acb radius by tail_H_prime on both real and imag.
    # For each component c of H_prime_main: replace by union(c - tail, c + tail).
    re = H_prime_main.real
    im = H_prime_main.imag
    re_certified = arb.union(re - tail_H_prime, re + tail_H_prime)
    im_certified = arb.union(im - tail_H_prime, im + tail_H_prime)
    return acb(re_certified, im_certified)


# ----------------------------------------------------------------------
# Validation tests
# ----------------------------------------------------------------------
def _test_1_zero_curve(prec: int = 200, rel_acc_bits: int = 25, L: int = 6):
    """Test 1: P=Q=0 → H_η'(z) = 1/√(1-z²) at multiple z in Ω."""
    print("=" * 72, flush=True)
    print("TEST 1: P=Q=0 — verify H_η'(z) = 1/√(1-z²) at multiple z in Ω",
          flush=True)
    print("=" * 72, flush=True)
    flint_ctx.prec = prec

    test_points = [
        ("origin",           acb(arb(0), arb(0))),
        ("real interior",    acb(arb("0.5"), arb(0))),
        ("complex interior", acb(arb("0.4"), arb("0.5"))),
    ]

    poly_terms = compute_J_polynomial_bound_zero()  # J=1
    all_pass = True

    for label, z in test_points:
        # Reference: 1/√(1-z²). Use acb.
        one_minus_z2 = acb(1) - z * z
        ref = acb(1) / one_minus_z2.sqrt()
        print(f"  -> {label}: z={z} ...", flush=True)

        try:
            t0 = time.time()
            result = compute_H_eta_prime_certified(
                z=z, P=zero_curve, Pp=zero_curve, Q=zero_curve, Qp=zero_curve,
                J_poly_terms=poly_terms,
                L=L, prec=prec, rel_acc_bits=rel_acc_bits, verbose=False,
            )
            dt = time.time() - t0
        except Exception as e:
            print(f"  {label:24s}  ERROR: {e}", flush=True)
            all_pass = False
            continue

        diff = (result - ref)
        diff_abs = float(diff.abs_upper())
        # Check: ref.real ∈ result.real and ref.imag ∈ result.imag
        re_in = (result.real - ref.real).contains(arb(0))
        im_in = (result.imag - ref.imag).contains(arb(0))
        encloses = re_in and im_in
        status = "✓ ENCLOSES" if encloses else "✗ NO ENCLOSE"
        print(f"  {label:24s}  |err|={diff_abs:.2e}  ({dt:.1f}s)  {status}",
              flush=True)
        if not encloses:
            all_pass = False
            print(f"    ref     = {ref}", flush=True)
            print(f"    result  = {result}", flush=True)
    print(flush=True)
    print("Test 1: " + ("✓ ALL ENCLOSURES" if all_pass else "✗ FAILURE"),
          flush=True)
    return all_pass


def _test_2_v26_vs_heuristic(prec: int = 200, rel_acc_bits: int = 25, L: int = 6):
    """Test 2: V26 P,Q at z=0.5+0i — cross-check vs heuristic GL evaluator."""
    print()
    print("=" * 72)
    print("TEST 2: V26 P,Q at z=0.5 — cross-check vs GL-based heuristic")
    print("=" * 72)
    flint_ctx.prec = prec

    eta_arb = arb("0.01")
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)
    poly_terms = compute_J_polynomial_bound_v26(eta_arb)

    z = acb(arb("0.5"), arb(0))
    print(f"  z = {z}, η = 0.01")
    print()

    t0 = time.time()
    result = compute_H_eta_prime_certified(
        z=z, P=P_plus, Pp=Pp_plus, Q=Q_minus, Qp=Qp_minus,
        J_poly_terms=poly_terms,
        L=L, prec=prec, rel_acc_bits=rel_acc_bits, verbose=True,
    )
    dt = time.time() - t0
    print(f"  Certified H_η'(0.5) = {result}")
    print(f"  time = {dt:.1f}s")
    print()

    # Reference from earlier session (commented in h_eta_prime_acb_integral.py)
    REF = arb("1.1530912169086362")
    print(f"  GL-based reference  = {REF.str(15)} (η=0.01, h_3 V26)")
    re_in = (result.real - REF).contains(arb(0))
    im_in = result.imag.contains(arb(0))
    print(f"  Real ∈ result.real?  {re_in}")
    print(f"  0    ∈ result.imag?  {im_in}")
    diff = (result.real - REF).abs_upper()
    print(f"  |result.real - REF| ≤ {float(diff):.2e}")
    print()
    return re_in and im_in


def _test_3_finite_diff(prec: int = 200, rel_acc_bits: int = 25, L: int = 6):
    """Test 3: H_η' matches finite difference of H_η.

    Uses Test 1's P=Q=0 case where H_η = arcsin and H_η' = 1/√(1-z²).
    Verifies the Price formula's normalisation (no missing 2π factors).

    Because this just re-checks 1/√(1-z²) again, we instead do a direct
    arithmetic identity test: (arcsin'(z) - arcsin'(z+ε))/ε ≈ -arcsin''(z).
    Sanity, no V26 here.
    """
    print()
    print("=" * 72)
    print("TEST 3: P=Q=0 finite-difference sanity")
    print("=" * 72)
    flint_ctx.prec = prec
    z = acb(arb("0.5"), arb(0))
    eps = arb("1e-3")
    z_plus = z + acb(eps, arb(0))
    z_minus = z - acb(eps, arb(0))
    poly_terms = compute_J_polynomial_bound_zero()

    print(f"  Computing H_η'(0.5 ± 1e-3) with P=Q=0...")
    Hp_plus = compute_H_eta_prime_certified(
        z=z_plus, P=zero_curve, Pp=zero_curve, Q=zero_curve, Qp=zero_curve,
        J_poly_terms=poly_terms, L=L, prec=prec, rel_acc_bits=rel_acc_bits,
    )
    Hp_minus = compute_H_eta_prime_certified(
        z=z_minus, P=zero_curve, Pp=zero_curve, Q=zero_curve, Qp=zero_curve,
        J_poly_terms=poly_terms, L=L, prec=prec, rel_acc_bits=rel_acc_bits,
    )
    H_pp_estimate = (Hp_plus - Hp_minus) / (acb(2) * acb(eps))

    # Reference: H_0''(z) = z/(1-z²)^{3/2} = 0.5 / 0.75^{1.5} = 0.7698…
    one_minus_z2 = acb(1) - z * z
    ref_hpp = z / (one_minus_z2 * one_minus_z2.sqrt())
    diff = (H_pp_estimate - ref_hpp).abs_upper()
    print(f"  FD H_0''(0.5)  = {H_pp_estimate}")
    print(f"  Exact H_0''(0.5) = {ref_hpp}")
    print(f"  |diff| ≤ {float(diff):.2e}  (expect ~ε² = 1e-6)")
    pass_fd = float(diff) < 1e-3
    print(f"  Test 3: {'✓ PASS' if pass_fd else '✗ FAIL'}")
    return pass_fd


if __name__ == "__main__":
    PREC = 100  # validation only — production would use 200
    REL_BITS = 20  # ~10⁻⁶ accuracy, plenty for enclosure check
    L_TEST = 6
    flint_ctx.prec = PREC

    print("\n" + "=" * 72, flush=True)
    print("Step 10.1.A: certified sharp H_η'(z) via Price + nested acb.integral",
          flush=True)
    print("=" * 72, flush=True)
    print(f"prec={PREC}, rel_acc_bits={REL_BITS}, L={L_TEST}", flush=True)

    t0 = time.time()
    pass1 = _test_1_zero_curve(prec=PREC, rel_acc_bits=REL_BITS, L=L_TEST)
    pass2 = _test_2_v26_vs_heuristic(prec=PREC, rel_acc_bits=REL_BITS, L=L_TEST)
    pass3 = _test_3_finite_diff(prec=PREC, rel_acc_bits=REL_BITS, L=L_TEST)
    t1 = time.time()

    print()
    print("=" * 72)
    print(f"SUMMARY ({t1 - t0:.0f}s total):")
    print(f"  Test 1 (P=Q=0):                  {'✓' if pass1 else '✗'}")
    print(f"  Test 2 (V26 vs heuristic):       {'✓' if pass2 else '✗'}")
    print(f"  Test 3 (finite-diff sanity):     {'✓' if pass3 else '✗'}")
    print("=" * 72)
    if pass1 and pass2 and pass3:
        print("All tests passed — module is ready for chunk-bound integration.")
        sys.exit(0)
    else:
        print("Some tests failed — investigate before next step.")
        sys.exit(1)
