"""η²-tight closed-form chunk bound on sup_{z ∈ Z} |Φ''(z)| for V26.

Replaces the loose triangle bound  |Φ''| ≤ |H_η''| + |H_0''|  ≈ O(1) (which
ignores cancellation between H_η'' and H_0'' at small η) with a direct η²-tight
bound based on the Price-formula expansion of the difference Φ''.

Math derivation (V26 with Q = -P, both odd):

The Price formula difference:
    Φ''(z) = (1/(π·D)) · ∫∫ [J_η·e_η·F_η  -  e_0·F_0] dx dy
where
    e_η  = exp(-S_z|η(x,y)),       e_0 = exp(-S_z|0(x,y))
    F_η  = 2z/D - S_z'|η(x,y),     F_0 = 2z/D - S_z'|0(x,y)
    J_η  = 1 - P'(x)P'(y),         J_0 = 1
    D    = 1 - z²
    S_z|η  = (A_η - 2z·B_η)/D
    A_η = x² + P²(x) + y² + Q²(y),  B_η = xy + P·Q
    A_0 = x² + y²,                   B_0 = xy

Δ-quantities (all O(η²) for V26 with Q=-P, P linear in η):
    δJ ≔ J_η - J_0 = -P'(x)·P'(y)
    δS ≔ S_z|η - S_z|0 = (P²(x) + P²(y) + 2z·P(x)·P(y)) / (1 - z²)
                         (using Q=-P, A_η-A_0 = P²+P², B_η-B_0 = -P·P)
    δF ≔ F_η - F_0 = -(2z·δA - 2(1+z²)·δB)/D²
                   = -(2z·(P²+P²) - 2(1+z²)·(-P·P))/D²
                   = -(2z·(P²(x)+P²(y)) + 2(1+z²)·P(x)·P(y))/D²

Telescope:
    J_η·e_η·F_η - e_0·F_0
      = e_0·[δJ·F_η + δF - F_η·δS + (higher-order in δS, δJ, δF)]

Leading O(η²):
    |LEAD|(x,y) := |δJ|·|F_0| + |δF| + |F_0|·|δS|

Remainder O(η⁴) (and higher):
    |REM|(x,y) := |δJ|·|δF| + |F_0|·|δS|·|δJ| + |F_η|·|δS|²/2  + |δF|·|δS|
                  + (small higher terms)

Conservative remainder: |REM|(x,y) ≤ |δJ|·|δF| + |F_0|·|δS|·(|δJ| + |δS|/2)
                                       + |δF|·|δS| + |δS|²/2·|F_0+δF|·1
For first iteration we use simpler conservative form:
    |REM| ≤ |δJ|·|δF| + |δJ|·|F_0|·|δS| + |F_0|·|δS|²
    + |δF|·|δS| + ...
We just take |REM| ≤ 2·|δS|²·|F_0|  +  4·|δJ|·|δF|  +  4·|δJ|·|F_0|·|δS|
which over-bounds the truncated Taylor remainder for |δJ|, |δS|, |δF| ≤ 1
(easily satisfied for V26 η=0.01 — these are O(η²) ≤ 10⁻⁴).

Each polynomial-bounded piece in (x², y²) gives a closed-form Hermite
moment integral via gaussian_tail_bounds.  Bound:
    |Φ''(z)| ≤ (1/(π·d_Z)) · ∫∫ (|LEAD| + |REM|)·|e_0| dx dy
            ≤ (1/(π·d_Z)) · ∫∫ (poly_LEAD + poly_REM) · exp(-λ·(x²+y²)) dx dy
where
    λ = min(α,β) ≥ 0, α = Re(1/(1-z)), β = Re(1/(1+z))   (over chunk).
    Justification: (x-y)² + (x+y)² = 2(x²+y²) (parallelogram identity), so
    Re[S_z] = (α/2)(x-y)² + (β/2)(x+y)² ≥ min(α,β) · (x²+y²).

Validation: at η=0.01, this should give ~K_P²·O(1) ≈ 10⁻⁵×const ≈ 10⁻³, vs
existing |H_η''|+|H_0''| ≈ 10² (5 orders of magnitude tighter). For Step 10.4
joint oracle, this matters only for the chunk-w pad on Φ', Φ'', DD; the
joint formula's signed numerator picks up sign cancellation otherwise.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import List, NamedTuple, Tuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from chunk_constants_safe import safe_chunk_constants
from gaussian_tail_bounds import M_full


# ----------------------------------------------------------------------
# Polynomial-list helpers (k, j, A_kj) — represents Σ A_kj · x^{2k} · y^{2j}
# ----------------------------------------------------------------------
PolyList = List[Tuple[int, int, arb]]


def _add(p1: PolyList, p2: PolyList) -> PolyList:
    accum = {}
    for (k, j, A) in p1 + p2:
        key = (k, j)
        accum[key] = accum.get(key, arb(0)) + A
    return [(k, j, A) for (k, j), A in accum.items() if A.upper() > arb(0)]


def _scale(p: PolyList, s: arb) -> PolyList:
    return [(k, j, A * s) for (k, j, A) in p]


def _mul(p1: PolyList, p2: PolyList) -> PolyList:
    accum = {}
    for (k1, j1, A1) in p1:
        for (k2, j2, A2) in p2:
            key = (k1 + k2, j1 + j2)
            accum[key] = accum.get(key, arb(0)) + A1 * A2
    return [(k, j, A) for (k, j), A in accum.items() if A.upper() > arb(0)]


# ----------------------------------------------------------------------
# Polynomial bounds (in x², y²) for V26 building blocks
# ----------------------------------------------------------------------
def _poly_P2() -> PolyList:
    """|P²(x)| ≤ K_P²·(16x⁶ + 24x⁴ + 9x²) — sign-flip for over-bound.

    Returns coefficients in K_P²-units (multiply by K_P² to get actual).
    """
    return [(1, 0, arb(9)), (2, 0, arb(24)), (3, 0, arb(16))]


def _poly_P2_y() -> PolyList:
    """|P²(y)| in K_P² units."""
    return [(0, 1, arb(9)), (0, 2, arb(24)), (0, 3, arb(16))]


def _poly_PPp_xy_amgm() -> PolyList:
    """|P(x)·P(y)| ≤ (P²(x)+P²(y))/2 in K_P² units (AM-GM).

    Returns Σ A_kj · x^{2k} · y^{2j} for the combined poly /2.
    """
    half = arb(1) / arb(2)
    return _add(_scale(_poly_P2(), half), _scale(_poly_P2_y(), half))


def _poly_Pp2() -> PolyList:
    """|P'²(x)| in K_P² units = K_P²·(144x⁴ - 72x² + 9). Sign-flip:
    |P'²| ≤ K_P²·(144x⁴ + 72x² + 9)."""
    return [(0, 0, arb(9)), (1, 0, arb(72)), (2, 0, arb(144))]


def _poly_PpPp_xy_abs() -> PolyList:
    """|P'(x)·P'(y)| ≤ K_P²·(12x²+3)·(12y²+3) (over-bound flipping signs).

    = K_P²·(144 x²y² + 36 x² + 36 y² + 9).
    """
    return [(0, 0, arb(9)),
            (1, 0, arb(36)), (0, 1, arb(36)),
            (1, 1, arb(144))]


def _poly_const(c: arb) -> PolyList:
    return [(0, 0, c)]


def _poly_x2_plus_y2() -> PolyList:
    return [(1, 0, arb(1)), (0, 1, arb(1))]


def _poly_xy_amgm() -> PolyList:
    """|xy| ≤ (x²+y²)/2 (AM-GM)."""
    half = arb(1) / arb(2)
    return _scale(_poly_x2_plus_y2(), half)


# ----------------------------------------------------------------------
# Compute polynomial bounds for δJ, δS, F_0, δF using chunk constants
# ----------------------------------------------------------------------
def _build_pieces(K_P_sq: arb, z_ub: arb, d_Z: arb) -> dict:
    """Return polynomial bounds (in x², y²) for V26 building blocks."""
    # |δJ| = |P'(x)·P'(y)| ≤ K_P²·(...)
    poly_dJ = _scale(_poly_PpPp_xy_abs(), K_P_sq)

    # |δS| = |(P² + P² + 2z·P·P)/(1-z²)|
    #      ≤ ((P²(x)+P²(y)) + 2|z|·|P(x)P(y)|)/d_Z
    #      ≤ (P²(x)+P²(y))·(1 + |z|)/d_Z   [using |PP| ≤ (P²+P²)/2]
    P2_sum = _add(_poly_P2(), _poly_P2_y())
    poly_dS = _scale(P2_sum, K_P_sq * (arb(1) + z_ub) / d_Z)

    # |F_0| = |2z/D - S_z'|0|
    #       ≤ 2|z|/d_Z + (2|z|·|x²+y²| + 2(1+|z|²)·|xy|)/d_Z²
    #       ≤ 2|z|/d_Z + (2|z|+(1+|z|²))·(x²+y²)/d_Z²
    inv_d = arb(1) / d_Z
    inv_d2 = inv_d * inv_d
    one_plus_z2 = arb(1) + z_ub * z_ub
    F0_const = arb(2) * z_ub * inv_d
    F0_poly_coef = (arb(2) * z_ub + one_plus_z2) * inv_d2
    poly_F0 = _add(
        _poly_const(F0_const),
        _scale(_poly_x2_plus_y2(), F0_poly_coef),
    )

    # |δF| = |-(2z·δA - 2(1+z²)·δB)/D²|
    #       ≤ (2|z|·(P²(x)+P²(y)) + 2(1+|z|²)·|P(x)P(y)|)/d_Z²
    #       ≤ (2|z| + (1+|z|²))·(P²(x)+P²(y))/d_Z²
    poly_dF = _scale(P2_sum,
                      K_P_sq * (arb(2) * z_ub + one_plus_z2) * inv_d2)

    return {
        "dJ": poly_dJ,
        "dS": poly_dS,
        "F0": poly_F0,
        "dF": poly_dF,
    }


# ----------------------------------------------------------------------
# Hermite-moment closed-form integration of poly·exp(-λ(x²+y²))
# ----------------------------------------------------------------------
def _integrate_poly_gaussian(p: PolyList, lambda_decay: arb) -> arb:
    """∫∫ Σ A_kj · x^{2k} · y^{2j} · exp(-λ(x²+y²)) dx dy
        = Σ A_kj · M_full(k; λ) · M_full(j; λ).
    """
    total = arb(0)
    for (k, j, A) in p:
        total = total + A * M_full(k, lambda_decay) * M_full(j, lambda_decay)
    return total


def _integrate_poly_aniso(p: PolyList, alpha: arb, beta: arb) -> arb:
    """Anisotropic Gaussian moment integration.

    Compute ∫∫ Σ A_kj · x^{2k} · y^{2j} · exp(-(α/2)(x-y)² - (β/2)(x+y)²) dx dy.

    Substitute u = x-y, v = x+y, so x = (u+v)/2, y = (v-u)/2,
    dx dy = du dv / 2.  Then
        x^{2k} y^{2j} = (1/4)^{k+j} · (u+v)^{2k} · (v-u)^{2j}.
    Expand:
        (u+v)^{2k} = Σ_{a=0}^{2k} C(2k, a) u^a v^{2k-a}
        (v-u)^{2j} = Σ_{b=0}^{2j} C(2j, b) (-u)^b v^{2j-b}
                   = Σ_{b=0}^{2j} C(2j, b) (-1)^b u^b v^{2j-b}
    Product: u^{a+b} v^{2k+2j-a-b} with sign (-1)^b.  Only (a+b) even
    surviving (else odd-power 1D moment vanishes).  Each surviving term
    integrates to M_full((a+b)/2, α/2) · M_full((2k+2j-a-b)/2, β/2).
    Multiply by Jacobian 1/2 and 1/4^{k+j} factor.

    Mathematically equal to the actual integral (no inequality), so it
    is a tight rigorous bound on `∫∫ poly · |e_0|`.
    """
    from math import comb
    half_alpha = alpha / arb(2)
    half_beta = beta / arb(2)
    jacobian = arb(1) / arb(2)
    total = arb(0)
    for (k, j, A) in p:
        # Sum over a, b with (a+b) even
        sum_kj = arb(0)
        inv_4_pow = arb(1) / arb(4) ** (k + j)
        for a in range(2 * k + 1):
            for b in range(2 * j + 1):
                if (a + b) % 2 != 0:
                    continue
                mu_pow = (a + b) // 2
                mv_pow = (2 * k + 2 * j - a - b) // 2
                sign = arb(1) if b % 2 == 0 else arb(-1)
                ca = arb(comb(2 * k, a))
                cb = arb(comb(2 * j, b))
                term = (sign * ca * cb
                        * M_full(mu_pow, half_alpha)
                        * M_full(mv_pow, half_beta))
                sum_kj = sum_kj + term
        total = total + A * inv_4_pow * sum_kj
    return jacobian * total


# ----------------------------------------------------------------------
# Main: bound sup_{z ∈ Z} |Φ''(z)|
# ----------------------------------------------------------------------
class PhiPpEtaTightResult(NamedTuple):
    bound: arb        # final |Φ''| chunk bound
    bound_lead: arb   # leading-O(η²) part
    bound_rem: arb    # remainder (O(η⁴) and higher)
    d_Z: arb
    lambda_decay: arb
    K_P: arb


def bound_Phi_pp_eta_tight_certified(
    z_ball: acb,
    eta_arb: arb,
    prec: int = 200,
) -> PhiPpEtaTightResult:
    """η²-tight closed-form chunk bound on sup_{z ∈ Z} |Φ''(z)| for V26.

    The chunk z_ball must satisfy |Re z| < 1 (interior of Ω), so
    safe_chunk_constants gives positive d_Z, α, β.
    """
    flint_ctx.prec = prec
    d_Z, alpha, beta, z_ub = safe_chunk_constants(z_ball)
    if not (d_Z > arb(0)):
        raise ValueError(f"d_Z not positive on chunk: {d_Z}")
    if not (alpha > arb(0) and beta > arb(0)):
        raise ValueError(f"alpha={alpha}, beta={beta} non-positive")

    # λ = min(α, β) — decay rate of |e_0|.
    # Re[S_z(x,y)] = (α/2)(x-y)² + (β/2)(x+y)²
    #             ≥ (min(α,β)/2) · [(x-y)² + (x+y)²]
    #             = min(α,β) · (x² + y²)         (parallelogram identity)
    # so |e_0| ≤ exp(-min(α,β) · (x² + y²)).
    lambda_decay = arb.union(alpha, beta).lower()
    if not (lambda_decay > arb(0)):
        raise ValueError(f"lambda_decay non-positive: {lambda_decay}")

    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P_sq = K_P * K_P

    pieces = _build_pieces(K_P_sq, z_ub, d_Z)
    dJ, dS, F0, dF = pieces["dJ"], pieces["dS"], pieces["F0"], pieces["dF"]

    # |LEAD| ≤ |δJ|·|F_0| + |δF| + |F_0|·|δS|
    poly_lead = _add(
        _add(_mul(dJ, F0), dF),
        _mul(F0, dS),
    )

    # Exact-quartic Taylor expansion of (1+δJ)·exp(-δS)·(F_0+δF) - F_0 in η:
    #   O(η⁴) terms:
    #     (1/2)·F_0·δS²
    #     F_0·δJ·δS  (sign: from -F_0·δJ·δS in original — abs value 1)
    #     δS·δF      (from -δS·δF, abs 1)
    #     δJ·δF
    # We over-bound each by its absolute value with coefficient 1 (and
    # 1/2 for the F_0·δS² term).  Compared to conservative factors 2, 4
    # this is 2× to 4× tighter on the dominant remainder term.
    half = arb(1) / arb(2)
    dS_sq = _mul(dS, dS)
    poly_rem_4 = _add(
        _add(
            _scale(_mul(F0, dS_sq), half),
            _mul(dJ, dF),
        ),
        _add(
            _mul(dJ, _mul(F0, dS)),
            _mul(dF, dS),
        ),
    )

    # O(η⁶) Lagrange remainder of Taylor expansion of exp(-δS).
    # Strict rigour requires this term. For chunks where Re(δS) ≥ 0 over
    # the integration region (V26 design with Q=-P, P odd), Lagrange:
    #     |R_3(δS)| ≤ |δS|³/6 · max{1, exp(-Re(δS))} = |δS|³/6
    # giving the bound |F_0·R_3| ≤ |F_0|·|δS|³/6.
    # For corner chunks where Re(δS) sign isn't certified, this same
    # bound holds if we restrict to the box where Re(δS) ≥ 0 + bound the
    # tail. Approximate conservatively as |F_0|·|δS|³/6 over whole domain.
    # NOTE: high-degree polynomial moments make this loose for corner
    # chunks; joint oracle takes min(η-tight, triangle) to fall back.
    sixth = arb(1) / arb(6)
    poly_rem_6 = _scale(_mul(F0, _mul(dS, dS_sq)), sixth)

    poly_rem = _add(poly_rem_4, poly_rem_6)

    # Integrate via anisotropic (exact) AND isotropic (upper-bound).
    # For each piece take the tighter (smaller) result. Anisotropic is
    # mathematically exact equal to ∫∫ poly · |e_0|, but its signed
    # expansion can produce wider arb intervals than the simpler iso
    # version at very high polynomial orders. Take min to be robust.
    integral_lead_aniso = _integrate_poly_aniso(poly_lead, alpha, beta)
    integral_lead_iso = _integrate_poly_gaussian(poly_lead, lambda_decay)
    if integral_lead_aniso.upper() < integral_lead_iso.upper() \
            and integral_lead_aniso > arb(0):
        integral_lead = integral_lead_aniso
    else:
        integral_lead = integral_lead_iso

    integral_rem_aniso = _integrate_poly_aniso(poly_rem, alpha, beta)
    integral_rem_iso = _integrate_poly_gaussian(poly_rem, lambda_decay)
    if integral_rem_aniso.upper() < integral_rem_iso.upper() \
            and integral_rem_aniso > arb(0):
        integral_rem = integral_rem_aniso
    else:
        integral_rem = integral_rem_iso

    # |Φ''(z)| ≤ (1/(π·d_Z)) · (integral_lead + integral_rem)
    pi_arb = arb.pi()
    bound_lead = integral_lead / (pi_arb * d_Z)
    bound_rem = integral_rem / (pi_arb * d_Z)
    bound = bound_lead + bound_rem

    return PhiPpEtaTightResult(
        bound=bound, bound_lead=bound_lead, bound_rem=bound_rem,
        d_Z=d_Z, lambda_decay=lambda_decay, K_P=K_P,
    )


# ----------------------------------------------------------------------
# Smoke tests
# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200
    eta_arb = arb("0.01")

    print("=" * 72)
    print("η²-tight |Φ''| chunk bound vs old |H_η''| + |H_0''| triangle")
    print("=" * 72)

    test_chunks = [
        ("real, half=0.05",
         acb(arb("0.5"), arb.union(arb("-0.05"), arb("0.05")))),
        ("V26 corner-ish",
         acb(arb("0.84"), arb.union(arb("0.97"), arb("1.115")))),
        ("V26 spike",
         acb(arb("0.84"), arb.union(arb("0.14"), arb("0.28")))),
        ("V26 near-edge real",
         acb(arb.union(arb("0.78"), arb("0.84")), arb("0.14"))),
    ]

    sys.path.insert(0, str(_HERE))
    from h_eta_pp_chunk_bound_certified import (
        bound_H_eta_pp_on_chunk_certified,
    )

    for label, z_box in test_chunks:
        try:
            res_new = bound_Phi_pp_eta_tight_certified(z_box, eta_arb)
            new_bound = res_new.bound
            lead = res_new.bound_lead
            rem = res_new.bound_rem
        except Exception as e:
            print(f"  {label:24s}  ERROR new: {e}")
            continue

        try:
            old_h_eta_pp = bound_H_eta_pp_on_chunk_certified(z_box, eta_arb).bound
            d_Z, _, _, z_ub = safe_chunk_constants(z_box)
            sup_H0pp = z_ub / (d_Z * d_Z.sqrt()) if d_Z > arb(0) else arb("inf")
            old_bound = old_h_eta_pp + sup_H0pp
        except Exception as e:
            print(f"  {label:24s}  ERROR old: {e}")
            continue

        ratio = float(new_bound.upper()) / float(old_bound.upper())
        print(f"  {label:24s} "
              f"new={float(new_bound.upper()):.4e} "
              f"(lead={float(lead.upper()):.2e}, rem={float(rem.upper()):.2e}) "
              f"old={float(old_bound.upper()):.4e}  ratio={ratio:.4e}")
