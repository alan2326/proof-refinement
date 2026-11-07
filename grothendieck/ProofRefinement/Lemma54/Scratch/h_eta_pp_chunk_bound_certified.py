"""Fully certified (closed-form arb) chunk bound on sup_{z∈Z} |H_η''(z)|.

Replaces h_eta_pp_chunk_bound.py's GL with closed-form 1D Gaussian moments.

Math from Price's-theorem 2nd derivative + real-positive majorant:

    |H_η''(z)| ≤ (1/(π·d_Z)) · ∫∫ J(x,y) · E_Z(x,y) · extra(x,y) dx dy

where (per LLM analysis in h_eta_pp_chunk_bound.py docstring):
    J(x,y) = |1 + P'(x)Q'(y)|
    A(x,y) = x² + y² + P²(x) + Q²(y)
    B(x,y) = |xy + P(x)Q(y)|
    extra(x,y) = 2|z|/d_Z + (2|z|·A + 2(1+|z|²)·B) / d_Z²

Certified analytic bounds (AM-GM + V26's Q = -P):
  J ≤ 1 + (P'(x)² + P'(y)²)/2                   (analytic)
  A = x² + y² + P²(x) + P²(y)                   (already analytic)
  B ≤ (x² + y²)/2 + (P²(x) + P²(y))/2           (AM-GM)

So the integrand bound is a polynomial in x², y², (P(x)², P(y)², P'(x)², P'(y)²)
times E_Z(x,y). Each term integrates to a closed-form 1D Gaussian moment via
the marginal-Gaussian identity ∫_R E_Z(x,y) dy = K₁·exp(-σ·x²),
σ = 2αβ/(α+β), K₁ = sqrt(2π/(α+β)).

For V26 with η = 1/100, P(x) = K_P·(4x³ − 3x), K_P = η/(√3·π^{1/4}):
  P²(x)   = K_P²·(16x⁶ − 24x⁴ + 9x²)
  P'²(x)  = K_P²·(144x⁴ − 72x² + 9)

The full polynomial expansion is mechanical. We organize by "monomial in (x², y²)":

  [1] term: extra has 2|z|/d_Z + (1+|z|²)/d_Z² · (x²+y²) + 2|z|/d_Z²·A_poly + ...
            etc. This file does the algebra explicitly.

Strategy: rewrite
    integrand(x,y) ≤ Σ_α C_α · g_α(x) · h_α(y)        (monomial separation)

then ∫∫ g·E_Z·h dx dy = K₁ · ∫_R g(x)·exp(-σ·x²) dx · (...)
After integrating over y first using the marginal Gaussian, only g(x)·exp(-σx²)·K₁
times any y-polynomial moment survives. We compile into

    ∫∫ x^{2k}·y^{2j} · E_Z dxdy = K₁ · M(k;σ) · M(j;σ_y)?

Wait — the marginal trick collapses one variable. Need to be more careful.

Cleaner derivation: in the diagonalising basis u = (x+y)/√2, v = (x−y)/√2,
    E_Z(x,y) = exp(-β u² − α v²)                 (jacobian 1)
    x = (u+v)/√2,  y = (u−v)/√2

So ∫∫ x^{2k}·y^{2j}·E_Z dxdy = ∫∫ ((u+v)/√2)^{2k}·((u−v)/√2)^{2j}·exp(-βu²−αv²) du dv.

Expand binomially and integrate each (u^a · v^b) against exp(-βu²−αv²):
    ∫_R u^a exp(-βu²) du = M_full(a/2; β)   if a even, 0 if a odd
    ∫_R v^b exp(-αv²) dv = M_full(b/2; α)   if b even, 0 if b odd

For our integrands the polynomials in (x², y²) are even in each, but expanding
((u+v)/√2)^{2k} mixes even and odd terms in u, v. Only the even-even terms
survive after integration.

For practicality we use a higher-level helper: gaussian_moment_2d(k_x, k_y; α, β)
that returns ∫∫ x^{2k_x}·y^{2k_y}·E_Z(x,y) dxdy in closed form.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import NamedTuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
from gaussian_tail_bounds import M_full


# ----------------------------------------------------------------------
def _binomial(n: int, k: int) -> arb:
    """Binomial coefficient as arb (exact)."""
    if k < 0 or k > n:
        return arb(0)
    if k == 0 or k == n:
        return arb(1)
    val = arb(1)
    for i in range(k):
        val = val * arb(n - i) / arb(i + 1)
    return val


def gaussian_moment_2d(k_x: int, k_y: int, alpha: arb, beta: arb) -> arb:
    """∫∫_R² x^{2k_x} · y^{2k_y} · exp(-α/2·(x-y)² - β/2·(x+y)²) dx dy.

    Diagonalising u = (x+y)/√2, v = (x-y)/√2:
        x = (u+v)/√2, y = (u-v)/√2
        E_Z = exp(-α v² - β u²)
    Hence integrand = ((u+v)^{2k_x}/(√2)^{2k_x}) · ((u-v)^{2k_y}/(√2)^{2k_y}) · E_Z
                    = (u+v)^{2k_x}·(u-v)^{2k_y} / 2^{k_x+k_y} · E_Z

    Expanding (u+v)^{2k_x} = Σ_p C(2k_x, p) u^p v^{2k_x-p},
              (u-v)^{2k_y} = Σ_q C(2k_y, q) u^q (-v)^{2k_y-q}.
    Only terms with both u-power and v-power EVEN survive.

    Returns arb upper bound (exact closed form here).
    """
    coef = arb(1) / arb(2) ** (k_x + k_y)
    total = arb(0)
    for p in range(0, 2 * k_x + 1):
        a_u = p
        a_v = 2 * k_x - p
        for q in range(0, 2 * k_y + 1):
            b_u = q
            b_v = 2 * k_y - q
            u_pow = a_u + b_u
            v_pow = a_v + b_v
            # We need both u_pow and v_pow even
            if u_pow % 2 != 0 or v_pow % 2 != 0:
                continue
            # Sign from (-v)^{2k_y - q}
            sign = arb(1) if (2 * k_y - q) % 2 == 0 else arb(-1)
            # Coefficient
            term_coef = sign * _binomial(2 * k_x, p) * _binomial(2 * k_y, q)
            mu = M_full(u_pow // 2, beta)
            mv = M_full(v_pow // 2, alpha)
            total = total + term_coef * mu * mv
    return coef * total


# ----------------------------------------------------------------------
class HetaPpChunkResult(NamedTuple):
    bound: arb
    d_Z: arb
    alpha_Z: arb
    beta_Z: arb
    z_abs_ub: arb
    K_P: arb


def _chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    from chunk_constants_safe import safe_chunk_constants
    return safe_chunk_constants(z_ball)


def bound_H_eta_pp_on_chunk_certified(
    z_ball: acb,
    eta_arb: arb,
    prec: int = 200,
) -> HetaPpChunkResult:
    """Closed-form arb upper bound on sup_{z∈Z} |H_η''(z)| for V26 curves."""
    flint_ctx.prec = prec
    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)

    if not (alpha_Z > arb(0) and beta_Z > arb(0)):
        raise ValueError(f"alpha_Z={alpha_Z}, beta_Z={beta_Z} must be positive")

    pi_quarter = arb.pi().sqrt().sqrt()
    K_P = eta_arb / (arb(3).sqrt() * pi_quarter)
    K_P2 = K_P * K_P

    # Polynomial coefficients (functions of x or y separately)
    # P²(x) coefficients: P²(x) = K_P²·(9x² − 24x⁴ + 16x⁶)
    P2_coefs = {1: K_P2 * arb(9), 2: -K_P2 * arb(24), 3: K_P2 * arb(16)}
    # P'²(x) coefficients: P'²(x) = K_P²·(9 − 72x² + 144x⁴)
    Pp2_coefs = {0: K_P2 * arb(9), 1: -K_P2 * arb(72), 2: K_P2 * arb(144)}

    # Helper: coefficient table for f(x) ≤ Σ a_k · x^{2k}  (actually just =, via signed coeffs).
    #   We compute ∫∫ f(x,y)·E_Z(x,y) dxdy assuming f(x,y) = sep_x(x) + sep_y(y) etc.
    # The integrand of H_η'' is more involved; expand as documented.

    # Bounded integrand:
    #   J(x,y)  ≤ 1 + (P'²(x) + P'²(y))/2
    #   A(x,y)  = x² + y² + P²(x) + P²(y)
    #   B(x,y)  ≤ (x² + y²)/2 + (P²(x) + P²(y))/2
    #   extra ≤ 2|z|/d_Z + (2|z|·A + 2·(1+|z|²)·B) / d_Z²
    #         = 2|z|/d_Z + (2|z|·(x²+y²+P²(x)+P²(y))
    #                       + (1+|z|²)·((x²+y²)+(P²(x)+P²(y))))/d_Z²
    #         = 2|z|/d_Z + (2|z| + 1 + |z|²)·(x²+y²+P²(x)+P²(y))/d_Z²
    #         = 2|z|/d_Z + (1+|z|)²·(x²+y²+P²(x)+P²(y))/d_Z²
    #
    # Integrand ≤ J · extra.  Expand:
    #   J · extra ≤ extra + (P'²(x)+P'²(y))/2 · extra
    #
    # The first piece (no J factor): "extra" itself
    #   = c0 + c1·(x² + y² + P²(x) + P²(y))     where c0 = 2|z|/d_Z, c1 = (1+|z|)²/d_Z²
    # The second piece (J's η²-correction):
    #   (P'²(x)+P'²(y))/2 · (c0 + c1·(x²+y²+P²(x)+P²(y)))
    # Each of these is a sum of separable monomials in (x², y²).

    c0 = arb(2) * z_abs_ub / d_Z
    c1 = (arb(1) + z_abs_ub) ** 2 / (d_Z * d_Z)

    # Helper: ∫∫ x^{2k_x} · y^{2k_y} · E_Z dxdy via gaussian_moment_2d
    def G(k_x: int, k_y: int) -> arb:
        return gaussian_moment_2d(k_x, k_y, alpha_Z, beta_Z)

    # ----- Piece 1: "extra" alone -----
    # = c0 + c1·(x²+y²+P²(x)+P²(y))
    piece1 = arb(0)
    piece1 = piece1 + c0 * G(0, 0)                          # c0 · 1
    piece1 = piece1 + c1 * G(1, 0)                          # c1 · x²
    piece1 = piece1 + c1 * G(0, 1)                          # c1 · y²
    for k_p2, coef in P2_coefs.items():                     # c1 · P²(x)
        piece1 = piece1 + c1 * coef * G(k_p2, 0)
    for k_p2, coef in P2_coefs.items():                     # c1 · P²(y)
        piece1 = piece1 + c1 * coef * G(0, k_p2)

    # ----- Piece 2: (P'²(x)+P'²(y))/2 · "extra" -----
    # = (1/2) · Σ_{k_pp ∈ {0,1,2}} Pp2_coefs[k_pp] · x^{2k_pp} · extra
    #   + same for y^{2k_pp}
    # We expand extra and combine.
    half = arb(1) / arb(2)
    piece2 = arb(0)
    for k_pp, c_pp in Pp2_coefs.items():
        # x^{2k_pp} · c0
        piece2 = piece2 + half * c_pp * c0 * G(k_pp, 0)
        # x^{2k_pp} · c1·x²
        piece2 = piece2 + half * c_pp * c1 * G(k_pp + 1, 0)
        # x^{2k_pp} · c1·y²
        piece2 = piece2 + half * c_pp * c1 * G(k_pp, 1)
        # x^{2k_pp} · c1·P²(x)
        for k_p2, coef in P2_coefs.items():
            piece2 = piece2 + half * c_pp * c1 * coef * G(k_pp + k_p2, 0)
        # x^{2k_pp} · c1·P²(y)
        for k_p2, coef in P2_coefs.items():
            piece2 = piece2 + half * c_pp * c1 * coef * G(k_pp, k_p2)
        # symmetric: y^{2k_pp} terms
        piece2 = piece2 + half * c_pp * c0 * G(0, k_pp)
        piece2 = piece2 + half * c_pp * c1 * G(1, k_pp)
        piece2 = piece2 + half * c_pp * c1 * G(0, k_pp + 1)
        for k_p2, coef in P2_coefs.items():
            piece2 = piece2 + half * c_pp * c1 * coef * G(k_p2, k_pp)
        for k_p2, coef in P2_coefs.items():
            piece2 = piece2 + half * c_pp * c1 * coef * G(0, k_pp + k_p2)

    integral = piece1 + piece2

    bound = integral / (arb.pi() * d_Z)

    return HetaPpChunkResult(
        bound=bound, d_Z=d_Z, alpha_Z=alpha_Z, beta_Z=beta_Z,
        z_abs_ub=z_abs_ub, K_P=K_P,
    )


# ----------------------------------------------------------------------
# Smoke tests
# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200
    eta_arb = arb("0.01")

    print("=" * 72)
    print("H_η'' chunk bound: closed-form certified vs prior GL-based")
    print("=" * 72)

    test_chunks = [
        ("real, half=0.05",  acb(arb("0.5"),  arb.union(arb("-0.05"), arb("0.05")))),
        ("interior cplx",    acb(arb.union(arb("0.35"), arb("0.45")),
                                  arb.union(arb("0.45"), arb("0.55")))),
        ("V26 corner-ish",   acb(arb("0.84"), arb.union(arb("0.97"), arb("1.115")))),
        ("V26 spike",        acb(arb("0.84"), arb.union(arb("0.14"), arb("0.28")))),
    ]

    sys.path.insert(0, str(_HERE))
    from h_eta_pp_chunk_bound import bound_H_eta_pp_on_chunk
    from h_eta_prime_integral import make_v26_P, make_v26_Pprime
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    for label, z_ball in test_chunks:
        print(f"\n>> {label}")
        r = bound_H_eta_pp_on_chunk_certified(z_ball, eta_arb, prec=200)
        print(f"   d_Z={float(r.d_Z):.4e}, α_Z={float(r.alpha_Z):.4e}, "
              f"β_Z={float(r.beta_Z):.4e}")
        print(f"   certified bound = {r.bound.str(8)}")
        gl_bound = bound_H_eta_pp_on_chunk(
            z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=200,
        )
        print(f"   GL-based       = {gl_bound.str(8)}")
        ratio = r.bound / gl_bound
        print(f"   certified/GL   = {ratio.str(8)}× (looseness vs GL)")

    print("\n" + "=" * 72)
