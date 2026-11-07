"""Rigorous closed-form Gaussian tail bounds for chunk-bound integrands.

For our 2D chunk-bound integrand
    f(x,y) = J(x,y) · E_Z(x,y)
where E_Z(x,y) = exp(-α/2·(x-y)² - β/2·(x+y)²) ≤ exp(-c·(x²+y²)) with
c = min(α, β), and J is a polynomial of bounded degree, we need

    tail(L) := ∫∫_{|x|>L OR |y|>L} f(x,y) dx dy

as a rigorous arb upper bound.

By inclusion-exclusion (and dropping the negative correction):
    tail(L) ≤ ∫∫_{|x|>L} f dx dy + ∫∫_{|y|>L} f dx dy
            = 2 · ∫_{|x|>L} ∫_R f dx dy   (when integrand is symmetric in x↔y)

For NON-symmetric integrands we keep both terms.

Building blocks (all closed-form, computed in arb):

    M_full(j; c) := ∫_R y^{2j} exp(-c·y²) dy
                  = (2j-1)!! · sqrt(π/c) / (2c)^j

    M_tail(k; c, L) := ∫_{|x|>L} x^{2k} exp(-c·x²) dx
                     = (1/c^{k+1/2}) · Γ(k+1/2, c·L²)

The upper incomplete gamma Γ(s, x) has a closed form in arb:
    Γ(s, x) = Γ(s) · arb_hypgeom_gamma_upper_regularized(s, x)
    or use arb's gamma_upper directly.

Polynomial decomposition:
For our V26 chunks with h_3 curves, the integrand polynomial factor J is
bounded by a polynomial in (x², y²) of total bidegree ≤ 6. We expand:

    J(x,y) ≤ Σ_{(k, j)} A_{k,j} · x^{2k} · y^{2j}

(with A_{k,j} ≥ 0 by construction of the polynomial bound). Then

    ∫∫ J · E_Z dx dy ≤ ∫∫ J · exp(-c·(x²+y²)) dx dy
                     = Σ_{(k,j)} A_{k,j} · M_full(k; c) · M_full(j; c)   (whole-plane)

    tail(L) ≤ Σ_{(k,j)} A_{k,j} · [M_tail(k; c, L) · M_full(j; c)
                                    + M_full(k; c) · M_tail(j; c, L)]

This file provides M_full, M_tail in arb arithmetic, and a wrapper that
takes a polynomial-coefficient table A_{k,j} and produces tail(L).
"""

from __future__ import annotations

from flint import arb, acb, ctx as flint_ctx


def double_factorial_double(n: int) -> arb:
    """(2n-1)!! = 1·3·5·...·(2n-1) for n ≥ 0.  (2·(-1))!! treated as 1."""
    if n <= 0:
        return arb(1)
    p = arb(1)
    for k in range(1, n + 1):
        p = p * arb(2 * k - 1)
    return p


def M_full(j: int, c: arb) -> arb:
    """∫_R y^{2j} exp(-c·y²) dy = (2j-1)!! · sqrt(π/c) / (2c)^j.

    Returns an arb upper bound (which is exactly the closed form here since
    everything is positive in arb arithmetic).
    """
    if j == 0:
        return (arb.pi() / c).sqrt()
    coef = double_factorial_double(j)
    base = (arb.pi() / c).sqrt()
    twoc_pow = (arb(2) * c) ** j
    return coef * base / twoc_pow


def upper_incomplete_gamma(s: arb, x: arb) -> arb:
    """Upper incomplete gamma Γ(s, x) = ∫_x^∞ t^{s-1} exp(-t) dt.

    Uses python-flint's arb.gamma_upper if available; otherwise the
    relation Γ(s, x) = Γ(s) - γ(s, x) where γ is lower incomplete.
    """
    # arb.gamma_upper returns the upper incomplete gamma function.
    # python-flint wraps acb_hypgeom_gamma_upper which works for arb too via acb.
    z = acb(x)
    s_acb = acb(s)
    # acb gamma_upper signature: (s, z, regularized=0)
    # python-flint: acb.gamma_upper(s) computes Γ(s, z) on self z
    return z.gamma_upper(s_acb).real


def M_tail(k: int, c: arb, L: arb) -> arb:
    """∫_{|x|>L} x^{2k} exp(-c·x²) dx
        = 2 · ∫_L^∞ x^{2k} exp(-c·x²) dx
        = (1/c^{k+1/2}) · Γ(k+1/2, c·L²).

    Symmetric in sign of x, so ∫_{-∞}^{-L} = ∫_L^∞.
    """
    s = arb(k) + arb(1) / arb(2)
    cL2 = c * L * L
    inc = upper_incomplete_gamma(s, cL2)
    return inc / c ** (arb(k) + arb(1) / arb(2))


def compute_tail_bound_polynomial(
    poly_terms: list[tuple[int, int, arb]],
    c: arb,
    L: arb,
) -> arb:
    """Tail bound for ∫∫_{|x|>L OR |y|>L} J(x,y)·exp(-c(x²+y²)) dx dy
    where J(x,y) ≤ Σ A_{k,j} · x^{2k} · y^{2j}.

    Args:
        poly_terms: list of (k, j, A_kj) with A_kj ≥ 0  (all arb-typed).
        c: minimum-eigenvalue Gaussian decay rate.
        L: truncation bound.

    Returns: arb upper bound on the tail.
    """
    tail = arb(0)
    for (k, j, A) in poly_terms:
        Mt_k = M_tail(k, c, L)
        Mf_k = M_full(k, c)
        Mt_j = M_tail(j, c, L)
        Mf_j = M_full(j, c)
        # tail ≤ A · (M_tail(k)·M_full(j) + M_full(k)·M_tail(j))
        # (over-counts when |x|>L AND |y|>L — but that's a positive over-count)
        tail = tail + A * (Mt_k * Mf_j + Mf_k * Mt_j)
    return tail


# ----------------------------------------------------------------------
# Smoke tests
# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200
    print("M_full(0; c=1) = sqrt(π) =", M_full(0, arb(1)).str(15))
    print("M_full(1; c=1) = sqrt(π)/2 =", M_full(1, arb(1)).str(15))
    print("M_full(2; c=1) = 3·sqrt(π)/4 =", M_full(2, arb(1)).str(15))
    print("M_full(3; c=1) = 15·sqrt(π)/8 =", M_full(3, arb(1)).str(15))
    print()
    # M_tail(0; c=1, L=2) = sqrt(π)·erfc(2). erfc(2) ≈ 0.0046777349810473
    L = arb(2)
    print(f"M_tail(0; c=1, L=2) = sqrt(π)·erfc(2) = "
          f"{(arb.pi().sqrt() * arb(2).erfc()).str(15)}")
    print(f"M_tail(0; c=1, L=2) computed       = {M_tail(0, arb(1), L).str(15)}")
    print()

    # Polynomial tail bound smoke test:
    # J(x,y) = 1 + x² + y², c=0.12, L=12
    print("Polynomial tail test: J(x,y) = 1 + x² + y², c=0.12, L=12")
    c = arb("0.12")
    L = arb(12)
    terms = [(0, 0, arb(1)), (1, 0, arb(1)), (0, 1, arb(1))]
    tail = compute_tail_bound_polynomial(terms, c, L)
    print(f"  tail ≤ {tail.str(15)}")
    # Check against full integral
    M00 = M_full(0, c)
    M10 = M_full(1, c)
    M01 = M_full(0, c)
    full = arb(1) * M00 * M00 + arb(1) * M10 * M01 + arb(1) * M00 * M10
    print(f"  full ∫∫ = {full.str(15)}")
    print(f"  tail / full = {(tail / full).str(8)}")
