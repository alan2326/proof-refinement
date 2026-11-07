"""
Steps 5-6: Choose ρ = α · γ₀ and compute M_ρ = max_{|z|=ρ} |φ(z)|.

ρ > γ makes (γ/ρ)^{2n+3} small in the tail bound.
The proof uses γ ≤ γ₀ (assumed for contradiction), so ρ = α · γ₀
with α > 1 and sin(ρD) ⊂ S (analyticity of φ).

S = {w ∈ ℂ : |Re(w)| < 1} is the analyticity domain of H_eta
[BMMN11, Lemma 4.2].  The condition sin(ρD) ⊂ S ensures
H_eta(sin z) is analytic on |z| ≤ ρ.

Approach: evaluate φ's OWN Taylor polynomial on |z|=ρ, plus a
rigorous Cauchy tail bound using Lemma 4.2 (formula 43) at a
larger radius R > ρ.  Exploits odd-only coefficients of φ.

Rigor notes:
  - All certification uses certified_lt/certified_positive on arb, never float
  - Max tracking uses arb.max (upper-endpoint accumulation), not interval >
  - Arc parameterization uses exp(iθ) for better correlation
  - Lemma 4.2 hypothesis (1 - a² > 0) checked per arc enclosure
"""

from __future__ import annotations

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    abs_ub, certified_lt, certified_positive,
)
from grothendieck.proof.certified.h_eta_evaluator import (
    gamma_0_arb,
)


# ────────────────────────────────────────────────────────
# Analyticity certification: sin(ρD) ⊂ S
# ────────────────────────────────────────────────────────

def certify_sin_disk_in_strip(
    rho: arb,
    n_arcs: int = 512,
    prec: int = 128,
) -> bool:
    """Certify that sin(ρD) ⊂ S = {w ∈ ℂ : |Re(w)| < 1}.

    Per-arc check: for each arc on |z| = ρ, certify
      -1 < Re(sin z) < 1
    using certified_lt (arb comparisons, no float conversions).
    Uses exp(iθ) parameterization for tight enclosures.

    Raises ValueError if any arc fails certification.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    one = arb(1)
    two_pi = arb(2) * arb.pi()

    for k in range(n_arcs):
        theta_lo = two_pi * arb(k) / arb(n_arcs)
        theta_hi = two_pi * arb(k + 1) / arb(n_arcs)
        theta = arb.union(theta_lo, theta_hi)

        # exp(iθ) preserves correlation better than (cos θ, sin θ) box
        z = acb(0, theta).exp() * rho

        re = z.sin().real

        if not certified_lt(re, one):
            flint_ctx.prec = old_prec
            raise ValueError(
                f"Cannot certify Re(sin z) < 1 on arc {k}/{n_arcs}"
            )
        if not certified_lt(-one, re):
            flint_ctx.prec = old_prec
            raise ValueError(
                f"Cannot certify Re(sin z) > -1 on arc {k}/{n_arcs}"
            )

    flint_ctx.prec = old_prec
    return True


def _try_certify(R_float: float, n_arcs: int, prec: int) -> bool:
    """Non-raising wrapper for certify_sin_disk_in_strip."""
    try:
        old_prec = flint_ctx.prec
        flint_ctx.prec = prec
        certify_sin_disk_in_strip(arb(str(R_float)), n_arcs, prec)
        flint_ctx.prec = old_prec
        return True
    except ValueError:
        flint_ctx.prec = old_prec
        return False


def find_certified_R(
    rho: arb,
    n_arcs: int = 2048,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Find a certified R > ρ with sin(RD) ⊂ S for the Cauchy tail.

    Float arithmetic is used only for the search; every candidate
    is re-certified via arb before returning.
    """
    rho_float = float(rho.mid())

    # Ascending gap search: find largest certifiable R and first failure
    R_lo = rho_float
    R_hi = None

    for gap in [0.002, 0.005, 0.01, 0.02, 0.05, 0.10, 0.15, 0.20, 0.25]:
        R_cand = rho_float + gap
        if _try_certify(R_cand, n_arcs, prec):
            R_lo = R_cand
        else:
            R_hi = R_cand
            break

    if R_lo <= rho_float:
        raise ValueError(
            f"Cannot find R > ρ = {rho_float:.6f} with sin(RD) ⊂ S. "
            f"ρ may be too close to the analyticity boundary (~1.157)."
        )

    # Bisect between R_lo (success) and R_hi (failure) to refine R_max
    if R_hi is not None:
        for _ in range(20):
            R_mid = (R_lo + R_hi) / 2
            if _try_certify(R_mid, n_arcs, prec):
                R_lo = R_mid
            else:
                R_hi = R_mid

    R_max = R_lo
    R_use = rho_float + 0.85 * (R_max - rho_float)
    if R_use <= rho_float:
        R_use = R_max

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    R_arb = arb(str(R_use))
    certify_sin_disk_in_strip(R_arb, n_arcs, prec)

    # Certify R > ρ rigorously
    if not certified_positive(R_arb - rho):
        flint_ctx.prec = old_prec
        raise ValueError("Cannot certify R > ρ for Cauchy tail")

    flint_ctx.prec = old_prec

    if verbose:
        print(f"    R_max ≈ {R_max:.6f}, R_use = {R_use:.6f} "
              f"(gap: {R_use - rho_float:.6f})")

    return R_arb


# ────────────────────────────────────────────────────────
# Lemma 4.2 bound (formula 43)
# ────────────────────────────────────────────────────────

def _H_eta_bound_lemma42(a: arb, b: arb, prec: int = 128) -> arb:
    """Upper bound on |H_eta(a+bi)| via Lemma 4.2, formula (43).

    |H_eta(w)| ≤ π((1+a)²+b²)((1-a)²+b²) / (2(1-a²)√((1-a²)²+b⁴+2(1+a²)b²))

    Caller must ensure 1 - a² > 0 (i.e. |Re(w)| < 1) for this arc.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    one = arb(1)
    pi_val = arb.pi()

    a2 = a ** 2
    b2 = b ** 2

    num = pi_val * ((one + a) ** 2 + b2) * ((one - a) ** 2 + b2)
    one_minus_a2 = one - a2
    denom1 = arb(2) * one_minus_a2
    radicand = one_minus_a2 ** 2 + b2 ** 2 + arb(2) * (one + a2) * b2
    denom2 = radicand.sqrt()

    val = num / (denom1 * denom2)

    flint_ctx.prec = old_prec
    return val


def _bound_phi_on_circle_lemma42(
    R: arb,
    n_arcs: int = 512,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Upper bound on max|φ(z)| on |z|=R using Lemma 4.2.

    Per-arc: |φ(z)| ≤ (|z| + |H_eta(sin z)|)·|cos z|

    Uses exp(iθ) parameterization and arb.max for upper-endpoint
    tracking.  Checks Lemma 4.2 hypothesis (1 - a² > 0) per arc.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    one = arb(1)
    two_pi = arb(2) * arb.pi()
    max_bound = arb(0)

    for k in range(n_arcs):
        theta_lo = two_pi * arb(k) / arb(n_arcs)
        theta_hi = two_pi * arb(k + 1) / arb(n_arcs)
        theta = arb.union(theta_lo, theta_hi)

        z = acb(0, theta).exp() * R

        sin_z = z.sin()
        cos_z = z.cos()

        a = sin_z.real
        b = sin_z.imag

        # Ensure Lemma 4.2 hypothesis for this arc's enclosure
        if not certified_positive(one - a * a):
            flint_ctx.prec = old_prec
            raise ValueError(
                f"Cannot certify 1 - (Re(sin z))² > 0 on arc {k}/{n_arcs}; "
                f"refine n_arcs or increase prec"
            )

        H_bound = _H_eta_bound_lemma42(a, b, prec)
        cos_bound = abs_ub(cos_z)
        
        phi_bound = (R + H_bound) * cos_bound

        # Track max via arb.max (accumulates upper endpoints correctly)
        max_bound = arb.max(max_bound, phi_bound)

    if verbose:
        print(f"    M_R (Lemma 4.2, R={float(R.mid()):.6f}, {n_arcs} arcs) "
              f"= {max_bound}")

    flint_ctx.prec = old_prec
    return max_bound


def _max_modulus_on_circle(
    f,
    radius: arb,
    n_arcs: int = 512,
    prec: int = 128,
) -> arb:
    """Rigorous upper bound on max|f(z)| for |z|=radius.

    Uses exp(iθ) parameterization and arb.max for tracking.
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    if not isinstance(radius, arb):
        radius = arb(str(radius))

    two_pi = arb(2) * arb.pi()
    max_val = arb(0)

    for k in range(n_arcs):
        theta_lo = two_pi * arb(k) / arb(n_arcs)
        theta_hi = two_pi * arb(k + 1) / arb(n_arcs)
        theta = arb.union(theta_lo, theta_hi)

        z = acb(0, theta).exp() * radius

        val = abs_ub(f(z))
        max_val = arb.max(max_val, val)

    flint_ctx.prec = old_prec
    return max_val


# ────────────────────────────────────────────────────────
# Main API
# ────────────────────────────────────────────────────────

def choose_rho(
    alpha: float = 1.02,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Set ρ = α · γ₀ and certify sin(ρD) ⊂ S.

    γ₀ = atanh(1/√2) ≈ 0.8814
    α > 1 (e.g., 1.02 → ρ ≈ 0.899, 1.305 → ρ ≈ 1.15)
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    g0 = gamma_0_arb(prec)
    alpha_arb = arb(str(alpha))
    rho = alpha_arb * g0

    # Certify sin(ρD) ⊂ S with adaptive arc refinement
    n_arcs = 512
    certified = False

    while n_arcs <= 16384:
        try:
            certify_sin_disk_in_strip(rho, n_arcs, prec)
            certified = True
            break
        except ValueError:
            n_arcs *= 2

    if not certified:
        flint_ctx.prec = old_prec
        raise ValueError(
            f"Cannot certify sin(ρD) ⊂ S for ρ = {rho} (α = {alpha}). "
            f"ρ may be too close to the analyticity boundary (~1.157). "
            f"Try smaller α."
        )

    if verbose:
        print(f"Steps 5-6: Choosing ρ")
        print(f"  γ₀ = {g0}")
        print(f"  α = {alpha}")
        print(f"  ρ = α·γ₀ = {rho}")
        print(f"  sin(ρD) ⊂ S certified ({n_arcs} arcs)")

    flint_ctx.prec = old_prec
    return rho


def compute_M_rho_via_phi_taylor(
    phi_series: arb_series,
    rho: arb,
    R: arb,
    n_arcs: int = 512,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute M_ρ via φ's Taylor polynomial + odd-only Cauchy tail.

    M_ρ ≤ max_{|z|=ρ} |P_K(z)| + M_R · (ρ/R)^{K_odd+2} / (1-(ρ/R)²)
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    coeffs = phi_series.coeffs()
    K = len(coeffs)

    # Scan downward for highest odd index with nontrivial coefficient
    K_odd_max = None
    for j in range(K - 1, -1, -1):
        if j % 2 == 1 and not coeffs[j].contains(arb(0)):
            K_odd_max = j
            break

    if K_odd_max is None:
        if verbose:
            print("  φ Taylor polynomial numerically zero; crude bound only")
        flint_ctx.prec = old_prec
        return _bound_phi_on_circle_lemma42(rho, n_arcs, prec, verbose)

    # Certify R > ρ
    if not certified_positive(R - rho):
        flint_ctx.prec = old_prec
        raise ValueError(f"Need certified R > ρ: R={R}, ρ={rho}")

    # 1. Polynomial part: max|P_K(z)| on |z| = ρ
    def eval_phi_poly(z: acb) -> acb:
        result = acb(coeffs[K - 1])
        for j in range(K - 2, -1, -1):
            result = result * z + acb(coeffs[j])
        return result

    M_poly = _max_modulus_on_circle(eval_phi_poly, rho, n_arcs, prec)

    # 2. Cauchy tail (odd-only): M_R · (ρ/R)^{K_odd+2} / (1-(ρ/R)²)
    M_R = _bound_phi_on_circle_lemma42(R, n_arcs, prec, verbose)

    ratio = rho / R
    ratio_sq = ratio ** 2
    one_minus_ratio_sq = arb(1) - ratio_sq

    if not certified_positive(one_minus_ratio_sq):
        flint_ctx.prec = old_prec
        raise ValueError(f"Cannot certify (ρ/R)² < 1: ρ={rho}, R={R}.")

    tail_exp = K_odd_max + 2  # exponent of first missing odd term
    tail = M_R * ratio ** tail_exp / one_minus_ratio_sq

    result = M_poly + tail

    if verbose:
        print(f"  M_ρ (φ-Taylor + Lemma 4.2, K={K})")
        print(f"    K_odd_max = {K_odd_max}")
        print(f"    max|P_K(z)| on |z|=ρ = {M_poly}")
        print(f"    ρ/R = {ratio}")
        print(f"    tail exponent = {tail_exp}")
        print(f"    tail bound = {tail}")
        print(f"    M_ρ = {result}")

    flint_ctx.prec = old_prec
    return result


def compute_M_rho(
    rho: arb,
    phi_series: arb_series = None,
    R_cauchy: arb = None,
    n_arcs: int = 512,
    prec: int = 128,
    verbose: bool = False,
) -> arb:
    """Compute M_ρ = max_{|z|=ρ} |φ(z)|.

    Two methods:
      1. Crude: Lemma 4.2 arc-by-arc bound at radius ρ directly.
      2. Refined: φ's Taylor polynomial + odd-only Cauchy tail
         with M_R from Lemma 4.2 at a larger radius R.

    Returns the tighter (smaller upper endpoint) of the two bounds.
    Both are valid upper bounds; we pick by comparing upper endpoints
    (not certified_lt, which would miss overlapping intervals).
    """
    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    # Crude bound at ρ via Lemma 4.2
    M_crude = _bound_phi_on_circle_lemma42(rho, n_arcs, prec, verbose)
    if verbose:
        print(f"  M_ρ (crude/Lemma 4.2) = {M_crude}")

    if phi_series is not None:
        # Find R for Cauchy tail (auto-search if not given)
        if R_cauchy is None:
            try:
                R_cauchy = find_certified_R(
                    rho, n_arcs=max(n_arcs, 2048), prec=prec,
                    verbose=verbose,
                )
            except ValueError as e:
                if verbose:
                    print(f"    (no R found for Cauchy tail: {e})")
                    print(f"    Falling back to crude bound only.")
                flint_ctx.prec = old_prec
                return M_crude

        M_refined = compute_M_rho_via_phi_taylor(
            phi_series, rho, R_cauchy, n_arcs, prec, verbose,
        )

        # Pick tighter bound by comparing upper endpoints.
        # Both are valid upper bounds; float conversion here is safe
        # (at worst picks the marginally less tight one).
        crude_ub = float(M_crude.upper())
        refined_ub = float(M_refined.upper())

        if refined_ub <= crude_ub:
            flint_ctx.prec = old_prec
            return M_refined

    flint_ctx.prec = old_prec
    return M_crude
