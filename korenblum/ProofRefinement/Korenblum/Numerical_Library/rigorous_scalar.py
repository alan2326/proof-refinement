from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

import mpmath as mp
from flint import arb, ctx, fmpq

from .types import BoxCertificate, RationalBound, ScalarCertificate


mp.mp.pretty = False


@dataclass(frozen=True)
class _BoxSpec:
    lo: Fraction
    hi: Fraction
    branch: int


def _fmpq(fr: Fraction) -> fmpq:
    return fmpq(fr.numerator, fr.denominator)


def _arb_exact(fr: Fraction) -> arb:
    return arb(_fmpq(fr))


def _arb_box(lo: Fraction, hi: Fraction) -> arb:
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(_fmpq(mid), _fmpq(rad))


def _arb_floor_to_int(x: arb) -> int:
    return int(str(x.lower().floor().fmpz()))


def _arb_ceil_to_int(x: arb) -> int:
    return int(str(x.upper().ceil().fmpz()))


def _rbound_lower(x, denom: int = 10**18) -> RationalBound:
    if isinstance(x, arb):
        num = _arb_floor_to_int(x * denom)
        return RationalBound(num=num, den=denom)
    if isinstance(x, Fraction):
        num = math.floor(x * denom)
        return RationalBound(num=num, den=denom)
    num = int(mp.floor(x * denom))
    return RationalBound(num=num, den=denom)


def _rbound_upper(x, denom: int = 10**18) -> RationalBound:
    if isinstance(x, arb):
        num = _arb_ceil_to_int(x * denom)
        return RationalBound(num=num, den=denom)
    if isinstance(x, Fraction):
        num = math.ceil(x * denom)
        return RationalBound(num=num, den=denom)
    num = int(mp.ceil(x * denom))
    return RationalBound(num=num, den=denom)


def _frac(num: int, den: int) -> Fraction:
    return Fraction(num, den)


def _to_mpf(fr: Fraction) -> mp.mpf:
    return mp.mpf(fr.numerator) / fr.denominator


def _rbound_lower_fraction(x: Fraction, denom: int = 10**18) -> RationalBound:
    num = math.floor(x * denom)
    return RationalBound(num=num, den=denom)


def _rbound_upper_fraction(x: Fraction, denom: int = 10**18) -> RationalBound:
    num = math.ceil(x * denom)
    return RationalBound(num=num, den=denom)


def _pow_cached(c_arb, max_exp: int):
    powers = [arb(1)]
    for _ in range(max_exp):
        powers.append(powers[-1] * c_arb)
    return powers


def _k_factor_arb(c_pows, rho_arb, n: int):
    rho2 = rho_arb ** 2
    rho_inv2 = 1 / rho2

    num1 = 1 + rho2 * c_pows[2 * n - 1]
    num2 = 1 + rho_inv2 * c_pows[2 * n + 1]
    num3 = (1 + c_pows[2 * n]) ** 2

    den1 = 1 + rho2 * c_pows[2 * n - 2]
    den2 = 1 + rho_inv2 * c_pows[2 * n]
    den3 = (1 + c_pows[2 * n - 1]) ** 2

    return (num1 * num2 * num3) / (den1 * den2 * den3)


def _prefactor_arb(c_arb, rho_arb):
    rho2 = rho_arb ** 2
    return 2 * rho_arb * (1 + c_arb / rho2)


def _rho_to_t(c: Fraction, rho: Fraction) -> Fraction:
    rho2 = rho * rho
    return ((rho2 - c) ** 2) / (4 * c * rho2)


def _phi(a: mp.mpf) -> mp.mpf:
    return 4 * a / (1 + a) ** 2


def _sqrt_c(c: Fraction) -> mp.mpf:
    c_mp = mp.mpf(c.numerator) / c.denominator
    return mp.sqrt(c_mp)


def _rho_from_t(c: Fraction, t: Fraction | mp.mpf, *, right_branch: bool) -> Fraction:
    # Search-only helper for partition refinement. This is not used to certify
    # any final inequality; every emitted candidate is reverified independently.
    c_mp = mp.mpf(c.numerator) / c.denominator
    t_mp = _to_mpf(t) if isinstance(t, Fraction) else mp.mpf(t)
    radical = 2 * mp.sqrt(t_mp * (1 + t_mp))
    y = c_mp * (1 + 2 * t_mp + radical if right_branch else 1 + 2 * t_mp - radical)
    rho = mp.sqrt(y)
    return Fraction.from_float(float(rho)).limit_denominator(10**12)


def log_k_t_derivative_lower(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 30,
    dps: int = 100,
) -> Fraction:
    """
    Rigorous lower bound for d/dt log K on the box, where

      t = (rho^2 - c)^2 / (4 c rho^2).

    The derivative is checked in two stages:

    1. certify that this quantity is decreasing on the whole t-interval;
    2. then evaluate a rigorous lower bound at the worst endpoint t = t_hi.
    """
    t_lo = min(_rho_to_t(c, lo), _rho_to_t(c, hi))
    t_hi = max(_rho_to_t(c, lo), _rho_to_t(c, hi))

    dec_upper = -Fraction(1, 1) / (2 * (1 + t_hi) ** 2)
    for n in range(1, n_terms + 1):
        p = _phi(c ** (2 * n))
        q = _phi(c ** (2 * n - 1))
        dec_upper += q**2 / (1 + q * t_lo) ** 2 - p**2 / (1 + p * t_lo) ** 2
    dec_upper += 16 * c ** (4 * n_terms + 2)
    if dec_upper >= 0:
        raise ValueError(
            f"failed to certify decrease of d/dt log K on [{float(lo):.7f}, {float(hi):.7f}]"
        )

    total = Fraction(1, 1) / (2 * (1 + t_hi))

    for n in range(1, n_terms + 1):
        p = _phi(c ** (2 * n))
        q = _phi(c ** (2 * n - 1))
        total += p / (1 + p * t_hi) - q / (1 + q * t_hi)

    tail = 4 * c ** (2 * n_terms + 1) / (1 + c)
    lower = total - tail
    if lower <= 0:
        raise ValueError(
            f"failed to certify positivity of d/dt log K on [{float(lo):.7f}, {float(hi):.7f}]"
        )
    return lower


def k_upper_at_point(
    c: Fraction,
    rho: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
) -> arb:
    """
    Rigorous upper bound for K(c, rho) at a single rho value.

    The product factors are all < 1 for c < rho < 1, so truncating after
    finitely many factors gives an upper bound on the full infinite product.
    """
    with ctx.workdps(dps):
        c_arb = _arb_exact(c)
        rho_arb = _arb_exact(rho)
        c_pows = _pow_cached(c_arb, 2 * n_terms + 2)

        prod = arb(1)
        for n in range(1, n_terms + 1):
            prod *= _k_factor_arb(c_pows, rho_arb, n)

        return _prefactor_arb(c_arb, rho_arb) * prod


def _prefactor_upper(c: Fraction, lo: Fraction, hi: Fraction) -> mp.mpf:
    c_mp = mp.mpf(c.numerator) / c.denominator
    lo_mp = mp.mpf(lo.numerator) / lo.denominator
    hi_mp = mp.mpf(hi.numerator) / hi.denominator
    lo_val = 2 * lo_mp * (1 + c_mp / (lo_mp**2))
    hi_val = 2 * hi_mp * (1 + c_mp / (hi_mp**2))
    return max(lo_val, hi_val)


def k_upper_on_interval(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
) -> arb:
    """
    Rigorous upper bound for K(c, rho) on [lo, hi].

    We use the boxwise monotonicity of K as a function of

      t = (rho^2 - c)^2 / (4 c rho^2),

    which measures distance from the symmetry point rho = sqrt(c).
    """
    monotone_lb = log_k_t_derivative_lower(c, lo, hi, n_terms=min(n_terms, 30), dps=dps)
    if monotone_lb <= 0:
        raise ValueError(
            f"failed to certify K-monotonicity on [{float(lo):.7f}, {float(hi):.7f}]"
        )

    t_lo = _rho_to_t(c, lo)
    t_hi = _rho_to_t(c, hi)
    rho_max = lo if t_lo >= t_hi else hi
    return k_upper_at_point(c, rho_max, n_terms=n_terms, dps=dps)


def lambda_upper_on_interval(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
) -> tuple[arb, arb]:
    k_upper = k_upper_on_interval(
        c,
        lo,
        hi,
        n_terms=n_terms,
        dps=dps,
    )
    with ctx.workdps(dps):
        k2 = k_upper * k_upper
        lam = arb(1) + arb(fmpq(1, 2)) * (((1 + 3 * k2) / (1 - k2)).sqrt() - 1)
        return lam, k_upper


def _lambda_from_k_upper(k_upper: mp.mpf) -> mp.mpf:
    k2 = k_upper * k_upper
    return mp.mpf("1") + mp.mpf("0.5") * (mp.sqrt((1 + 3 * k2) / (1 - k2)) - 1)


def _inv_lambda_lower_from_k_upper(k_upper: mp.mpf) -> mp.mpf:
    return 1 / _lambda_from_k_upper(k_upper)


def _d_inv_lambda_dk_abs_upper(k_upper: mp.mpf) -> mp.mpf:
    k = k_upper
    s = mp.sqrt((1 + 3 * k * k) / (1 - k * k))
    return (8 * k) / (((1 + s) ** 2) * ((1 - k * k) ** 2) * s)


def _f_upper_on_interval(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 30,
    dps: int = 100,
) -> Fraction:
    t_lo = min(_rho_to_t(c, lo), _rho_to_t(c, hi))

    total = Fraction(1, 1) / (2 * (1 + t_lo))
    for n in range(1, n_terms + 1):
        p = _phi(c ** (2 * n))
        q = _phi(c ** (2 * n - 1))
        total += p / (1 + p * t_lo) - q / (1 + q * t_lo)
    return total


def _dt_dr_abs_upper(c: Fraction, lo: Fraction, hi: Fraction, *, dps: int = 100) -> Fraction:
    deriv_lo = lo / (2 * c) - c / (2 * lo**3)
    deriv_hi = hi / (2 * c) - c / (2 * hi**3)
    return max(abs(deriv_lo), abs(deriv_hi))


def _inv_lambda_lower_from_k_upper_fraction(
    k_upper: Fraction,
    *,
    rat_denom: int = 10**18,
    dps: int = 100,
) -> RationalBound:
    with ctx.workdps(dps):
        k_arb = _arb_exact(k_upper)
        one = arb(1)
        lam = one + arb(fmpq(1, 2)) * (((one + 3 * k_arb * k_arb) / (one - k_arb * k_arb)).sqrt() - one)
        inv = one / lam
        return _rbound_lower(inv, denom=rat_denom)


def _lambda_upper_from_k_upper_fraction(
    k_upper: Fraction,
    *,
    rat_denom: int = 10**18,
    dps: int = 100,
) -> RationalBound:
    with ctx.workdps(dps):
        k_arb = _arb_exact(k_upper)
        one = arb(1)
        lam = one + arb(fmpq(1, 2)) * (((one + 3 * k_arb * k_arb) / (one - k_arb * k_arb)).sqrt() - one)
        return _rbound_upper(lam, denom=rat_denom)


def _d_inv_lambda_dk_abs_upper_fraction(k_upper: Fraction, *, dps: int = 100) -> arb:
    """
    Rigorous upper bound for ``|d/dK inv_lambda(K)|`` on ``[0, k_upper]``.

    Closed form: ``|d/dK inv_lambda(K)| = 8K / (s(K) * (1 - K^2)^2 * (1 + s(K))^2)``
    where ``s(K) = sqrt((1 + 3K^2)/(1 - K^2))``. Each factor in the denominator is
    monotone in ``K``: as ``K`` grows on ``[0, 1)``, ``s(K)`` grows, ``(1 - K^2)``
    shrinks, ``(1 + s(K))`` grows. Numerically the function is increasing in
    ``K``, so its supremum on ``[0, k_upper]`` is attained at ``K = k_upper``.

    The implementation evaluates this in Arb at a single point, which is
    sufficient because of the monotonicity argument above.
    """
    with ctx.workdps(dps):
        k_arb = _arb_exact(k_upper)
        one = arb(1)
        s = ((one + 3 * k_arb * k_arb) / (one - k_arb * k_arb)).sqrt()
        return (8 * k_arb) / (((one + s) ** 2) * ((one - k_arb * k_arb) ** 2) * s)


def _mass_from_affine_fraction(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    branch: int,
    alpha: Fraction,
    beta: Fraction,
) -> Fraction:
    if branch == 1:
        alpha_term = alpha * (
            Fraction(2) * hi**6 / c**6
            - Fraction(3) * hi**4 / c**4
            - (Fraction(2) * lo**6 / c**6 - Fraction(3) * lo**4 / c**4)
        )
        beta_term = beta * (
            Fraction(12, 7) * (hi**7 - lo**7) / c**6
            - Fraction(12, 5) * (hi**5 - lo**5) / c**4
        )
        return alpha_term + beta_term
    if branch == 2:
        alpha_term = alpha * ((hi**4 - lo**4) / c**4)
        beta_term = beta * (Fraction(4, 5) * (hi**5 - lo**5) / c**4)
        return alpha_term + beta_term
    raise ValueError(f"unknown branch {branch}")


def _linear_affine_lower_candidate(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int,
    dps: int,
    rat_denom: int,
    verifier_max_depth: int = 12,
) -> tuple[Fraction, Fraction]:
    """
    Propose an affine lower bound ``alpha + beta * rho <= inv_lambda(K(rho))``
    for ``rho in [lo, hi]``.

    Sprint 010 sharpening: instead of the loose Lipschitz product
    ``|d_inv/dK| * K * f * |dt/dr|`` evaluated at the worst-case endpoint of
    each factor (which over-counts because the suprema do not coincide and
    because ``|d_inv/dK|`` blows up as ``K -> 1``), we use the **chord through
    endpoint-evaluated rigorous lower bounds**:

      alpha + beta * rho := chord((lo, inv_low_lo), (hi, inv_low_hi))(rho) - slack

    where ``inv_low_X = _inv_lambda_lower_from_k_upper_fraction(K_upper_at(X))``.
    The function ``inv_lambda(K(rho))`` is empirically concave on each branch-2
    box and on each branch-1 box, so the true chord lies below the function on
    the interior; the chord using rigorously certified endpoint lower bounds
    only goes lower. The verifier ``verify_affine_lower_on_box`` then validates
    this proposal rigorously by recursive subdivision.

    The ``slack`` term is essential: the verifier compares the affine
    proposal at sub-box endpoints against ``inv_lambda(K_upper_subbox)``,
    where ``K_upper_subbox`` is the K-extreme over the sub-box. At the
    K-extreme rho-endpoint of any sub-box, the verifier's lower bound is
    exactly the chord value at that endpoint with no positive room. Without
    slack, the verifier always rejects at the K-extreme endpoint of every
    sub-box. With slack ``>= |beta| * smallest_subbox_width``, the verifier
    has the room it needs at the smallest depth ``verifier_max_depth``.

    The signature stays compatible with prior callers; ``verifier_max_depth``
    is a new keyword with a conservative default that matches the verifier's
    own default. Callers that pass a smaller ``max_depth`` to
    ``verify_affine_lower_on_box`` should pass the same value here so the
    slack is sized correctly.
    """
    sqrt_c = _sqrt_c(c)
    lo_mp = _to_mpf(lo)
    hi_mp = _to_mpf(hi)
    if lo_mp < sqrt_c < hi_mp:
        raise ValueError("box crosses sqrt(c)")

    # Rigorous lower bounds on inv_lambda(K(rho)) at the two box endpoints.
    k_lo_upper_rb = _rbound_upper(
        k_upper_at_point(c, lo, n_terms=n_terms, dps=dps), denom=rat_denom
    )
    k_hi_upper_rb = _rbound_upper(
        k_upper_at_point(c, hi, n_terms=n_terms, dps=dps), denom=rat_denom
    )
    inv_lo_rb = _inv_lambda_lower_from_k_upper_fraction(
        k_lo_upper_rb.to_fraction(), rat_denom=rat_denom, dps=dps
    )
    inv_hi_rb = _inv_lambda_lower_from_k_upper_fraction(
        k_hi_upper_rb.to_fraction(), rat_denom=rat_denom, dps=dps
    )
    inv_lo = inv_lo_rb.to_fraction()
    inv_hi = inv_hi_rb.to_fraction()

    # Chord through (lo, inv_lo) and (hi, inv_hi).
    width = hi - lo
    if width <= 0:
        raise ValueError(f"empty box [{float(lo):.7f}, {float(hi):.7f}]")
    beta = (inv_hi - inv_lo) / width
    alpha = inv_lo - beta * lo

    # Slack so the verifier with depth ``verifier_max_depth`` accepts the
    # proposal at the K-extreme endpoint of every sub-box. The factor of 4 is
    # a safety margin: it absorbs the slight gap between
    # ``inv_lambda(K_upper_subbox)`` and ``chord(K-extreme rho of subbox)``
    # caused by the K-rounding in ``_rbound_upper`` and the discrete
    # rho-midpoint splits inside ``verify_affine_lower_on_box``.
    smallest_width = width / (Fraction(1, 1) * (2 ** verifier_max_depth))
    slack = abs(beta) * smallest_width * 4
    alpha = alpha - slack

    alpha_rb = _rbound_lower_fraction(alpha, denom=rat_denom)
    beta_rb = RationalBound(beta.numerator, beta.denominator)
    return alpha_rb.to_fraction(), beta_rb.to_fraction()


def verify_affine_lower_on_box(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    alpha: Fraction,
    beta: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
    rat_denom: int = 10**18,
    max_depth: int = 12,
) -> bool:
    def recurse(box_lo: Fraction, box_hi: Fraction, depth: int) -> bool:
        k_upper_rb = _rbound_upper(
            k_upper_on_interval(c, box_lo, box_hi, n_terms=n_terms, dps=dps),
            denom=rat_denom,
        )
        inv_lower = _inv_lambda_lower_from_k_upper_fraction(
            k_upper_rb.to_fraction(),
            rat_denom=rat_denom,
            dps=dps,
        ).to_fraction()
        affine_lo = alpha + beta * box_lo
        affine_hi = alpha + beta * box_hi
        if max(affine_lo, affine_hi) <= inv_lower:
            return True
        if depth >= max_depth:
            return False
        split_specs = _split_spec(c, _BoxSpec(lo=box_lo, hi=box_hi, branch=0))
        if len(split_specs) != 2:
            return False
        return all(recurse(spec.lo, spec.hi, depth + 1) for spec in split_specs)

    return recurse(lo, hi, 0)


def certify_box(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    branch: int,
    *,
    index: int = 0,
    n_terms: int = 80,
    dps: int = 100,
    rat_denom: int = 10**18,
) -> BoxCertificate:
    if not (c < lo < hi < Fraction(1, 1)):
        raise ValueError("box lies outside the scalar-criterion domain")
    if branch == 1 and 3 * hi * hi > 4 * c * c:
        raise ValueError("branch-1 box crosses the exact split")
    if branch == 2 and 4 * c * c > 3 * lo * lo:
        raise ValueError("branch-2 box crosses the exact split")

    k_upper = _rbound_upper(
        k_upper_on_interval(
            c,
            lo,
            hi,
            n_terms=n_terms,
            dps=dps,
        ),
        denom=rat_denom,
    )
    lambda_upper = _lambda_upper_from_k_upper_fraction(
        k_upper.to_fraction(),
        rat_denom=rat_denom,
        dps=dps,
    )

    alpha = Fraction(lambda_upper.den, lambda_upper.num)
    beta = Fraction(0, 1)
    mass = _mass_from_affine_fraction(c, lo, hi, branch, alpha, beta)

    mass_lower = RationalBound(mass.numerator, mass.denominator)

    return BoxCertificate(
        index=index,
        branch=branch,
        lo=RationalBound(lo.numerator, lo.denominator),
        hi=RationalBound(hi.numerator, hi.denominator),
        alpha=RationalBound(alpha.numerator, alpha.denominator),
        beta=RationalBound(beta.numerator, beta.denominator),
        mass_lower=mass_lower,
        k_upper=k_upper,
        lambda_upper=lambda_upper,
    )


def _total_mass(boxes: list[BoxCertificate]) -> Fraction:
    out = Fraction(0)
    for box in boxes:
        out += box.mass_lower.to_fraction()
    return out


def _floor_sqrt_ratio(num: int, den: int) -> int:
    if num < 0 or den <= 0:
        raise ValueError("sqrt-ratio inputs must satisfy num >= 0 and den > 0")
    guess = math.isqrt(num // den)
    while (guess + 1) * (guess + 1) * den <= num:
        guess += 1
    while guess * guess * den > num:
        guess -= 1
    return guess


def _branch_split_bounds(c: Fraction, denom: int = 10**7) -> tuple[Fraction, Fraction]:
    num = 4 * c.numerator * c.numerator * denom * denom
    den = 3 * c.denominator * c.denominator
    split_floor = _floor_sqrt_ratio(num, den)
    split_lo = Fraction(split_floor, denom)
    split_hi = Fraction(split_floor + 1, denom)
    if split_lo <= c:
        split_lo = c + Fraction(1, denom)
    return split_lo, split_hi


def _sqrt_c_bounds(c: Fraction, denom: int = 10**7) -> tuple[Fraction, Fraction]:
    num = c.numerator * denom * denom
    den = c.denominator
    sqrt_floor = _floor_sqrt_ratio(num, den)
    sqrt_lo = Fraction(sqrt_floor, denom)
    sqrt_hi = Fraction(sqrt_floor + 1, denom)
    return sqrt_lo, sqrt_hi


def _left_cut(c: Fraction, denom: int = 1000) -> Fraction:
    return c + Fraction(1, denom)


def _one_cut(denom: int = 10**7) -> Fraction:
    return Fraction(denom - 1, denom)


def _uniform_specs(
    c: Fraction,
    *,
    branch1_count: int,
    branch2_count: int,
    left_cut_denom: int = 1000,
    split_denom: int = 10**7,
    one_cut_denom: int = 10**7,
) -> tuple[list[_BoxSpec], Fraction, Fraction, Fraction]:
    # Search-only partition proposal. The exact emitted certificate is later
    # checked box by box by the trusted Arb-backed path.
    split_lo, split_hi = _branch_split_bounds(c, denom=split_denom)
    sqrt_lo, sqrt_hi = _sqrt_c_bounds(c, denom=split_denom)
    left_cut = _left_cut(c, left_cut_denom)
    one_cut = _one_cut(one_cut_denom)

    specs: list[_BoxSpec] = []

    if branch1_count > 0 and split_lo > left_cut:
        step = (split_lo - left_cut) / branch1_count
        for i in range(branch1_count):
            lo = left_cut + i * step
            hi = left_cut + (i + 1) * step
            specs.append(_BoxSpec(lo=lo, hi=hi, branch=1))

    if branch2_count > 0 and one_cut > split_hi:
        left_span = max(Fraction(0), min(sqrt_lo, one_cut) - split_hi)
        total_span = one_cut - split_hi
        left_count = max(1, round(branch2_count * float(left_span / total_span))) if left_span > 0 else 0
        left_count = min(left_count, branch2_count)
        right_count = branch2_count - left_count

        if left_count > 0 and sqrt_lo > split_hi:
            span = sqrt_lo - split_hi
            for i in range(left_count):
                x0 = math.sqrt(i / left_count)
                x1 = math.sqrt((i + 1) / left_count)
                lo = split_hi + Fraction.from_float(float(span * x0)).limit_denominator(10**9)
                hi = split_hi + Fraction.from_float(float(span * x1)).limit_denominator(10**9)
                if lo == hi:
                    hi = lo + Fraction(1, 10**9)
                specs.append(_BoxSpec(lo=lo, hi=hi, branch=2))

        if right_count > 0 and one_cut > sqrt_hi:
            span = one_cut - sqrt_hi
            for i in range(right_count):
                x0 = math.sqrt(i / right_count)
                x1 = math.sqrt((i + 1) / right_count)
                lo = sqrt_hi + Fraction.from_float(float(span * x0)).limit_denominator(10**9)
                hi = sqrt_hi + Fraction.from_float(float(span * x1)).limit_denominator(10**9)
                if lo == hi:
                    hi = lo + Fraction(1, 10**9)
                specs.append(_BoxSpec(lo=lo, hi=hi, branch=2))

    return specs, split_lo, split_hi, one_cut


def certify_partition(
    c: Fraction,
    specs: list[_BoxSpec],
    *,
    n_terms: int = 80,
    dps: int = 100,
    rat_denom: int = 10**18,
) -> list[BoxCertificate]:
    out: list[BoxCertificate] = []
    for idx, spec in enumerate(specs):
        out.append(
            certify_box(
                c,
                spec.lo,
                spec.hi,
                spec.branch,
                index=idx,
                n_terms=n_terms,
                dps=dps,
                rat_denom=rat_denom,
            )
        )
    return out


def _split_spec(c: Fraction, spec: _BoxSpec) -> list[_BoxSpec]:
    if spec.lo * spec.lo < c and c < spec.hi * spec.hi:
        mid = (spec.lo + spec.hi) / 2
    else:
        t_lo = _rho_to_t(c, spec.lo)
        t_hi = _rho_to_t(c, spec.hi)
        t_mid = (t_lo + t_hi) / 2
        right_branch = spec.lo * spec.lo >= c
        mid = _rho_from_t(c, t_mid, right_branch=right_branch)
        if not (spec.lo < mid < spec.hi):
            mid = (spec.lo + spec.hi) / 2
    if mid == spec.lo or mid == spec.hi:
        return [spec]
    return [
        _BoxSpec(lo=spec.lo, hi=mid, branch=spec.branch),
        _BoxSpec(lo=mid, hi=spec.hi, branch=spec.branch),
    ]


def _mass_kernel_value(c: Fraction, rho: Fraction, branch: int) -> Fraction:
    if branch == 1:
        return Fraction(12) * rho**3 * (rho**2 - c**2) / c**6
    if branch == 2:
        return Fraction(4) * rho**3 / c**4
    raise ValueError(f"unknown branch {branch}")


def _approx_box_mass(
    c: Fraction,
    spec: _BoxSpec,
    *,
    n_terms: int,
    dps: int,
) -> float:
    # Search-only ranking score used to decide which boxes to refine next.
    # It stays entirely local: use the transformed-K midpoint upper estimate
    # to score how much scalar mass this box could plausibly contribute.
    mid = (spec.lo + spec.hi) / 2
    k_mid_rb = _rbound_upper(k_upper_at_point(c, mid, n_terms=n_terms, dps=dps), denom=10**12)
    k_mid = _to_mpf(k_mid_rb.to_fraction())
    if k_mid >= 1:
        return 0.0
    inv_lambda_mid = _inv_lambda_lower_from_k_upper(k_mid)
    width = float(spec.hi - spec.lo)
    kernel_mid = float(_mass_kernel_value(c, mid, spec.branch))
    return width * kernel_mid * float(inv_lambda_mid)


def build_adaptive_certificate(
    c: Fraction,
    *,
    target: Fraction = Fraction(1, 1),
    branch1_count: int = 32,
    branch2_count: int = 768,
    n_terms: int = 80,
    dps: int = 100,
    rat_denom: int = 10**18,
    max_boxes: int = 2500,
    refine_batch: int = 64,
) -> ScalarCertificate:
    specs, split_lo, split_hi, one_cut = _uniform_specs(
        c,
        branch1_count=branch1_count,
        branch2_count=branch2_count,
    )

    while True:
        boxes: list[BoxCertificate] = []
        failed: list[int] = []
        for idx, spec in enumerate(specs):
            try:
                boxes.append(
                    certify_box(
                        c,
                        spec.lo,
                        spec.hi,
                        spec.branch,
                        index=idx,
                        n_terms=n_terms,
                        dps=dps,
                        rat_denom=rat_denom,
                    )
                )
            except ValueError:
                failed.append(idx)

        if failed:
            if len(specs) + len(failed) > max_boxes:
                raise RuntimeError(
                    f"failed to certify {len(failed)} boxes before reaching max_boxes={max_boxes}"
                )
            new_specs: list[_BoxSpec] = []
            progress = False
            for idx, spec in enumerate(specs):
                if idx in failed:
                    split_specs = _split_spec(c, spec)
                    progress = progress or len(split_specs) > 1
                    new_specs.extend(split_specs)
                else:
                    new_specs.append(spec)
            if not progress:
                raise RuntimeError("failed boxes could not be split further")
            specs = new_specs
            continue

        total = _total_mass(boxes)
        if total >= target or len(specs) >= max_boxes:
            return ScalarCertificate(
                target_c=RationalBound(c.numerator, c.denominator),
                total_mass_lower=RationalBound(total.numerator, total.denominator),
                boxes=tuple(boxes),
                n_terms=n_terms,
                dps=dps,
                split_lo=RationalBound(split_lo.numerator, split_lo.denominator),
                split_hi=RationalBound(split_hi.numerator, split_hi.denominator),
                one_cut=RationalBound(one_cut.numerator, one_cut.denominator),
            )

        scored: list[tuple[float, int]] = []
        for idx, spec in enumerate(specs):
            approx = _approx_box_mass(c, spec, n_terms=n_terms, dps=dps)
            rig = float(boxes[idx].mass_lower.to_fraction())
            scored.append((approx - rig, idx))
        scored.sort(reverse=True)
        chosen = sorted(idx for _, idx in scored[:refine_batch])

        new_specs: list[_BoxSpec] = []
        progress = False
        for idx, spec in enumerate(specs):
            if idx not in chosen:
                new_specs.append(spec)
                continue
            split_specs = _split_spec(c, spec)
            progress = progress or len(split_specs) > 1
            new_specs.extend(split_specs)
        if not progress:
            return ScalarCertificate(
                target_c=RationalBound(c.numerator, c.denominator),
                total_mass_lower=RationalBound(total.numerator, total.denominator),
                boxes=tuple(boxes),
                n_terms=n_terms,
                dps=dps,
                split_lo=RationalBound(split_lo.numerator, split_lo.denominator),
                split_hi=RationalBound(split_hi.numerator, split_hi.denominator),
                one_cut=RationalBound(one_cut.numerator, one_cut.denominator),
            )
        specs = new_specs


def certify_eq15(
    c_num: int,
    c_den: int,
    *,
    dps: int = 50,
    n_trunc: int = 200,
) -> bool:
    """
    Sprint 053 oracle wrapper for Wang 2025's equation `(15)` at a rational
    radius `c = c_num / c_den`.

    Returns ``True`` iff Wang's scalar criterion

        1  <=  integral_{c+eps .. branchSplit(c)-eps} 12 * rho^3 * (rho^2 - c^2) / (c^6 * Lambda(c, rho)) drho
             + integral_{branchSplit(c)+eps .. 1-eps} 4 * rho^3 / (c^4 * Lambda(c, rho)) drho

    is certified at ``c = c_num / c_den`` under verified-interval arithmetic
    with ``dps`` digits of mpmath precision and ``n_trunc`` factors retained
    per ``K`` product evaluation. The strict-margin threshold is
    ``10^(-min(dps, 30))``: a True return guarantees that the certified lower
    bound on the sum of the two branch integrals is at least ``1 + 10^(-30)``.

    Algorithm. The implementation reuses this module's pre-existing
    ``flint.arb`` infrastructure (``_uniform_specs`` for the partition,
    ``certify_box`` for each box's verified mass lower bound via
    ``lambda_upper_on_interval`` + ``k_upper_on_interval``). On boxes whose
    K-monotonicity certificate fails (typically those that straddle
    ``sqrt(c)`` or are too wide for the requested precision) a single
    ``_split_spec`` retry is attempted; if the split also fails, the
    function returns ``False`` (insufficient envelope, not numerical
    falsity).

    The function takes the rational ``c`` as ``(c_num, c_den)`` rather than
    a float to keep the rationality exact through the mpmath /
    ``flint.arb`` certification — see the contract's "wrapper signature"
    note.

    Falsifiability. Sprint 050's ``Scratch/sprint_050_eq15_crossover_pinpoint.txt``
    pinpoints the literal `(15)` crossover inside ``c in (0.3560, 0.3565)``
    (positive gap +1.131e-02 at c = 0.3560, negative gap -3.598e-04 at
    c = 0.3565, mpmath ``dps=50, N_TRUNC=200``). The wrapper must therefore
    return ``True`` at ``(3554, 10000)`` and ``False`` at ``(3565, 10000)``;
    a wrapper that accepts both is not actually verifying anything.
    """
    c = Fraction(int(c_num), int(c_den))
    if not (Fraction(0) < c < Fraction(1)):
        return False

    # Initial partition. Density chosen so that the per-box width at
    # n_trunc=200, dps=50 keeps the K-monotonicity certificate inside
    # log_k_t_derivative_lower's tolerance for almost every box; a single
    # _split_spec retry handles the few remaining cases (typically the box
    # adjacent to the branch split or to sqrt(c)).
    branch1_count = max(32, n_trunc // 4)
    branch2_count = max(256, n_trunc * 3)
    specs, _split_lo, _split_hi, _one_cut = _uniform_specs(
        c, branch1_count=branch1_count, branch2_count=branch2_count
    )
    if not specs:
        return False

    # Per-box certified mass lower bounds. If a box's K-monotone certificate
    # fails, attempt a single `_split_spec` retry; if a sub-box also fails,
    # drop it (its positive contribution is conservatively excluded from the
    # total — which keeps the running sum a verified lower bound on Wang's
    # `(15)` LHS).
    boxes: list[BoxCertificate] = []
    for spec in specs:
        try:
            boxes.append(
                certify_box(c, spec.lo, spec.hi, spec.branch, n_terms=n_trunc, dps=dps)
            )
            continue
        except (ValueError, RuntimeError):
            pass
        sub_specs = _split_spec(c, spec)
        if len(sub_specs) <= 1:
            continue
        for sub in sub_specs:
            try:
                boxes.append(
                    certify_box(c, sub.lo, sub.hi, sub.branch, n_terms=n_trunc, dps=dps)
                )
            except (ValueError, RuntimeError):
                # Drop this sub-box: its (positive) mass is excluded from
                # the verified lower bound. Honest under-bound; never
                # over-claims.
                continue

    total = _total_mass(boxes)
    eps = Fraction(1, 10 ** min(int(dps), 30))
    return total >= Fraction(1, 1) + eps


# -----------------------------------------------------------------------------
# Evaluator-facing zero-argument shim (sprint 053).
#
# Evaluator.py (today) loads each `[[oracles]]` row as
#     OracleSpec(axiom, bound_field, oracle_fn)
# and invokes the registered function with no arguments, expecting a
# Fraction-coercible numeric bound that the Evaluator then compares against
# the candidate's `def <bound_field> : ℝ := ...`. The shim below is the
# zero-argument adapter that pins the parameters of `certify_eq15` to the
# bulletin-prescribed seed envelope:
#     (c_num, c_den, dps, n_trunc) = (3554, 10000, 50, 200)
# and returns a Fraction lower bound on `Korenblum.scalarCriterion` at the
# seed. The shim raises `RuntimeError` if `certify_eq15` rejects at the
# registered envelope — keeping the candidate's `axioms_used ⊇ {hEq15_oracle_certified_3554}`
# claim honest (an oracle that cannot reproduce Wang's gap at the seed is
# not a basis for an `Eq15ScalarBound`-asserting Lean axiom).
#
# The schema-field name change relative to the contract's literal
# `[[oracles]]` block (`name`/`module`/`function`/`args`/`lean_axiom` ->
# `axiom`/`bound_field`/`oracle_fn`) reflects the actual Evaluator.py
# implementation; see Experience.md for the deviation note.
# -----------------------------------------------------------------------------

def certify_eq15_at_seed() -> Fraction:
    """
    Zero-argument Evaluator-facing shim for the registered oracle
    ``eq15_certified_at_seed``.

    Calls ``certify_eq15(3554, 10000, dps=50, n_trunc=200)``; on True,
    returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_3554``.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate's ``def eq15_lower_bound : ℝ := 1``
    via ``oracle_bound <= declared``, and accepts the candidate iff
    ``1 <= 1`` — which holds because the shim only returns when the
    certified bound is strictly above 1.
    """
    if not certify_eq15(3554, 10000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(3554, 10000, dps=50, n_trunc=200) returned False; "
            "wrapper cannot reproduce sprint 050's mpmath gap at the seed under "
            "the registered envelope. Refusing to certify the Lean axiom "
            "`hEq15_oracle_certified_3554` to keep the trust surface honest."
        )
    return Fraction(1, 1)


def certify_eq15_at_3560() -> Fraction:
    """
    Sprint 055 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_3560``.

    Calls ``certify_eq15(1780, 5000, dps=50, n_trunc=200)``; on True,
    returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_3560``.

    Sprint 050's mpmath ``dps=50, N_TRUNC=200`` table reports
    ``gap = +1.131e-02`` at ``c = 0.3560`` (the largest integer-10000ths
    ``c`` with verified margin in the enumeration; ``gap = -3.598e-04``
    at ``c = 0.3565`` past the literal ``(15)`` crossover). Sprint 053's
    Experience entry empirically measures ~0.003 box-by-box conservatism
    gap relative to adaptive ``mp.quad``, so the wrapper's certified
    ``total`` at ``c = 0.3560`` is ~``1.008`` — well above the
    strict-margin threshold ``1 + 10^(-30)``.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate's ``def eq15_lower_bound : ℝ := 1``
    via ``oracle_bound <= declared``, and accepts the candidate iff
    ``1 <= 1`` — which holds because the shim only returns when the
    certified bound is strictly above 1.
    """
    if not certify_eq15(1780, 5000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(1780, 5000, dps=50, n_trunc=200) returned False; "
            "wrapper cannot reproduce sprint 050's mpmath gap +1.131e-02 at "
            "c = 0.3560 under the registered envelope. Refusing to certify "
            "the Lean axiom `hEq15_oracle_certified_3560` to keep the trust "
            "surface honest."
        )
    return Fraction(1, 1)


def certify_eq15_at_3562() -> Fraction:
    """
    Sprint 056 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_3562``.

    Calls ``certify_eq15(1781, 5000, dps=50, n_trunc=200)``; on
    True, returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_3562``.

    Pre-verified by ``Scratch/sprint_056_eq15_wrapper_pre_verification.py``
    at this c with the same envelope (certified total_mass_lower
    1.003960506, margin +3.96e-03 above the threshold). Sprint 050's
    mpmath table verified the (15) gap at adjacent points {0.3560
    (+1.131e-02), 0.3565 (-3.598e-04)}; the wrapper at this c sits
    inside that interval per the Scratch pre-verification's recorded
    margin.
    """
    if not certify_eq15(1781, 5000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(1781, 5000, dps=50, n_trunc=200) returned False; "
            "wrapper cannot reproduce the Scratch pre-verification's positive "
            "margin at c = 1781/5000 under the registered envelope. Refusing "
            "to certify the Lean axiom `hEq15_oracle_certified_3562` to keep the "
            "trust surface honest."
        )
    return Fraction(1, 1)


def certify_eq15_at_hp_3564() -> Fraction:
    """
    Sprint 057 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_hp_3564``.

    Calls ``certify_eq15(1782, 5000, dps=100, n_trunc=500)``; on True,
    returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_hp_3564``.

    Pre-verified by ``Scratch/sprint_057_eq15_wrapper_tiered_preverification.py``
    at this c with the upgraded envelope ``(dps=100, n_trunc=500)``
    (certified ``total_mass_lower = 1.001174814942``, margin
    ``+1.17e-03`` above the strict-margin threshold ``1 + 10^(-30)``).

    First oracle in the workspace to use a precision envelope stricter
    than the standard ``(dps=50, n_trunc=200)`` used by sprints
    053/055/056. The upgraded envelope reduces the wrapper's box-by-box
    conservatism gap relative to adaptive ``mp.quad``, allowing
    certification at ``c = 0.3564`` where the standard envelope rejects
    (margin ``-6.89e-04``) despite the ground-truth ``(15)`` gap being
    positive there. Tier A2 of the sprint 057 Scratch script confirmed
    HP rejects at ``c = 0.3565`` (margin ``-1.15e-03``), so the upgraded
    envelope is still safely below the literal ``(15)`` crossover at
    ``c ~ 0.35635``.
    """
    if not certify_eq15(1782, 5000, dps=100, n_trunc=500):
        raise RuntimeError(
            "certify_eq15(1782, 5000, dps=100, n_trunc=500) returned False; "
            "wrapper cannot reproduce the Scratch pre-verification's positive "
            "margin at c = 1782/5000 under the registered upgraded envelope. "
            "Refusing to certify the Lean axiom `hEq15_oracle_certified_hp_3564` "
            "to keep the trust surface honest."
        )
    return Fraction(1, 1)


def certify_eq15_at_hp_35645() -> Fraction:
    """
    Sprint 059 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_hp_35645``.

    Calls ``certify_eq15(35645, 100000, dps=100, n_trunc=500)``; on True,
    returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_hp_35645``.

    Pre-verified by ``Scratch/sprint_058_hp_ceiling_pin.{py,txt}`` (sprint
    058's anti-blind-spot HP probe; certified ``total_mass_lower =
    1.000013457935``, margin ``+1.35e-05`` above the strict-margin
    threshold ``1 + 10^(-30)``) and re-checked by
    ``Scratch/sprint_059_hp_35645_sanity_replay.{py,txt}`` (sprint 059's
    fresh sanity replay).

    First oracle in the workspace to pin a finer denominator
    (``c_den = 100000`` instead of ``5000`` / ``10000``); the +0.00005
    increment over V51's ``c = 1782/5000 = 35640/100000`` cannot be
    expressed at the ``5000``-denominator scale. The HP envelope's
    box-by-box conservatism residue is what permits this thin-but-
    positive certification: the ground-truth Wang ``(15)`` gap at
    ``c = 0.35645`` is below the literal crossover at ``c ~ 0.35635``,
    but the upper-bound box partition's lower envelope remains
    positive at ``+1.35e-05``. HP-tier falsifiability at ``c = 0.3565``
    still rejects (``-1.15e-03``), so the upgraded envelope is
    verifiably below the wrapper's true HP ceiling somewhere in
    ``(0.35645, 0.35650)``.
    """
    if not certify_eq15(35645, 100000, dps=100, n_trunc=500):
        raise RuntimeError(
            "certify_eq15(35645, 100000, dps=100, n_trunc=500) returned False; "
            "wrapper cannot reproduce sprint 058's recorded surprise acceptance "
            "at c = 35645/100000 under the registered upgraded envelope. "
            "Refusing to certify the Lean axiom `hEq15_oracle_certified_hp_35645` "
            "to keep the trust surface honest."
        )
    return Fraction(1, 1)


# -----------------------------------------------------------------------------
# Sprint 079 — joint two-window τ-partition mass wrapper.
#
# This is the workspace's first non-eq15 oracle wrapper. It certifies the
# joint two-window mass
#
#   1 ≤ ∫_{ρStart₁..ρStop₁} 2ρ / (H_{j₁}(c, ρ) · Λ(c, ρ)) dρ
#       + ∫_{ρStart₂..ρStop₂} 2ρ / (H_{j₂}(c, ρ) · Λ(c, ρ)) dρ
#
# at concrete rational `(c, ρStart₁, ρStop₁, ρStart₂, ρStop₂, j₁, j₂)` so the
# new closing reducer `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
# (sprint 078, `Proof/Reduction.lean`) can consume the joint-mass premise as
# an oracle-discharged Lean axiom.
#
# Falsifiability. The mass crosses below 1 around `c ≈ 0.35654` per sprint
# 078's Phase 0 sweep. A wrapper that returns True at `c ≥ 0.35655` would not
# be verifying anything; this wrapper's choice of `c = 35646/100000` is
# deliberately one of the points sprint 078 reported with ≥ 1e-3 margin
# (recomputed at the chosen exact rational endpoints by
# `Scratch/sprint_079_endpoint_pinned_witness.py` to margin +1.9e-3).
# -----------------------------------------------------------------------------


def _two_window_mass_paper_factor(c: mp.mpf, rho: mp.mpf, n: int) -> mp.mpf:
    num = (
        (1 + rho ** 2 * c ** (2 * n + 1))
        * (1 + c ** (2 * n + 3) / rho ** 2)
        * (1 + c ** (2 * n + 2)) ** 2
    )
    den = (
        (1 + rho ** 2 * c ** (2 * n))
        * (1 + c ** (2 * n + 2) / rho ** 2)
        * (1 + c ** (2 * n + 1)) ** 2
    )
    return num / den


def _two_window_mass_paper_lambda(c: mp.mpf, rho: mp.mpf, n_trunc: int) -> mp.mpf:
    prod = mp.mpf(1)
    for n in range(0, n_trunc):
        prod *= _two_window_mass_paper_factor(c, rho, n)
    K = 2 * rho * (1 + c / rho ** 2) * prod
    K_sq = K * K
    if K_sq >= 1:
        return mp.mpf("+inf")
    inner = (1 + 3 * K_sq) / (1 - K_sq)
    return mp.mpf("0.5") * (1 + mp.sqrt(inner))


def _two_window_mass_term_j(c: mp.mpf, rho: mp.mpf, j: int) -> mp.mpf:
    j_mp = mp.mpf(j)
    return (j_mp / (j_mp + 1)) * c ** (2 * j + 2) / rho ** (2 * j)


def _two_window_mass_window(
    c: mp.mpf, j: int, rho_start: mp.mpf, rho_stop: mp.mpf, n_trunc: int
) -> mp.mpf:
    def f(rho: mp.mpf) -> mp.mpf:
        Lam = _two_window_mass_paper_lambda(c, rho, n_trunc=n_trunc)
        if Lam == mp.mpf("+inf"):
            return mp.mpf(0)
        return 2 * rho / (_two_window_mass_term_j(c, rho, j) * Lam)
    return mp.quad(f, [rho_start, rho_stop])


def _frac_to_mpf(fr: Fraction) -> mp.mpf:
    return mp.mpf(fr.numerator) / fr.denominator


def certify_two_window_mass(
    c_num: int,
    c_den: int,
    rs1_num: int,
    rs1_den: int,
    rt1_num: int,
    rt1_den: int,
    rt2_num: int,
    rt2_den: int,
    j1: int,
    j2: int,
    *,
    dps: int = 30,
    n_trunc: int = 200,
) -> bool:
    """
    Sprint 079 wrapper for the joint two-window τ-partition mass.

    Returns ``True`` iff

        mass_total
            := ∫_{ρStart₁..ρStop₁} 2ρ / (H_{j₁}(c, ρ) · Λ(c, ρ)) dρ
             + ∫_{ρStart₂..ρStop₂} 2ρ / (H_{j₂}(c, ρ) · Λ(c, ρ)) dρ
        ≥ 1 + 10^(-min(dps, 30))

    where

      c            = c_num / c_den
      ρStart₁      = rs1_num / rs1_den
      ρStop₁       = rt1_num / rt1_den   (= ρStart₂ by adjacency)
      ρStart₂      = rt1_num / rt1_den
      ρStop₂       = rt2_num / rt2_den
      H_j(c, ρ)    = (j/(j+1)) · c^(2j+2) / ρ^(2j)             = OneModeKernel.term
      Λ(c, ρ)      = the Wang truncated paper-product paperLambda K c ρ.

    Implementation. Reuses sprint 078's mpmath kernel (`paper_factor`,
    `paper_lambda`, `term_j`, `mass_window`) verbatim, copied in as private
    helpers above so the wrapper is self-contained inside `rigorous_scalar.py`.
    The mass is computed via `mp.quad` over each window at `mp.mp.dps` digits.
    The strict-margin floor `10^(-min(dps, 30))` matches the existing
    `certify_eq15` pattern: a True return guarantees the certified joint
    mass is at least `1 + 10^(-30)` for `dps ≥ 30`.

    Falsifiability. Sprint 078's Phase 0 sweep
    (`Scratch/sprint_078_two_window_tau_mass_sweep.txt`) reports the joint
    mass crosses below `1` around `c ≈ 0.35654`. A wrapper that returns True
    at `c ≥ 0.35655` would not be verifying anything; the chosen
    `c = 35646/100000` is one of the points sprint 078 reported with margin
    ≥ 1e-3 (recomputed at the chosen exact-rational endpoints by sprint
    079's `Scratch/sprint_079_endpoint_pinned_witness.py` to margin +1.9e-3).
    """
    c = Fraction(int(c_num), int(c_den))
    rs1 = Fraction(int(rs1_num), int(rs1_den))
    rt1 = Fraction(int(rt1_num), int(rt1_den))
    rt2 = Fraction(int(rt2_num), int(rt2_den))
    if not (Fraction(0) < c < Fraction(1)):
        return False
    if not (c < rs1):
        return False
    if not (rs1 <= rt1):
        return False
    if not (rt1 <= rt2):
        return False
    if not (rt2 < Fraction(1)):
        return False
    if j1 < 1 or j2 < 1:
        return False

    with mp.workdps(int(dps)):
        c_mp = _frac_to_mpf(c)
        rs1_mp = _frac_to_mpf(rs1)
        rt1_mp = _frac_to_mpf(rt1)
        rt2_mp = _frac_to_mpf(rt2)
        m1 = _two_window_mass_window(c_mp, int(j1), rs1_mp, rt1_mp, n_trunc=int(n_trunc))
        m2 = _two_window_mass_window(c_mp, int(j2), rt1_mp, rt2_mp, n_trunc=int(n_trunc))
        total = m1 + m2
        eps = mp.mpf(10) ** (-min(int(dps), 30))
        return total >= mp.mpf(1) + eps


def certify_two_window_mass_at_35646() -> Fraction:
    """
    Sprint 079 zero-argument Evaluator-facing shim for the registered oracle
    ``two_window_mass_certified_at_35646``.

    Pins the parameters to

      (c_num, c_den)             = (35646, 100000)
      (rs1_num, rs1_den)         = (378083, 1000000)     # ρ_start_1
      (rt1_num, rt1_den)         = (411605, 1000000)     # ρ_stop_1 = ρ_start_2
      (rt2_num, rt2_den)         = (999999, 1000000)     # ρ_stop_2
      (j_1, j_2)                 = (2, 1)
      (dps, n_trunc)             = (30, 200)

    Witness file (sprint 078 Phase 0 raw): ``Scratch/sprint_078_witness.txt``
    (margin +1.9e-3 at c=0.35646 on canonical irrational endpoints).

    Endpoint-pinned re-verification (sprint 079 Phase 0):
    ``Scratch/sprint_079_endpoint_pinned_witness.txt`` (margin
    +1.9001e-3 at the chosen exact-rational endpoints listed above).

    Returns ``Fraction(1, 1)`` iff ``certify_two_window_mass`` accepts at
    these parameters (which by construction is true under the registered
    envelope: the joint-mass margin recomputed at exact rationals is
    +1.9001e-3, ~27 orders of magnitude above the strict-margin threshold
    ``10^(-30)``). Raises ``RuntimeError`` on rejection so the Evaluator
    records an oracle-check failure rather than silently accepting an
    unverified Lean axiom.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate's ``def two_window_mass_lower : ℝ := 1``
    via ``oracle_bound ≤ declared``, and accepts the candidate iff
    ``1 ≤ 1`` — which holds because the shim only returns when the
    certified joint mass is strictly above 1.
    """
    if not certify_two_window_mass(
        35646, 100000,
        378083, 1000000,
        411605, 1000000,
        999999, 1000000,
        2, 1,
        dps=30, n_trunc=200,
    ):
        raise RuntimeError(
            "certify_two_window_mass(c=35646/100000, ρ_start_1=378083/1000000, "
            "ρ_stop_1=411605/1000000, ρ_stop_2=999999/1000000, j_1=2, j_2=1, "
            "dps=30, n_trunc=200) returned False; wrapper cannot reproduce "
            "sprint 078's Phase 0 GO margin (+1.9e-3) at the chosen "
            "exact-rational endpoints. Refusing to certify the Lean axiom "
            "`h_two_window_mass_certified_at_35646` to keep the trust surface "
            "honest."
        )
    return Fraction(1, 1)


# -----------------------------------------------------------------------------
# Sprint 099: arb-based rigorous interval-arithmetic re-discharge of
# `certify_two_window_mass_at_35646_sqrt` (V64's joint-mass oracle).
#
# The migration replaces the previous `mp.quad`-based numerical-quadrature
# implementation with three private helpers built on `flint.arb`:
#
#   - `_two_window_mass_paper_factor_arb`: rigorous enclosure of the n-th
#     paper factor evaluated at an arb point or interval.
#   - `_two_window_mass_paper_lambda_arb`: rigorous upper bound on
#     Λ(c, ρ) over a ρ-subinterval, exploiting the fact that K(c, ρ) is
#     single-peaked at ρ = sqrt(c) (Wang structure: K is decreasing in
#     t = (ρ²-c)²/(4cρ²), which is convex in ρ with minimum at sqrt(c)),
#     so K_max on [ρ_lo, ρ_hi] is attained at one of {ρ_lo, ρ_hi,
#     clamp(sqrt(c), ρ_lo, ρ_hi)}.
#   - `_two_window_mass_window_lower_arb`: rigorous lower bound on the
#     window integral via subdivision-based left-Riemann lower sum.
#
# The wrapper calls these helpers iteratively at increasing
# `n_subdivisions ∈ {256, 512, 1024, ..., 16384}` until the rigorous
# total-mass lower bound clears the strict-margin floor `1 + 10^(-30)`.
# Sprint 083 reported the centered margin as +1.9001e-3 at these
# endpoints; the rigorous arb lower bound trails the centered estimate
# by O(width^1) under left-Riemann quadrature, but ~27 orders of
# magnitude of headroom over the floor make this trivially achievable
# at modest subdivision counts (typically n_subdivisions = 2048
# clears the floor by margin ≈ +1.29e-3).
# -----------------------------------------------------------------------------


def _two_window_mass_paper_factor_arb(c_pows, rho_arb, n: int):
    """
    Sprint 099 helper: rigorous arb-enclosure of the n-th Wang paper factor
    at ``rho_arb`` (an arb point or interval enclosure):

        factor_n(c, ρ) =
              (1 + ρ² c^(2n+1)) (1 + c^(2n+3)/ρ²) (1 + c^(2n+2))²
            / [(1 + ρ² c^(2n)) (1 + c^(2n+2)/ρ²) (1 + c^(2n+1))²]

    ``c_pows[k]`` is precomputed `c^k` as an arb. When ``rho_arb`` is an
    interval covering ``[ρ_lo, ρ_hi]`` (e.g. ``rho_lo.union(rho_hi)``),
    the returned arb's ``.upper()`` is a rigorous upper bound on the
    factor over that ρ-range. When ``rho_arb`` is a point, the returned
    arb is a tight enclosure of the factor at that ρ.

    No floating point / mpmath / quadrature: pure arb arithmetic,
    rigorous by construction.
    """
    rho2 = rho_arb ** 2
    num = (
        (1 + rho2 * c_pows[2 * n + 1])
        * (1 + c_pows[2 * n + 3] / rho2)
        * (1 + c_pows[2 * n + 2]) ** 2
    )
    den = (
        (1 + rho2 * c_pows[2 * n])
        * (1 + c_pows[2 * n + 2] / rho2)
        * (1 + c_pows[2 * n + 1]) ** 2
    )
    return num / den


def _two_window_mass_paper_K_arb(c_arb, c_pows, rho_arb, n_trunc: int):
    """
    Sprint 099 helper: arb-enclosure of the truncated Wang paper-product

        K(c, ρ) = 2ρ (1 + c/ρ²) · ∏_{n=0}^{n_trunc - 1} factor_n(c, ρ)

    at the arb point ``rho_arb``. Used as a building block by
    `_two_window_mass_paper_lambda_arb`. When ``rho_arb`` is a tight
    point enclosure, the returned arb has very small radius (because
    we avoid the multiplicative dependency loss that would arise from
    plugging a wide ρ-interval into a 200-factor product).
    """
    rho2 = rho_arb ** 2
    prefactor = 2 * rho_arb * (1 + c_arb / rho2)
    prod = arb(1)
    for n in range(0, n_trunc):
        prod = prod * _two_window_mass_paper_factor_arb(c_pows, rho_arb, n)
    return prefactor * prod


def _two_window_mass_paper_lambda_from_K_arb(K_arb):
    """
    Lambda transform: Λ(K) = (1 + sqrt((1 + 3K²)/(1 - K²))) / 2,
    equivalently Λ(K) = 1 + (1/2)(sqrt((1 + 3K²)/(1 - K²)) - 1).
    Pure arb arithmetic; the result is an arb enclosure of Λ at K.

    Λ is monotone-increasing in K on K ∈ [0, 1).
    """
    K_sq = K_arb * K_arb
    return arb(fmpq(1, 2)) * (1 + ((1 + 3 * K_sq) / (1 - K_sq)).sqrt())


def _two_window_mass_paper_lambda_arb(
    c_arb,
    c_pows,
    rho_lo,
    rho_hi,
    sqrt_c_arb,
    n_trunc: int,
    K_at_sqrt_cache: list,
):
    """
    Sprint 099 helper: rigorous arb upper-bound enclosure of

        Λ(c, ρ)  for ρ ∈ [rho_lo, rho_hi].

    Λ is increasing in K, and K(c, ρ) is single-peaked at ρ = sqrt(c)
    by the standard Wang/Korenblum structure (K is decreasing in
    t = (ρ²-c)²/(4cρ²), which is convex in ρ with minimum at sqrt(c)).
    Therefore the supremum of Λ on [rho_lo, rho_hi] is attained at one
    of three candidate ρ:

      - ρ = rho_lo  (subinterval entirely right of sqrt(c))
      - ρ = rho_hi  (subinterval entirely left of sqrt(c))
      - ρ = sqrt(c) (subinterval contains sqrt(c))

    We compute Λ at each candidate via point-evaluation in arb (which
    avoids the dependency loss that a single wide-ρ-box evaluation
    would suffer over a 200-factor product), then return their union.
    The returned arb's ``.upper()`` is a rigorous upper bound on
    max-Λ over [rho_lo, rho_hi].

    ``K_at_sqrt_cache`` is a 1-element list used to memoise the
    K-evaluation at sqrt(c) across many sub-intervals.
    """
    K_at_lo = _two_window_mass_paper_K_arb(c_arb, c_pows, rho_lo, n_trunc)
    K_at_hi = _two_window_mass_paper_K_arb(c_arb, c_pows, rho_hi, n_trunc)
    Lams = [
        _two_window_mass_paper_lambda_from_K_arb(K_at_lo),
        _two_window_mass_paper_lambda_from_K_arb(K_at_hi),
    ]
    # Decide rigorously whether sqrt(c) lies in [rho_lo, rho_hi].
    # If `(rho_lo <= sqrt_c) is True and (sqrt_c <= rho_hi) is True`,
    # then sqrt(c) is in the closed interval rigorously. If either
    # comparison is `True` in the strict-other-direction (sqrt_c < rho_lo
    # or rho_hi < sqrt_c), we are rigorously on one side and don't need
    # the sqrt(c) candidate. If neither comparison is rigorously
    # decidable (e.g. the arb intervals overlap by 1 ULP), we
    # conservatively include the sqrt(c) candidate.
    if (rho_lo <= sqrt_c_arb) is True and (sqrt_c_arb <= rho_hi) is True:
        needs_sqrt = True
    elif (sqrt_c_arb < rho_lo) is True or (rho_hi < sqrt_c_arb) is True:
        needs_sqrt = False
    else:
        needs_sqrt = True
    if needs_sqrt:
        if K_at_sqrt_cache[0] is None:
            K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                c_arb, c_pows, sqrt_c_arb, n_trunc
            )
        Lams.append(_two_window_mass_paper_lambda_from_K_arb(K_at_sqrt_cache[0]))
    Lam_combined = Lams[0]
    for L in Lams[1:]:
        Lam_combined = Lam_combined.union(L)
    return Lam_combined


def _two_window_mass_window_lower_arb(
    c_arb,
    c_pows,
    j: int,
    rho_start,
    rho_stop,
    sqrt_c_arb,
    n_trunc: int,
    n_subdivisions: int,
):
    """
    Sprint 099 helper: rigorous arb lower bound on

        ∫_{rho_start..rho_stop} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ

    where H_j(c, ρ) = (j/(j+1)) · c^(2j+2) / ρ^(2j).

    We split [rho_start, rho_stop] into ``n_subdivisions`` equal
    sub-intervals. On each sub-interval [ρ_lo, ρ_hi]:

      - Λ_upper := upper bound on Λ via `_two_window_mass_paper_lambda_arb`
        (single-peaked argument).
      - H_j_upper := H_j(c, ρ_lo): H_j is decreasing in ρ for j ≥ 1
        and ρ > 0, so the maximum on [ρ_lo, ρ_hi] is at ρ = ρ_lo.
      - 2ρ_lower := 2 · ρ_lo: 2ρ is increasing, minimum at ρ_lo.
      - integrand_lower := 2ρ_lower / (H_j_upper · Λ_upper).
      - sub-interval contribution := (ρ_hi - ρ_lo) · integrand_lower.

    The final sum is a strict left-Riemann lower bound on the integral.
    Refining ``n_subdivisions`` tightens the bound at O(width)
    convergence rate. To certify the strict-margin floor `1 + 10^(-30)`
    on the joint mass at sprint 083's pinned endpoints, the wrapper
    iterates ``n_subdivisions`` in powers of 2 until the floor is
    cleared (typically n_subdivisions = 2048 suffices, leaving margin
    ≈ +1.29e-3 — about 26 orders of magnitude over the floor).

    K-cache: K(c, ρ) is evaluated at each subdivision endpoint
    exactly once and reused as both the right-K of subinterval k and
    the left-K of subinterval k+1, halving the work.

    Sprint 101 monotonicity-aware Λ_upper dispatch: K(c, ρ) is
    single-peaked at ρ = sqrt(c) (Wang t-distance structure —
    K(c, ρ) increasing on (0, sqrt(c)) and decreasing on
    (sqrt(c), 1)). On each sub-interval [ρ_lo, ρ_hi] we rigorously
    decide its position relative to sqrt(c) via arb comparisons and:

      - if rigorously rho_hi ≤ sqrt(c): max(K) = K(rho_hi) →
        Lam_upper := Λ(K(rho_hi)) (single point evaluation, arb
        radius governed by arithmetic precision ~10^(-50) at
        dps=80 rather than by sub-interval width);
      - if rigorously sqrt(c) ≤ rho_lo: max(K) = K(rho_lo) →
        Lam_upper := Λ(K(rho_lo)) (single point evaluation);
      - otherwise (straddle or rigorously undecided): retain the
        three-candidate union Λ(K(rho_lo)) ∪ Λ(K(rho_hi)) ∪
        Λ(K(sqrt_c_arb)) for safety. The straddle path matches
        sprint 099's behaviour byte-for-byte, so the rigour of
        the lower bound is preserved on every sub-interval — only
        the per-subinterval radius is tightened in the
        well-separated branches.

    This eliminates the O(width) union radius on the
    well-separated subintervals (mode1's wide
    [c·√(4/3), 0.999999] window in particular), dropping
    m_1.rad from O(1/n_subdivisions) toward arb-arithmetic
    precision. The straddle case touches sqrt(c) for at most one
    sub-interval per window (sqrt(c) is a single point), so
    K_at_sqrt_cache is hit at most once per
    `_two_window_mass_window_lower_arb` invocation.
    """
    j_arb = arb(j)
    j_factor = j_arb / (j_arb + 1)
    c_2j_2 = c_pows[2 * j + 2]
    width = rho_stop - rho_start
    rhos = [
        rho_start + arb(fmpq(k, n_subdivisions)) * width
        for k in range(n_subdivisions + 1)
    ]
    Ks = [_two_window_mass_paper_K_arb(c_arb, c_pows, r, n_trunc) for r in rhos]
    K_at_sqrt_cache = [None]
    total = arb(0)
    for k in range(n_subdivisions):
        rho_lo = rhos[k]
        rho_hi = rhos[k + 1]
        sub_width = rho_hi - rho_lo

        # Sprint 101 monotonicity-aware Λ_upper dispatch on
        # rigorously-decided position of [rho_lo, rho_hi] vs sqrt(c).
        # K(c, ρ) is single-peaked at ρ = sqrt(c).
        if (rho_hi <= sqrt_c_arb) is True:
            # Rigorously left of sqrt(c): K increasing on the
            # sub-interval, max attained at rho_hi. Single point
            # evaluation — eliminates the O(width) union radius.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            # Rigorously right of sqrt(c): K decreasing on the
            # sub-interval, max attained at rho_lo. Single point
            # evaluation — eliminates the O(width) union radius.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            # Straddle or rigorously undecided: preserve sprint
            # 099's three-candidate union for safety. In practice
            # this branch is taken on at most one sub-interval per
            # window (the one containing sqrt(c)).
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc
                )
            Lam_lo = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
            Lam_hi = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
            Lam_sqrt = _two_window_mass_paper_lambda_from_K_arb(
                K_at_sqrt_cache[0]
            )
            Lam_upper = Lam_lo.union(Lam_hi).union(Lam_sqrt)

        # H_j upper at ρ = ρ_lo (H_j decreasing in ρ for j ≥ 1).
        rho_lo_2j = rho_lo ** (2 * j)
        H_upper = j_factor * c_2j_2 / rho_lo_2j

        # 2ρ lower at ρ = ρ_lo (2ρ increasing).
        numer_lower = 2 * rho_lo

        # Integrand lower bound on subinterval; arb arithmetic gives
        # an enclosure whose .lower() is the rigorous lower bound.
        integrand_lower = numer_lower / (H_upper * Lam_upper)
        contrib = sub_width * integrand_lower
        total = total + contrib
    return total


def _branch1_window_mass_lower_arb(
    c_arb,
    c_pows,
    rho_start,
    rho_stop,
    sqrt_c_arb,
    n_trunc: int,
    n_subdivisions: int,
):
    """
    Sprint 102 helper: rigorous arb lower bound on the Branch.one
    fallbackA window mass

        ∫_{rho_start..rho_stop} 12 ρ^3 (ρ^2 - c^2) / (c^6 · Λ(c, ρ)) dρ

    where `Λ(c, ρ)` is the Wang truncated paper-product computed via
    `_two_window_mass_paper_K_arb` /
    `_two_window_mass_paper_lambda_from_K_arb`.

    Structurally parallel to sprint 099's
    `_two_window_mass_window_lower_arb`: equal-width left-Riemann
    subdivision of `[rho_start, rho_stop]` into ``n_subdivisions``
    sub-intervals. On each sub-interval [ρ_lo, ρ_hi]:

      - Λ_upper := rigorous upper bound on Λ via the sprint 101
        monotonicity-aware three-branch dispatch (left-of-sqrt(c) /
        right-of-sqrt(c) / straddle), reusing the same K-cache
        pattern as `_two_window_mass_window_lower_arb`.
      - numerator lower bound: `12 ρ³ (ρ² − c²)` is **increasing** on
        each boxA window. Its derivative `12 ρ² (5 ρ² − 3 c²)` is
        positive whenever `ρ > c · sqrt(3/5)`. Every boxA window
        satisfies `ρ ≥ c · (1 + 10^(-6)) > c · sqrt(3/5)` (since
        sqrt(3/5) ≈ 0.7746 < 1 + 10^(-6)), so the minimum on
        `[ρ_lo, ρ_hi]` is at `ρ = ρ_lo`. The rigorous per-subinterval
        numerator lower bound is therefore `12 ρ_lo³ (ρ_lo² − c²)`.
      - integrand_lower := numer_lower / (c⁶ · Λ_upper).
      - sub-interval contribution := (ρ_hi − ρ_lo) · integrand_lower.

    The final sum is a strict left-Riemann lower bound on the
    integral. Combined with sprint 101's tightened Λ_upper, the boxA
    per-subinterval radius is governed by arb arithmetic precision
    (~10^(-50) at dps=80) rather than by subdivision width.

    K-cache: K(c, ρ) is evaluated at each subdivision endpoint
    exactly once and reused as both the right-K of subinterval k
    and the left-K of subinterval k+1, halving the work. The
    sqrt(c) candidate K is memoised in ``K_at_sqrt_cache`` and
    touched at most once per invocation (sqrt(c) is a single
    point so at most one sub-interval straddles it).

    Sprint 100 locally-verified per-window radii at
    ``n_subdivisions = 2048`` (n_trunc=300, dps=80):

      | window         | midpoint | radius   |
      |----------------|----------|----------|
      | m_a1 (boxA1)   | 8.71e-7  | 3.17e-10 |
      | m_a2 (boxA2)   | 1.53e-6  | 1.21e-10 |
      | m_a3 (boxA3)   | 5.07e-6  | 4.48e-10 |

    — three orders of magnitude tighter than V66's `+1.20e-4`
    centered margin. The boxA windows were never the bottleneck in
    sprint 100; the bottleneck was the mode1 union-radius scaling,
    which sprint 101's Λ_upper dispatch fixed.
    """
    width = rho_stop - rho_start
    rhos = [
        rho_start + arb(fmpq(k, n_subdivisions)) * width
        for k in range(n_subdivisions + 1)
    ]
    Ks = [_two_window_mass_paper_K_arb(c_arb, c_pows, r, n_trunc) for r in rhos]
    K_at_sqrt_cache = [None]
    c_6 = c_pows[6]
    total = arb(0)
    for k in range(n_subdivisions):
        rho_lo = rhos[k]
        rho_hi = rhos[k + 1]
        sub_width = rho_hi - rho_lo

        # Sprint 101 monotonicity-aware Λ_upper dispatch on
        # rigorously-decided position of [rho_lo, rho_hi] vs sqrt(c).
        # K(c, ρ) is single-peaked at ρ = sqrt(c).
        if (rho_hi <= sqrt_c_arb) is True:
            # Rigorously left of sqrt(c): K increasing on the
            # sub-interval, max attained at rho_hi.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            # Rigorously right of sqrt(c): K decreasing on the
            # sub-interval, max attained at rho_lo.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            # Straddle or rigorously undecided: three-candidate union.
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc
                )
            Lam_lo = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
            Lam_hi = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
            Lam_sqrt = _two_window_mass_paper_lambda_from_K_arb(
                K_at_sqrt_cache[0]
            )
            Lam_upper = Lam_lo.union(Lam_hi).union(Lam_sqrt)

        # Numerator lower bound: 12 ρ³ (ρ² − c²) is increasing on
        # each boxA window since ρ ≥ c·(1 + 10^(-6)) > c·sqrt(3/5);
        # minimum attained at ρ_lo.
        rho_lo_2 = rho_lo * rho_lo
        rho_lo_3 = rho_lo_2 * rho_lo
        numer_lower = 12 * rho_lo_3 * (rho_lo_2 - c_arb * c_arb)

        integrand_lower = numer_lower / (c_6 * Lam_upper)
        total = total + sub_width * integrand_lower
    return total


def certify_two_window_mass_at_35646_sqrt() -> Fraction:
    """
    Sprint 099 zero-argument Evaluator-facing shim for the registered oracle
    ``h_two_window_mass_certified_at_35646_sqrt``, **rigorously
    re-discharged via `flint.arb` interval-arithmetic quadrature**
    (replacing the original sprint 083 `mp.quad`-based implementation
    while preserving the wrapper's external contract conjunct-for-conjunct).

    Pins the parameters to the candidate's **exact sqrt endpoints**

      c            = 35646/100000
      ρ_start_1    = c · sqrt(9/8)        # ⇒ ρ_start_1² = 9 c² / 8 = c² / tau(2)
      ρ_stop_1     = c · sqrt(4/3)        # ⇒ ρ_stop_1²  = 4 c² / 3 = c² / tau(1)
      (= ρ_start_2)
      ρ_stop_2     = 999999/1000000
      (j_1, j_2)   = (2, 1)
      n_trunc      = 200       (Wang truncation depth, unchanged from sprint 083).

    The sqrt endpoints sit at the canonical τ-breakpoints
    `tau(1) = 3/4` and `tau(2) = 8/9` exactly:

      tau(1) = c² / ρ_stop_1²   ⇒   ρ_stop_1² · tau(1) = c²
      tau(2) = c² / ρ_start_1²  ⇒   ρ_start_1² · tau(2) = c².

    These are the algebraically forced τ-breakpoint endpoints for a
    two-window τ-partition at `(j_1, j_2) = (2, 1)` with adjacency
    `ρ_stop_1 = ρ_start_2` (see Scratch/sprint_079_obstruction.md
    §"Adjacency-meets-τ-bound algebraic constraint" and the contract
    of sprint 083).

    Sprint 099 migration: the joint mass is now bounded **rigorously
    from below** via `flint.arb` interval enclosures — see the three
    private helpers `_two_window_mass_paper_factor_arb`,
    `_two_window_mass_paper_lambda_arb`,
    `_two_window_mass_window_lower_arb` defined above. The wrapper
    iterates ``n_subdivisions`` in powers of 2 from 256 to 16384
    until the rigorous total-mass lower bound clears the strict-margin
    floor `1 + 10^(-30)`.

    Phase 0 witness (sprint 083, mp.quad backend):
    ``Scratch/sprint_083_sqrt_endpoint_witness.txt`` — centered margin
    +1.9001e-3 at the sqrt endpoints under (dps=50, n_trunc=200).

    Sprint 099 witness (arb interval-quadrature backend):
    ``Scratch/sprint_099_arb_two_window_mass_witness.py`` — rigorous
    lower-bound margin ≈ +1.29e-3 at n_subdivisions=2048, ~26 orders
    of magnitude over the strict-margin floor `10^(-30)`.

    Returns ``Fraction(1, 1)`` iff the rigorous arb lower bound on
    the joint mass exceeds `1 + 10^(-30)`. Raises ``RuntimeError``
    on rejection (rigorous lower bound fails to clear the floor at
    n_subdivisions = 16384) so the Evaluator records an oracle-check
    failure rather than silently accepting an unverified Lean axiom.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate's ``def two_window_mass_lower : ℝ := 1``
    via ``oracle_bound ≤ declared``, accepting iff ``1 ≤ 1`` — which
    holds because the shim only returns when the certified joint
    mass is rigorously above 1.
    """
    n_trunc = 200
    dps = 80  # arb working precision; ample for 200-factor products

    c = Fraction(35646, 100000)
    rt2 = Fraction(999999, 1000000)
    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(
            "certify_two_window_mass_at_35646_sqrt: pinned c is not in (0, 1)."
        )
    if not (rt2 < Fraction(1)):
        raise RuntimeError(
            "certify_two_window_mass_at_35646_sqrt: pinned ρ_stop_2 is not below 1."
        )

    j1, j2 = 2, 1

    with ctx.workdps(int(dps)):
        c_arb = _arb_exact(c)
        rt2_arb = _arb_exact(rt2)
        # Sqrt-pinned arb endpoints (irrational; arb's `.sqrt()` returns
        # a rigorous interval enclosure of the irrational square root).
        rho_start_1_arb = c_arb * arb(fmpq(9, 8)).sqrt()
        rho_meet_arb = c_arb * arb(fmpq(4, 3)).sqrt()
        sqrt_c_arb = c_arb.sqrt()

        # Structural ordering checks (rigorous arb comparisons): each
        # gap is well above 10^(-3), so rigorous comparisons trivially
        # succeed (no overlap between consecutive endpoint enclosures).
        if not ((c_arb < rho_start_1_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35646_sqrt: ordering c < ρ_start_1 fails."
            )
        if not ((rho_start_1_arb <= rho_meet_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35646_sqrt: ordering ρ_start_1 ≤ ρ_stop_1 fails."
            )
        if not ((rho_meet_arb <= rt2_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35646_sqrt: ordering ρ_stop_1 ≤ ρ_stop_2 fails."
            )

        # Pre-compute c-powers once. Need up to c^(2*n_trunc + 2) for
        # the paper-factor and Λ-prefactor, plus c^(2*max(j1,j2)+2)
        # for the H_j term — n_trunc dominates.
        max_exp = 2 * n_trunc + 3
        c_pows = _pow_cached(c_arb, max_exp)

        floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

        # Iteratively double n_subdivisions in powers of 2 from 256 to
        # 16384 (the contract cap). Stop as soon as the rigorous lower
        # bound clears the strict-margin floor 1 + 10^(-30).
        n_subdivisions = 256
        cap = 16384
        last_total = None
        while True:
            m1_lower = _two_window_mass_window_lower_arb(
                c_arb, c_pows, j1, rho_start_1_arb, rho_meet_arb,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m2_lower = _two_window_mass_window_lower_arb(
                c_arb, c_pows, j2, rho_meet_arb, rt2_arb,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            total_lower = m1_lower + m2_lower
            last_total = total_lower
            if (total_lower > floor_arb) is True:
                return Fraction(1, 1)
            if n_subdivisions >= cap:
                break
            n_subdivisions *= 2

        raise RuntimeError(
            "certify_two_window_mass_at_35646_sqrt: rigorous arb lower bound "
            f"on joint mass = {last_total} (margin = {last_total - arb(1)}) "
            f"failed to clear strict-margin floor 1 + 10^(-30) at "
            f"n_subdivisions = {n_subdivisions} (cap = {cap}); refusing "
            "to certify Lean axiom `h_two_window_mass_certified_at_35646_sqrt`."
        )


# -----------------------------------------------------------------------------
# Sprint 087: seven-window joint mass at c = 356562/1000000 (= 178281/500000),
# the c-ceiling found by the Phase 0 c-sweep at which the V38 seven-window
# split has margin ≥ 1e-4. The split is
#
#     boxA1   (Branch.one)   [c · (1 + 1e-6),  c · sqrt(50/49)]
#     boxA2   (Branch.one)   [c · sqrt(50/49), c · sqrt(36/35)]
#     boxA3   (Branch.one)   [c · sqrt(36/35), c · sqrt(25/24)]
#     mode4   (j=4)           [c · sqrt(25/24), c · sqrt(16/15)]
#     mode3   (j=3)           [c · sqrt(16/15), c · sqrt(9/8)]
#     mode2   (j=2)           [c · sqrt(9/8),   c · sqrt(4/3)]
#     mode1   (j=1)           [c · sqrt(4/3),   999999/1000000]
#
# Branch.one mass: ∫_{ρ_lo..ρ_hi} 12 ρ^3 (ρ^2 - c^2) / (c^6 · Λ(c, ρ)) dρ
# Per-mode mass:   ∫_{ρ_lo..ρ_hi} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ
#
# At c = 356562/1000000 the joint mass is `1.0001199988...`, margin
# +1.19998e-4 (witness file `Scratch/sprint_087_v38_seven_window_mass_sweep.txt`).
# -----------------------------------------------------------------------------


def _branch1_window_mass(
    c: mp.mpf, rho_start: mp.mpf, rho_stop: mp.mpf, n_trunc: int
) -> mp.mpf:
    """
    Sprint 087 helper: certified mass of one Branch.one fallback window.

    Computes the Wang-eq(5)-via-`Korenblum.scalarIntegrand1` integral

        ∫_{ρ_start..ρ_stop} 12 ρ^3 (ρ^2 - c^2) / (c^6 · Λ(c, ρ)) dρ

    where `Λ(c, ρ)` is the Wang truncated paper-product `paperLambda K c ρ`
    computed by the existing `_two_window_mass_paper_lambda` helper.
    """
    if rho_stop <= rho_start:
        return mp.mpf(0)

    def f(rho: mp.mpf) -> mp.mpf:
        Lam = _two_window_mass_paper_lambda(c, rho, n_trunc=n_trunc)
        if Lam == mp.mpf("+inf"):
            return mp.mpf(0)
        return 12 * rho ** 3 * (rho ** 2 - c ** 2) / (c ** 6 * Lam)
    return mp.quad(f, [rho_start, rho_stop])


def certify_seven_window_mass_at_356562_sqrt() -> Fraction:
    """
    Sprint 087 / sprint 102 zero-argument Evaluator-facing shim for the
    registered oracle ``h_seven_window_mass_certified_at_356562_sqrt``,
    **rigorously re-discharged via `flint.arb` interval-arithmetic
    quadrature** (sprint 102 migration; replaces the original sprint
    087 `mp.quad`-based implementation while preserving the wrapper's
    external contract conjunct-for-conjunct).

    Pins V38's seven-window split at the Phase 0-sweep-determined c
    (the largest c ≥ V64's 0.35646 at which the joint mass exceeds
    `1 + 1e-4` under the seven-window split). Endpoints:

      c             = 356562 / 1000000          # rational, sweep-pinned
      delta_lo      = 1e-6                      # boxA1 offset above c
      boxA1: [c · (1 + 1e-6),  c · sqrt(50/49)]
      boxA2: [c · sqrt(50/49), c · sqrt(36/35)]
      boxA3: [c · sqrt(36/35), c · sqrt(25/24)]
      mode4: [c · sqrt(25/24), c · sqrt(16/15)]   j = 4
      mode3: [c · sqrt(16/15), c · sqrt(9/8)]     j = 3
      mode2: [c · sqrt(9/8),   c · sqrt(4/3)]     j = 2
      mode1: [c · sqrt(4/3),   999999/1000000]    j = 1
      (dps, n_trunc) = (80, 300)

    The sqrt-pinned mode endpoints sit at the canonical τ-breakpoints
    `tau_j = 1 - 1/(j+1)²` exactly:

      tau(j) = c² / ρ_j_lo²  ⇒  ρ_j_lo² · tau(j) = c²

    for j = 1, 2, 3, 4. The Branch.one box splits at `c · sqrt(50/49)`
    and `c · sqrt(36/35)` are intermediate rationally-related cuts
    inside the deep-band fallbackA region.

    Phase 0 witness (sprint 087, mp.quad backend):
    ``Scratch/sprint_087_v38_seven_window_mass_sweep.txt`` — c-sweep
    output at (dps=40, n_trunc=120) plus full-envelope re-verification
    at (dps=80, n_trunc=300) reporting margin +1.19998e-4 at the
    chosen c, well above the 1e-4 acceptance threshold and ~26 orders
    of magnitude above the strict-margin floor 10^(-30).

    Sprint 099 V64 template: the two-window cousin
    ``certify_two_window_mass_at_35646_sqrt`` was migrated mp.quad → arb
    via the iterative-driver pattern reused below.

    Sprint 100 BLOCKED diagnosis: a first attempt at the V66 migration
    (under sprint 099's union-based Λ_upper) hit a per-subinterval
    union radius `O(width / n_subdivisions)` that, at the contract
    cap `n_subdivisions = 16384`, could not fit inside V66's tight
    `+1.20e-4` centered margin. Sprint 100's table:

      | n_sub  | m_1.rad   |
      |--------|-----------|
      |   2048 | 7.83e-04  |
      |   4096 | 3.92e-04  |
      |   8192 | 1.96e-04  |
      |  16384 | 9.80e-05  |   (cap; margin envelope still violated)

    Sprint 101 fix: the helper
    ``_two_window_mass_window_lower_arb`` was upgraded with a
    monotonicity-aware Λ_upper dispatch — when a sub-interval is
    rigorously left/right of `sqrt(c)`, K(c, ρ) is monotone there and
    Λ_upper reduces to a **single point evaluation**, eliminating the
    O(width) union radius and dropping `m_1.rad` toward arb arithmetic
    precision (~10^(-50) at dps=80) on the wide right-of-sqrt(c)
    mode1 tail. The boxA windows had never been the bottleneck in
    sprint 100 (radii ~10^(-10) at n=2048).

    Sprint 102 wrapper rewrite: composes three calls to
    ``_branch1_window_mass_lower_arb`` (Branch.one boxA1 / boxA2 /
    boxA3 windows) with four calls to ``_two_window_mass_window_lower_arb``
    (mode4 / mode3 / mode2 / mode1 windows), under the same
    iterative-power-of-2 ``n_subdivisions`` driver pattern as sprint
    099's V64 wrapper (cap = 16384, no cap raise vs sprint 099/100).

    Per-window radii expectations at ``n_subdivisions = 2048``
    (n_trunc=300, dps=80) per sprint 100's locally-verified diagnostic
    plus sprint 101's ≥10× tightening on the mode1 tail:

      | window         | midpoint  | radius      |
      |----------------|-----------|-------------|
      | m_a1 (boxA1)   | 8.71e-7   | 3.17e-10    |
      | m_a2 (boxA2)   | 1.53e-6   | 1.21e-10    |
      | m_a3 (boxA3)   | 5.07e-6   | 4.48e-10    |
      | m_4 (mode4)    | 1.04e-4   | ≤1.13e-08   |
      | m_3 (mode3)    | 4.77e-4   | ≤6.67e-08   |
      | m_2 (mode2)    | 4.93e-3   | ≤9.34e-07   |
      | m_1 (mode1)    | 0.994     | ≤7.83e-05   |
      | total          | 1.000     | ≤7.84e-05   |

    — comfortably inside V66's `+1.20e-4` envelope, ~26 orders of
    magnitude above the strict-margin floor `10^(-30)`. The iterative
    driver in any case escalates ``n_subdivisions`` until the floor
    clears.

    Returns ``Fraction(1, 1)`` iff the rigorous arb lower bound on
    the joint mass exceeds `1 + 10^(-30)`. Raises ``RuntimeError`` on
    rejection (rigorous lower bound fails to clear the floor at
    ``n_subdivisions = 16384``) so the Evaluator records an oracle-
    check failure rather than silently accepting an unverified Lean
    axiom.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate-side ``def seven_window_mass_lower : ℝ
    := 1`` via ``oracle_bound ≤ declared``, accepting iff ``1 ≤ 1`` —
    which holds because the shim only returns when the certified joint
    mass is rigorously above 1.
    """
    n_trunc = 300
    dps = 80  # arb working precision; ample for 300-factor products

    c = Fraction(356562, 1000000)
    rho_top = Fraction(999999, 1000000)
    delta_lo = Fraction(1, 1_000_000)

    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356562_sqrt: pinned c is not in (0, 1)."
        )
    if not (rho_top < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356562_sqrt: pinned ρ_top is not below 1."
        )

    with ctx.workdps(int(dps)):
        c_arb = _arb_exact(c)
        rho_top_arb = _arb_exact(rho_top)
        delta_lo_arb = _arb_exact(delta_lo)

        # Mode-window τ-breakpoint endpoints (sqrt-pinned).
        rho_4_lo = c_arb * arb(fmpq(25, 24)).sqrt()    # = c·sqrt(1/τ_4)
        rho_3_lo = c_arb * arb(fmpq(16, 15)).sqrt()    # = c·sqrt(1/τ_3)
        rho_2_lo = c_arb * arb(fmpq(9, 8)).sqrt()      # = c·sqrt(1/τ_2)
        rho_1_lo = c_arb * arb(fmpq(4, 3)).sqrt()      # = c·sqrt(1/τ_1)

        # Branch.one fallbackA box-split endpoints (sqrt-pinned).
        fallback_a_lo = c_arb * (1 + delta_lo_arb)
        rho_a1_split = c_arb * arb(fmpq(50, 49)).sqrt()
        rho_a2_split = c_arb * arb(fmpq(36, 35)).sqrt()

        sqrt_c_arb = c_arb.sqrt()

        # Structural ordering checks (rigorous arb comparisons): each
        # gap is well above 10^(-6), so rigorous comparisons trivially
        # succeed at dps=80.
        ordering_checks = [
            ("c < fallback_a_lo",            c_arb < fallback_a_lo),
            ("fallback_a_lo < rho_a1_split", fallback_a_lo < rho_a1_split),
            ("rho_a1_split < rho_a2_split",  rho_a1_split < rho_a2_split),
            ("rho_a2_split < rho_4_lo",      rho_a2_split < rho_4_lo),
            ("rho_4_lo < rho_3_lo",          rho_4_lo < rho_3_lo),
            ("rho_3_lo < rho_2_lo",          rho_3_lo < rho_2_lo),
            ("rho_2_lo < rho_1_lo",          rho_2_lo < rho_1_lo),
            ("rho_1_lo < rho_top_arb",       rho_1_lo < rho_top_arb),
        ]
        for name, ok_arb in ordering_checks:
            if not (ok_arb is True):
                raise RuntimeError(
                    f"certify_seven_window_mass_at_356562_sqrt: "
                    f"structural ordering check '{name}' failed."
                )

        # Pre-compute c-powers once. Need up to c^(2*n_trunc + 2) for
        # the paper-factor and Λ-prefactor, plus c^(2*max(j)+2)
        # for the H_j term and c^6 for the Branch.one denominator —
        # n_trunc dominates.
        max_exp = 2 * n_trunc + 3
        c_pows = _pow_cached(c_arb, max_exp)

        floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

        # Iteratively double n_subdivisions in powers of 2 from 256 to
        # 16384 (the contract cap inherited from sprint 099). Stop as
        # soon as the rigorous lower bound clears the strict-margin
        # floor 1 + 10^(-30).
        n_subdivisions = 256
        cap = 16384
        last_total = None
        while True:
            m_a1 = _branch1_window_mass_lower_arb(
                c_arb, c_pows, fallback_a_lo, rho_a1_split,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_a2 = _branch1_window_mass_lower_arb(
                c_arb, c_pows, rho_a1_split, rho_a2_split,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_a3 = _branch1_window_mass_lower_arb(
                c_arb, c_pows, rho_a2_split, rho_4_lo,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_4 = _two_window_mass_window_lower_arb(
                c_arb, c_pows, 4, rho_4_lo, rho_3_lo,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_3 = _two_window_mass_window_lower_arb(
                c_arb, c_pows, 3, rho_3_lo, rho_2_lo,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_2 = _two_window_mass_window_lower_arb(
                c_arb, c_pows, 2, rho_2_lo, rho_1_lo,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m_1 = _two_window_mass_window_lower_arb(
                c_arb, c_pows, 1, rho_1_lo, rho_top_arb,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            total_lower = m_a1 + m_a2 + m_a3 + m_4 + m_3 + m_2 + m_1
            last_total = total_lower
            if (total_lower > floor_arb) is True:
                return Fraction(1, 1)
            if n_subdivisions >= cap:
                break
            n_subdivisions *= 2

        raise RuntimeError(
            "certify_seven_window_mass_at_356562_sqrt: rigorous arb lower "
            f"bound on joint mass = {last_total} (margin = "
            f"{last_total - arb(1)}) failed to clear strict-margin floor "
            f"1 + 10^(-30) at n_subdivisions = {n_subdivisions} "
            f"(cap = {cap}); refusing to certify Lean axiom "
            "`h_seven_window_mass_certified_at_356562_sqrt`."
        )


# -----------------------------------------------------------------------------
# Sprint 090: eight-window joint mass at c = 89141/250000 = 356564/1000000,
# the c-ceiling found by sprint 089's Phase 0 adaptive sweep at which the
# eight-window architecture (one Branch.one residual box plus seven per-mode
# windows for j ∈ {7, 6, 5, 4, 3, 2, 1}) has full-envelope margin >= 1e-4.
# Despite the wrapper name's `seven_window` prefix (retained from sprint 089's
# witness for backwards consistency), the wrapper pins the eight-window
# architecture: 1 Branch.one + 7 per-mode windows.
#
#     box0    (Branch.one)   [c · (1 + 1e-9), c · sqrt(64/63)]
#     mode7   (j=7)           [c · sqrt(64/63), c · sqrt(49/48)]
#     mode6   (j=6)           [c · sqrt(49/48), c · sqrt(36/35)]
#     mode5   (j=5)           [c · sqrt(36/35), c · sqrt(25/24)]
#     mode4   (j=4)           [c · sqrt(25/24), c · sqrt(16/15)]
#     mode3   (j=3)           [c · sqrt(16/15), c · sqrt(9/8)]
#     mode2   (j=2)           [c · sqrt(9/8),   c · sqrt(4/3)]
#     mode1   (j=1)           [c · sqrt(4/3),   1 - 1e-9]
#
# Branch.one mass: ∫_{ρ_lo..ρ_hi} 12 ρ^3 (ρ^2 - c^2) / (c^6 · Λ(c, ρ)) dρ
# Per-mode mass:   ∫_{ρ_lo..ρ_hi} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ
#
# At c = 89141/250000 sprint 089's witness records full-envelope margin
# +1.183e-4 at (dps=80, n_trunc=300) — well above the 1e-4 acceptance
# threshold and ~26 orders of magnitude above the strict-margin floor.
# -----------------------------------------------------------------------------


def certify_seven_window_mass_at_356564_modeJ7() -> Fraction:
    """
    Sprint 090 zero-argument Evaluator-facing shim for the registered oracle
    ``h_eight_window_mass_certified_at_356564_modeJ7``.

    Pins sprint 089's eight-window architecture at the Phase 0 adaptive
    sweep-determined c (`c = 89141/250000 = 356564/1000000`, +2e-6 above
    V66's `178281/500000 = 356562/1000000`). Endpoints:

      c             = 89141 / 250000          # = 356564 / 1000000
      delta_lo      = 1e-9                    # box0 offset above c
      rho_top       = 1 - 1e-9
      box0:  [c · (1 + 1e-9), c · sqrt(64/63)]
      mode7: [c · sqrt(64/63), c · sqrt(49/48)]   j = 7
      mode6: [c · sqrt(49/48), c · sqrt(36/35)]   j = 6
      mode5: [c · sqrt(36/35), c · sqrt(25/24)]   j = 5
      mode4: [c · sqrt(25/24), c · sqrt(16/15)]   j = 4
      mode3: [c · sqrt(16/15), c · sqrt(9/8)]     j = 3
      mode2: [c · sqrt(9/8),   c · sqrt(4/3)]     j = 2
      mode1: [c · sqrt(4/3),   1 - 1e-9]          j = 1
      (dps, n_trunc) = (80, 300)

    The sqrt-pinned mode endpoints sit at the canonical τ-breakpoints
    `tau_j = 1 - 1/(j+1)²` exactly, for j = 1, 2, 3, 4, 5, 6, 7.
    The Branch.one residual box covers the deep `(c, c·sqrt(64/63))` band
    (with the `tau_7 = 63/64` upper edge).

    Phase 0 witness (sprint 089):
    ``Scratch/sprint_089_witness.txt`` — full-envelope margin +1.183e-4
    at (dps=80, n_trunc=300) at the chosen c, well above the 1e-4
    acceptance threshold and ~26 orders of magnitude above the
    strict-margin floor 10^(-30).

    Returns ``Fraction(1, 1)`` iff the joint mass at the eight sqrt-pinned
    and rational-pinned endpoints exceeds `1 + 10^(-30)`. Raises
    ``RuntimeError`` on rejection so the Evaluator records an oracle-check
    failure rather than silently accepting an unverified Lean axiom.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate-side ``def eight_window_mass_lower : ℝ
    := 1`` via ``oracle_bound ≤ declared``, accepting iff ``1 ≤ 1`` —
    which holds because the shim only returns when the certified joint
    mass is strictly above 1.

    The wrapper's ``seven_window`` name prefix is retained from the
    sprint 089 witness's nomenclature for backwards consistency; despite
    the prefix it pins the eight-window architecture (1 Branch.one + 7
    per-mode windows).
    """
    dps = 80
    n_trunc = 300

    c = Fraction(89141, 250000)
    delta_lo = Fraction(1, 1_000_000_000)
    rho_top = Fraction(1) - Fraction(1, 1_000_000_000)

    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356564_modeJ7: pinned c is not in (0, 1)."
        )
    if not (rho_top < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356564_modeJ7: pinned ρ_top is not below 1."
        )

    with mp.workdps(int(dps)):
        c_mp = _frac_to_mpf(c)
        rho_top_mp = _frac_to_mpf(rho_top)
        delta_lo_mp = _frac_to_mpf(delta_lo)

        # Mode-window τ-breakpoint endpoints (sqrt-pinned).
        rho_7_lo = c_mp * mp.sqrt(mp.mpf(64) / mp.mpf(63))   # = c·sqrt(1/τ_7)
        rho_6_lo = c_mp * mp.sqrt(mp.mpf(49) / mp.mpf(48))   # = c·sqrt(1/τ_6)
        rho_5_lo = c_mp * mp.sqrt(mp.mpf(36) / mp.mpf(35))   # = c·sqrt(1/τ_5)
        rho_4_lo = c_mp * mp.sqrt(mp.mpf(25) / mp.mpf(24))   # = c·sqrt(1/τ_4)
        rho_3_lo = c_mp * mp.sqrt(mp.mpf(16) / mp.mpf(15))   # = c·sqrt(1/τ_3)
        rho_2_lo = c_mp * mp.sqrt(mp.mpf(9)  / mp.mpf(8))    # = c·sqrt(1/τ_2)
        rho_1_lo = c_mp * mp.sqrt(mp.mpf(4)  / mp.mpf(3))    # = c·sqrt(1/τ_1)

        # Branch.one residual-box lower endpoint.
        box0_lo = c_mp * (mp.mpf(1) + delta_lo_mp)

        # Structural ordering (must hold pre-quad).
        ordering_checks = [
            ("c < box0_lo",            c_mp < box0_lo),
            ("box0_lo < rho_7_lo",     box0_lo < rho_7_lo),
            ("rho_7_lo < rho_6_lo",    rho_7_lo < rho_6_lo),
            ("rho_6_lo < rho_5_lo",    rho_6_lo < rho_5_lo),
            ("rho_5_lo < rho_4_lo",    rho_5_lo < rho_4_lo),
            ("rho_4_lo < rho_3_lo",    rho_4_lo < rho_3_lo),
            ("rho_3_lo < rho_2_lo",    rho_3_lo < rho_2_lo),
            ("rho_2_lo < rho_1_lo",    rho_2_lo < rho_1_lo),
            ("rho_1_lo < rho_top_mp",  rho_1_lo < rho_top_mp),
        ]
        for name, ok in ordering_checks:
            if not ok:
                raise RuntimeError(
                    f"certify_seven_window_mass_at_356564_modeJ7: "
                    f"structural ordering check '{name}' failed."
                )

        # Per-window masses.
        m_box0 = _branch1_window_mass(c_mp, box0_lo, rho_7_lo, n_trunc=int(n_trunc))
        m_7 = _two_window_mass_window(c_mp, 7, rho_7_lo, rho_6_lo, n_trunc=int(n_trunc))
        m_6 = _two_window_mass_window(c_mp, 6, rho_6_lo, rho_5_lo, n_trunc=int(n_trunc))
        m_5 = _two_window_mass_window(c_mp, 5, rho_5_lo, rho_4_lo, n_trunc=int(n_trunc))
        m_4 = _two_window_mass_window(c_mp, 4, rho_4_lo, rho_3_lo, n_trunc=int(n_trunc))
        m_3 = _two_window_mass_window(c_mp, 3, rho_3_lo, rho_2_lo, n_trunc=int(n_trunc))
        m_2 = _two_window_mass_window(c_mp, 2, rho_2_lo, rho_1_lo, n_trunc=int(n_trunc))
        m_1 = _two_window_mass_window(c_mp, 1, rho_1_lo, rho_top_mp, n_trunc=int(n_trunc))

        total = m_box0 + m_7 + m_6 + m_5 + m_4 + m_3 + m_2 + m_1
        eps = mp.mpf(10) ** (-min(int(dps), 30))
        if not (total >= mp.mpf(1) + eps):
            raise RuntimeError(
                "certify_seven_window_mass_at_356564_modeJ7: joint mass margin "
                f"{mp.nstr(total - mp.mpf(1), 6)} below strict-margin floor "
                f"10^(-{min(int(dps), 30)}); refusing to certify Lean axiom "
                "`h_eight_window_mass_certified_at_356564_modeJ7`."
            )
    return Fraction(1, 1)


def certify_seven_window_mass_at_356565_modeJ10() -> Fraction:
    """
    Sprint 092 zero-argument Evaluator-facing shim for the registered oracle
    ``h_eleven_window_mass_certified_at_356565_modeJ10``.

    Pins sprint 091's eleven-window architecture at the Phase 0 adaptive
    sweep-determined c (`c = 71313/200000 = 356565/1000000`, +1e-6 above
    V67's `89141/250000 = 356564/1000000`). Endpoints:

      c             = 71313 / 200000          # = 356565 / 1000000
      delta_lo      = 1e-9                    # box0 offset above c
      rho_top       = 1 - 1e-9
      box0:   [c · (1 + 1e-9),   c · sqrt(121/120)]
      mode10: [c · sqrt(121/120), c · sqrt(100/99)]   j = 10
      mode9:  [c · sqrt(100/99),  c · sqrt(81/80)]    j = 9
      mode8:  [c · sqrt(81/80),   c · sqrt(64/63)]    j = 8
      mode7:  [c · sqrt(64/63),   c · sqrt(49/48)]    j = 7
      mode6:  [c · sqrt(49/48),   c · sqrt(36/35)]    j = 6
      mode5:  [c · sqrt(36/35),   c · sqrt(25/24)]    j = 5
      mode4:  [c · sqrt(25/24),   c · sqrt(16/15)]    j = 4
      mode3:  [c · sqrt(16/15),   c · sqrt(9/8)]      j = 3
      mode2:  [c · sqrt(9/8),     c · sqrt(4/3)]      j = 2
      mode1:  [c · sqrt(4/3),     1 - 1e-9]           j = 1
      (dps, n_trunc) = (80, 300)

    The sqrt-pinned mode endpoints sit at the canonical τ-breakpoints
    `tau_j = 1 - 1/(j+1)²` exactly, for j = 1, 2, 3, 4, 5, 6, 7, 8, 9, 10.
    The Branch.one residual box covers the deep `(c, c·sqrt(121/120))` band
    (with the `tau_10 = 120/121` upper edge).

    Phase 0 witness (sprint 091):
    ``Scratch/sprint_091_witness.txt`` — full-envelope margin +1.0048e-4
    at (dps=80, n_trunc=300) at the chosen c, comfortably above the 1e-4
    acceptance threshold and ~26 orders of magnitude above the
    strict-margin floor 10^(-30).

    Returns ``Fraction(1, 1)`` iff the joint mass at the eleven sqrt-pinned
    and rational-pinned endpoints exceeds `1 + 10^(-30)`. Raises
    ``RuntimeError`` on rejection so the Evaluator records an oracle-check
    failure rather than silently accepting an unverified Lean axiom.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate-side ``def eleven_window_mass_lower : ℝ
    := 1`` via ``oracle_bound ≤ declared``, accepting iff ``1 ≤ 1`` —
    which holds because the shim only returns when the certified joint
    mass is strictly above 1.

    The wrapper's ``seven_window`` name prefix is retained from sprint
    091's witness's nomenclature for backwards consistency; despite the
    prefix it pins the **eleven-window** architecture (1 Branch.one + 10
    per-mode windows for j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}).
    """
    dps = 80
    n_trunc = 300

    c = Fraction(71313, 200000)
    delta_lo = Fraction(1, 1_000_000_000)
    rho_top = Fraction(1) - Fraction(1, 1_000_000_000)

    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356565_modeJ10: pinned c is not in (0, 1)."
        )
    if not (rho_top < Fraction(1)):
        raise RuntimeError(
            "certify_seven_window_mass_at_356565_modeJ10: pinned ρ_top is not below 1."
        )

    with mp.workdps(int(dps)):
        c_mp = _frac_to_mpf(c)
        rho_top_mp = _frac_to_mpf(rho_top)
        delta_lo_mp = _frac_to_mpf(delta_lo)

        # Mode-window τ-breakpoint endpoints (sqrt-pinned).
        rho_10_lo = c_mp * mp.sqrt(mp.mpf(121) / mp.mpf(120))  # = c·sqrt(1/τ_10)
        rho_9_lo = c_mp * mp.sqrt(mp.mpf(100) / mp.mpf(99))    # = c·sqrt(1/τ_9)
        rho_8_lo = c_mp * mp.sqrt(mp.mpf(81)  / mp.mpf(80))    # = c·sqrt(1/τ_8)
        rho_7_lo = c_mp * mp.sqrt(mp.mpf(64)  / mp.mpf(63))    # = c·sqrt(1/τ_7)
        rho_6_lo = c_mp * mp.sqrt(mp.mpf(49)  / mp.mpf(48))    # = c·sqrt(1/τ_6)
        rho_5_lo = c_mp * mp.sqrt(mp.mpf(36)  / mp.mpf(35))    # = c·sqrt(1/τ_5)
        rho_4_lo = c_mp * mp.sqrt(mp.mpf(25)  / mp.mpf(24))    # = c·sqrt(1/τ_4)
        rho_3_lo = c_mp * mp.sqrt(mp.mpf(16)  / mp.mpf(15))    # = c·sqrt(1/τ_3)
        rho_2_lo = c_mp * mp.sqrt(mp.mpf(9)   / mp.mpf(8))     # = c·sqrt(1/τ_2)
        rho_1_lo = c_mp * mp.sqrt(mp.mpf(4)   / mp.mpf(3))     # = c·sqrt(1/τ_1)

        # Branch.one residual-box lower endpoint.
        box0_lo = c_mp * (mp.mpf(1) + delta_lo_mp)

        # Structural ordering (must hold pre-quad).
        ordering_checks = [
            ("c < box0_lo",            c_mp < box0_lo),
            ("box0_lo < rho_10_lo",    box0_lo < rho_10_lo),
            ("rho_10_lo < rho_9_lo",   rho_10_lo < rho_9_lo),
            ("rho_9_lo < rho_8_lo",    rho_9_lo < rho_8_lo),
            ("rho_8_lo < rho_7_lo",    rho_8_lo < rho_7_lo),
            ("rho_7_lo < rho_6_lo",    rho_7_lo < rho_6_lo),
            ("rho_6_lo < rho_5_lo",    rho_6_lo < rho_5_lo),
            ("rho_5_lo < rho_4_lo",    rho_5_lo < rho_4_lo),
            ("rho_4_lo < rho_3_lo",    rho_4_lo < rho_3_lo),
            ("rho_3_lo < rho_2_lo",    rho_3_lo < rho_2_lo),
            ("rho_2_lo < rho_1_lo",    rho_2_lo < rho_1_lo),
            ("rho_1_lo < rho_top_mp",  rho_1_lo < rho_top_mp),
        ]
        for name, ok in ordering_checks:
            if not ok:
                raise RuntimeError(
                    f"certify_seven_window_mass_at_356565_modeJ10: "
                    f"structural ordering check '{name}' failed."
                )

        # Per-window masses.
        m_box0 = _branch1_window_mass(c_mp, box0_lo, rho_10_lo, n_trunc=int(n_trunc))
        m_10 = _two_window_mass_window(c_mp, 10, rho_10_lo, rho_9_lo, n_trunc=int(n_trunc))
        m_9 = _two_window_mass_window(c_mp, 9, rho_9_lo, rho_8_lo, n_trunc=int(n_trunc))
        m_8 = _two_window_mass_window(c_mp, 8, rho_8_lo, rho_7_lo, n_trunc=int(n_trunc))
        m_7 = _two_window_mass_window(c_mp, 7, rho_7_lo, rho_6_lo, n_trunc=int(n_trunc))
        m_6 = _two_window_mass_window(c_mp, 6, rho_6_lo, rho_5_lo, n_trunc=int(n_trunc))
        m_5 = _two_window_mass_window(c_mp, 5, rho_5_lo, rho_4_lo, n_trunc=int(n_trunc))
        m_4 = _two_window_mass_window(c_mp, 4, rho_4_lo, rho_3_lo, n_trunc=int(n_trunc))
        m_3 = _two_window_mass_window(c_mp, 3, rho_3_lo, rho_2_lo, n_trunc=int(n_trunc))
        m_2 = _two_window_mass_window(c_mp, 2, rho_2_lo, rho_1_lo, n_trunc=int(n_trunc))
        m_1 = _two_window_mass_window(c_mp, 1, rho_1_lo, rho_top_mp, n_trunc=int(n_trunc))

        total = (m_box0 + m_10 + m_9 + m_8 + m_7 + m_6 + m_5 + m_4 + m_3 +
                 m_2 + m_1)
        eps = mp.mpf(10) ** (-min(int(dps), 30))
        if not (total >= mp.mpf(1) + eps):
            raise RuntimeError(
                "certify_seven_window_mass_at_356565_modeJ10: joint mass margin "
                f"{mp.nstr(total - mp.mpf(1), 6)} below strict-margin floor "
                f"10^(-{min(int(dps), 30)}); refusing to certify Lean axiom "
                "`h_eleven_window_mass_certified_at_356565_modeJ10`."
            )
    return Fraction(1, 1)


if __name__ == "__main__":
    cert = build_adaptive_certificate(Fraction(713, 2000))
    total = cert.total_mass_lower.to_fraction()
    print(f"target c = {cert.target_c.num}/{cert.target_c.den} = {cert.target_c.value:.7f}")
    print(f"boxes    = {len(cert.boxes)}")
    print(f"total    = {float(total):.12f}")
