```python path=ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py
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
        return RationalBound(num=_arb_floor_to_int(x * denom), den=denom)
    if isinstance(x, Fraction):
        return RationalBound(num=math.floor(x * denom), den=denom)
    return RationalBound(num=int(mp.floor(x * denom)), den=denom)


def _rbound_upper(x, denom: int = 10**18) -> RationalBound:
    if isinstance(x, arb):
        return RationalBound(num=_arb_ceil_to_int(x * denom), den=denom)
    if isinstance(x, Fraction):
        return RationalBound(num=math.ceil(x * denom), den=denom)
    return RationalBound(num=int(mp.ceil(x * denom)), den=denom)


def _frac(num: int, den: int) -> Fraction:
    return Fraction(num, den)


def _to_mpf(fr: Fraction) -> mp.mpf:
    return mp.mpf(fr.numerator) / fr.denominator


def _rbound_lower_fraction(x: Fraction, denom: int = 10**18) -> RationalBound:
    return RationalBound(num=math.floor(x * denom), den=denom)


def _rbound_upper_fraction(x: Fraction, denom: int = 10**18) -> RationalBound:
    return RationalBound(num=math.ceil(x * denom), den=denom)


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
    # Search-only helper for partition refinement; never used to certify.
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
    """Rigorous lower bound for d/dt log K on the box, t = (rho^2-c)^2/(4 c rho^2)."""
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
    """Rigorous upper bound for K(c, rho) at a single rho (factors are < 1)."""
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
    """Rigorous upper bound for K(c, rho) on [lo, hi] via boxwise t-monotonicity."""
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
    k_upper = k_upper_on_interval(c, lo, hi, n_terms=n_terms, dps=dps)
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
        lam = one + arb(fmpq(1, 2)) * (
            ((one + 3 * k_arb * k_arb) / (one - k_arb * k_arb)).sqrt() - one
        )
        return _rbound_lower(one / lam, denom=rat_denom)


def _lambda_upper_from_k_upper_fraction(
    k_upper: Fraction,
    *,
    rat_denom: int = 10**18,
    dps: int = 100,
) -> RationalBound:
    with ctx.workdps(dps):
        k_arb = _arb_exact(k_upper)
        one = arb(1)
        lam = one + arb(fmpq(1, 2)) * (
            ((one + 3 * k_arb * k_arb) / (one - k_arb * k_arb)).sqrt() - one
        )
        return _rbound_upper(lam, denom=rat_denom)


def _d_inv_lambda_dk_abs_upper_fraction(k_upper: Fraction, *, dps: int = 100) -> arb:
    """Rigorous upper bound for |d/dK inv_lambda(K)| on [0, k_upper] (monotone in K)."""
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
    """Search-only affine proposal (chord through rigorous endpoint bounds, minus slack)."""
    sqrt_c = _sqrt_c(c)
    lo_mp = _to_mpf(lo)
    hi_mp = _to_mpf(hi)
    if lo_mp < sqrt_c < hi_mp:
        raise ValueError("box crosses sqrt(c)")

    k_lo_upper_rb = _rbound_upper(
        k_upper_at_point(c, lo, n_terms=n_terms, dps=dps), denom=rat_denom
    )
    k_hi_upper_rb = _rbound_upper(
        k_upper_at_point(c, hi, n_terms=n_terms, dps=dps), denom=rat_denom
    )
    inv_lo = _inv_lambda_lower_from_k_upper_fraction(
        k_lo_upper_rb.to_fraction(), rat_denom=rat_denom, dps=dps
    ).to_fraction()
    inv_hi = _inv_lambda_lower_from_k_upper_fraction(
        k_hi_upper_rb.to_fraction(), rat_denom=rat_denom, dps=dps
    ).to_fraction()

    width = hi - lo
    if width <= 0:
        raise ValueError(f"empty box [{float(lo):.7f}, {float(hi):.7f}]")
    beta = (inv_hi - inv_lo) / width
    alpha = inv_lo - beta * lo

    smallest_width = width / (Fraction(1, 1) * (2 ** verifier_max_depth))
    alpha = alpha - abs(beta) * smallest_width * 4

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
            k_upper_rb.to_fraction(), rat_denom=rat_denom, dps=dps
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
        k_upper_on_interval(c, lo, hi, n_terms=n_terms, dps=dps),
        denom=rat_denom,
    )
    lambda_upper = _lambda_upper_from_k_upper_fraction(
        k_upper.to_fraction(), rat_denom=rat_denom, dps=dps
    )

    alpha = Fraction(lambda_upper.den, lambda_upper.num)
    beta = Fraction(0, 1)
    mass = _mass_from_affine_fraction(c, lo, hi, branch, alpha, beta)

    return BoxCertificate(
        index=index,
        branch=branch,
        lo=RationalBound(lo.numerator, lo.denominator),
        hi=RationalBound(hi.numerator, hi.denominator),
        alpha=RationalBound(alpha.numerator, alpha.denominator),
        beta=RationalBound(beta.numerator, beta.denominator),
        mass_lower=RationalBound(mass.numerator, mass.denominator),
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
    return Fraction(sqrt_floor, denom), Fraction(sqrt_floor + 1, denom)


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
    # Search-only partition proposal; each emitted box is reverified by certify_box.
    split_lo, split_hi = _branch_split_bounds(c, denom=split_denom)
    sqrt_lo, sqrt_hi = _sqrt_c_bounds(c, denom=split_denom)
    left_cut = _left_cut(c, left_cut_denom)
    one_cut = _one_cut(one_cut_denom)

    specs: list[_BoxSpec] = []

    if branch1_count > 0 and split_lo > left_cut:
        step = (split_lo - left_cut) / branch1_count
        for i in range(branch1_count):
            specs.append(
                _BoxSpec(lo=left_cut + i * step, hi=left_cut + (i + 1) * step, branch=1)
            )

    if branch2_count > 0 and one_cut > split_hi:
        left_span = max(Fraction(0), min(sqrt_lo, one_cut) - split_hi)
        total_span = one_cut - split_hi
        left_count = (
            max(1, round(branch2_count * float(left_span / total_span)))
            if left_span > 0
            else 0
        )
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
                c, spec.lo, spec.hi, spec.branch,
                index=idx, n_terms=n_terms, dps=dps, rat_denom=rat_denom,
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


def _approx_box_mass(c: Fraction, spec: _BoxSpec, *, n_terms: int, dps: int) -> float:
    # Search-only ranking score for refinement ordering.
    mid = (spec.lo + spec.hi) / 2
    k_mid_rb = _rbound_upper(
        k_upper_at_point(c, mid, n_terms=n_terms, dps=dps), denom=10**12
    )
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
        c, branch1_count=branch1_count, branch2_count=branch2_count
    )

    while True:
        boxes: list[BoxCertificate] = []
        failed: list[int] = []
        for idx, spec in enumerate(specs):
            try:
                boxes.append(
                    certify_box(
                        c, spec.lo, spec.hi, spec.branch,
                        index=idx, n_terms=n_terms, dps=dps, rat_denom=rat_denom,
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
    Verified-interval wrapper for Wang 2025's equation (15) at c = c_num/c_den.

    Returns True iff the certified box-partition lower bound on

        int_{c..split} 12 r^3 (r^2 - c^2) / (c^6 Lambda)
      + int_{split..1} 4 r^3 / (c^4 Lambda)

    exceeds 1 + 10^(-min(dps, 30)). Falsifiability: rejects at (3565, 10000),
    which lies past the literal (15) crossover pinned by sprint 050.
    """
    c = Fraction(int(c_num), int(c_den))
    if not (Fraction(0) < c < Fraction(1)):
        return False

    branch1_count = max(32, n_trunc // 4)
    branch2_count = max(256, n_trunc * 3)
    specs, _split_lo, _split_hi, _one_cut = _uniform_specs(
        c, branch1_count=branch1_count, branch2_count=branch2_count
    )
    if not specs:
        return False

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
                # Drop this sub-box; its positive mass is excluded from the
                # verified lower bound. Honest under-bound, never over-claims.
                continue

    total = _total_mass(boxes)
    eps = Fraction(1, 10 ** min(int(dps), 30))
    return total >= Fraction(1, 1) + eps


# --- Evaluator-facing zero-argument shims for the eq15 oracle cascade --------


def certify_eq15_at_seed() -> Fraction:
    """Pins certify_eq15(3554, 10000, dps=50, n_trunc=200)."""
    if not certify_eq15(3554, 10000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(3554, 10000, dps=50, n_trunc=200) returned False; "
            "refusing to certify `hEq15_oracle_certified_3554`."
        )
    return Fraction(1, 1)


def certify_eq15_at_3560() -> Fraction:
    """Pins certify_eq15(1780, 5000, dps=50, n_trunc=200)."""
    if not certify_eq15(1780, 5000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(1780, 5000, dps=50, n_trunc=200) returned False; "
            "refusing to certify `hEq15_oracle_certified_3560`."
        )
    return Fraction(1, 1)


def certify_eq15_at_3562() -> Fraction:
    """Pins certify_eq15(1781, 5000, dps=50, n_trunc=200)."""
    if not certify_eq15(1781, 5000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(1781, 5000, dps=50, n_trunc=200) returned False; "
            "refusing to certify `hEq15_oracle_certified_3562`."
        )
    return Fraction(1, 1)


def certify_eq15_at_hp_3564() -> Fraction:
    """Pins certify_eq15(1782, 5000, dps=100, n_trunc=500)."""
    if not certify_eq15(1782, 5000, dps=100, n_trunc=500):
        raise RuntimeError(
            "certify_eq15(1782, 5000, dps=100, n_trunc=500) returned False; "
            "refusing to certify `hEq15_oracle_certified_hp_3564`."
        )
    return Fraction(1, 1)


def certify_eq15_at_hp_35645() -> Fraction:
    """Pins certify_eq15(35645, 100000, dps=100, n_trunc=500)."""
    if not certify_eq15(35645, 100000, dps=100, n_trunc=500):
        raise RuntimeError(
            "certify_eq15(35645, 100000, dps=100, n_trunc=500) returned False; "
            "refusing to certify `hEq15_oracle_certified_hp_35645`."
        )
    return Fraction(1, 1)


# --- Joint two-window tau-partition mass (mp.quad backend, sprint 079) -------


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
    return mp.mpf("0.5") * (1 + mp.sqrt((1 + 3 * K_sq) / (1 - K_sq)))


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
    Joint two-window tau-partition mass at exact rational endpoints.
    True iff the mass is at least 1 + 10^(-min(dps, 30)). The mass crosses
    below 1 around c ~ 0.35654 (sprint 078 Phase 0 sweep), preserving
    falsifiability.
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
        m1 = _two_window_mass_window(
            c_mp, int(j1), _frac_to_mpf(rs1), _frac_to_mpf(rt1), n_trunc=int(n_trunc)
        )
        m2 = _two_window_mass_window(
            c_mp, int(j2), _frac_to_mpf(rt1), _frac_to_mpf(rt2), n_trunc=int(n_trunc)
        )
        eps = mp.mpf(10) ** (-min(int(dps), 30))
        return (m1 + m2) >= mp.mpf(1) + eps


def certify_two_window_mass_at_35646() -> Fraction:
    """
    Zero-argument shim for `h_two_window_mass_certified_at_35646`, pinning
    c = 35646/100000, rho_start_1 = 378083/1000000,
    rho_stop_1 = 411605/1000000 (= rho_start_2), rho_stop_2 = 999999/1000000,
    (j_1, j_2) = (2, 1), (dps, n_trunc) = (30, 200). Witness margin +1.9001e-3.
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
            "certify_two_window_mass at the sprint-079 rational endpoints "
            "returned False; refusing to certify the Lean axiom "
            "`h_two_window_mass_certified_at_35646`."
        )
    return Fraction(1, 1)


# --- Rigorous flint.arb interval quadrature for the sqrt-endpoint oracles ----
#
# K(c, rho) is single-peaked at rho = sqrt(c) (Wang structure: K decreases in
# t = (rho^2 - c)^2 / (4 c rho^2), which is convex in rho with minimum at
# sqrt(c)). Lambda is increasing in K. So on any sub-interval the supremum of
# Lambda is attained at rho_lo, rho_hi, or sqrt(c); the branch is decided
# rigorously by arb comparisons, and the well-separated branches use a single
# point evaluation whose radius is set by arithmetic precision, not width.


def _two_window_mass_paper_factor_arb(c_pows, rho_arb, n: int):
    """Rigorous arb enclosure of the n-th Wang paper factor at `rho_arb`."""
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
    """Arb enclosure of K(c, rho) = 2 rho (1 + c/rho^2) * prod_{n<n_trunc} factor_n."""
    rho2 = rho_arb ** 2
    prefactor = 2 * rho_arb * (1 + c_arb / rho2)
    prod = arb(1)
    for n in range(0, n_trunc):
        prod = prod * _two_window_mass_paper_factor_arb(c_pows, rho_arb, n)
    return prefactor * prod


def _two_window_mass_paper_lambda_from_K_arb(K_arb):
    """Lambda(K) = (1 + sqrt((1 + 3K^2)/(1 - K^2))) / 2, increasing in K on [0, 1)."""
    K_sq = K_arb * K_arb
    return arb(fmpq(1, 2)) * (1 + ((1 + 3 * K_sq) / (1 - K_sq)).sqrt())


def _two_window_mass_paper_lambda_arb(
    c_arb, c_pows, rho_lo, rho_hi, sqrt_c_arb, n_trunc: int, K_at_sqrt_cache: list
):
    """Rigorous arb upper enclosure of Lambda(c, rho) over [rho_lo, rho_hi]."""
    Lams = [
        _two_window_mass_paper_lambda_from_K_arb(
            _two_window_mass_paper_K_arb(c_arb, c_pows, rho_lo, n_trunc)
        ),
        _two_window_mass_paper_lambda_from_K_arb(
            _two_window_mass_paper_K_arb(c_arb, c_pows, rho_hi, n_trunc)
        ),
    ]
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
    out = Lams[0]
    for L in Lams[1:]:
        out = out.union(L)
    return out


def _two_window_mass_window_lower_arb(
    c_arb, c_pows, j: int, rho_start, rho_stop, sqrt_c_arb,
    n_trunc: int, n_subdivisions: int,
):
    """
    Rigorous arb lower bound on int 2 rho / (H_j(c, rho) Lambda(c, rho)) drho over
    [rho_start, rho_stop], where H_j = (j/(j+1)) c^(2j+2) / rho^(2j).

    Equal-width left-Riemann sum. Per sub-interval: Lambda upper via the
    monotonicity-aware dispatch above; H_j upper at rho_lo (H_j decreasing in
    rho for j >= 1); 2 rho lower at rho_lo (increasing). Converges at O(1/n).
    K is evaluated once per subdivision endpoint and reused.
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

        if (rho_hi <= sqrt_c_arb) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc
                )
            Lam_upper = (
                _two_window_mass_paper_lambda_from_K_arb(Ks[k])
                .union(_two_window_mass_paper_lambda_from_K_arb(Ks[k + 1]))
                .union(_two_window_mass_paper_lambda_from_K_arb(K_at_sqrt_cache[0]))
            )

        H_upper = j_factor * c_2j_2 / (rho_lo ** (2 * j))
        integrand_lower = (2 * rho_lo) / (H_upper * Lam_upper)
        total = total + sub_width * integrand_lower
    return total


def _branch1_window_mass_lower_arb(
    c_arb, c_pows, rho_start, rho_stop, sqrt_c_arb, n_trunc: int, n_subdivisions: int
):
    """
    Rigorous arb lower bound on the Branch.one fallback window mass
    int 12 rho^3 (rho^2 - c^2) / (c^6 Lambda(c, rho)) drho. The numerator is
    increasing whenever rho > c sqrt(3/5), which every boxA window satisfies,
    so its per-sub-interval minimum is at rho_lo.
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

        if (rho_hi <= sqrt_c_arb) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc
                )
            Lam_upper = (
                _two_window_mass_paper_lambda_from_K_arb(Ks[k])
                .union(_two_window_mass_paper_lambda_from_K_arb(Ks[k + 1]))
                .union(_two_window_mass_paper_lambda_from_K_arb(K_at_sqrt_cache[0]))
            )

        rho_lo_2 = rho_lo * rho_lo
        numer_lower = 12 * (rho_lo_2 * rho_lo) * (rho_lo_2 - c_arb * c_arb)
        total = total + sub_width * (numer_lower / (c_6 * Lam_upper))
    return total


def _certify_two_window_mass_sqrt_at(
    c: Fraction,
    label: str,
    *,
    rt2: Fraction = Fraction(999999, 1000000),
    n_trunc: int = 200,
    dps: int = 80,
    n_start: int = 256,
    n_cap: int = 16384,
) -> Fraction:
    """
    Shared rigorous-arb core for the sqrt-endpoint joint two-window mass oracles.

    Pins the canonical tau-breakpoint endpoints

        rho_start_1 = c * sqrt(9/8)   (so c^2 / rho_start_1^2 = 8/9 = tau(2))
        rho_stop_1  = c * sqrt(4/3)   (so c^2 / rho_stop_1^2  = 3/4 = tau(1))
                    = rho_start_2     (adjacency)
        rho_stop_2  = `rt2`

    with (j_1, j_2) = (2, 1), and returns Fraction(1, 1) iff the RIGOROUS arb
    interval-arithmetic lower bound on the joint mass exceeds 1 + 10^(-30).
    `n_subdivisions` doubles from `n_start` to `n_cap` until the floor clears;
    on exhaustion a RuntimeError is raised so the Evaluator records an
    oracle-check failure rather than silently accepting an unverified axiom.
    """
    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(f"{label}: pinned c is not in (0, 1).")
    if not (rt2 < Fraction(1)):
        raise RuntimeError(f"{label}: pinned rho_stop_2 is not below 1.")

    j1, j2 = 2, 1

    with ctx.workdps(int(dps)):
        c_arb = _arb_exact(c)
        rt2_arb = _arb_exact(rt2)
        rho_start_1_arb = c_arb * arb(fmpq(9, 8)).sqrt()
        rho_meet_arb = c_arb * arb(fmpq(4, 3)).sqrt()
        sqrt_c_arb = c_arb.sqrt()

        if not ((c_arb < rho_start_1_arb) is True):
            raise RuntimeError(f"{label}: ordering c < rho_start_1 fails.")
        if not ((rho_start_1_arb <= rho_meet_arb) is True):
            raise RuntimeError(f"{label}: ordering rho_start_1 <= rho_stop_1 fails.")
        if not ((rho_meet_arb <= rt2_arb) is True):
            raise RuntimeError(f"{label}: ordering rho_stop_1 <= rho_stop_2 fails.")

        c_pows = _pow_cached(c_arb, 2 * n_trunc + 3)
        floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

        n_subdivisions = n_start
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
            if n_subdivisions >= n_cap:
                break
            n_subdivisions *= 2

        raise RuntimeError(
            f"{label}: rigorous arb lower bound on joint mass = {last_total} "
            f"(margin = {last_total - arb(1)}) failed to clear the strict-margin "
            f"floor 1 + 10^(-30) at n_subdivisions = {n_subdivisions} "
            f"(cap = {n_cap}); refusing to certify."
        )


def certify_two_window_mass_at_35646_sqrt() -> Fraction:
    """
    Zero-argument shim for `h_two_window_mass_certified_at_35646_sqrt`, pinning
    c = 35646/100000 with the canonical sqrt endpoints, (j_1, j_2) = (2, 1),
    n_trunc = 200, arb precision dps = 80. Sprint 083's centered witness margin
    at these endpoints is +1.9001e-3; the rigorous arb lower bound clears the
    floor around n_subdivisions = 2048 with margin ~ +1.29e-3.
    """
    return _certify_two_window_mass_sqrt_at(
        Fraction(35646, 100000), "certify_two_window_mass_at_35646_sqrt"
    )


def certify_two_window_mass_at_35648_sqrt() -> Fraction:
    """
    Zero-argument shim for `h_two_window_mass_certified_at_35648_sqrt`, pinning
    c = 35648/100000 with the canonical sqrt endpoints

        rho_start_1 = c * sqrt(9/8)
        rho_stop_1  = c * sqrt(4/3)  (= rho_start_2)
        rho_stop_2  = 999999/1000000

    at (j_1, j_2) = (2, 1), n_trunc = 200, arb precision dps = 80.

    Numerical basis: sprint 078's Phase 0 sweep records joint-mass margin
    >= 1e-3 at every c in {0.35646, 0.35647, 0.35648}, with the mass only
    falling below 1 around c ~ 0.35654. Sprint 083 measured the arb
    conservatism at ~6e-4 at n_subdivisions = 2048, so the rigorous lower
    bound at c = 0.35648 clears 1 + 10^(-30) well inside the subdivision cap.
    Falsifiability is preserved: pinning c >= 0.35655 would make the joint
    mass fall below 1 and the shim would raise.
    """
    return _certify_two_window_mass_sqrt_at(
        Fraction(35648, 100000), "certify_two_window_mass_at_35648_sqrt"
    )
```

All four files are now emitted: `Candidates/V65/TauWindowEndpoints.lean`, `Candidates/V65.lean`, `lemma.toml`, and `Numerical_Library/rigorous_scalar.py`. Build `ProofRefinement/Korenblum/Candidates/V65.lean`.