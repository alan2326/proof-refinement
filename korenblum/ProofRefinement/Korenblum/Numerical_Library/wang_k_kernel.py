from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx, fmpq

from .types import RationalBound


def _fmpq(fr: Fraction) -> fmpq:
    return fmpq(fr.numerator, fr.denominator)


def _arb_exact(fr: Fraction) -> arb:
    return arb(_fmpq(fr))


def _arb_box(lo: Fraction, hi: Fraction) -> arb:
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(_fmpq(mid), _fmpq(rad))


def _arb_floor_to_int(x: arb) -> int:
    floored = x.lower().floor()
    exact = floored.unique_fmpz()
    if exact is not None:
        return int(str(exact))
    text = str(floored)
    if " +/- " in text:
        text = text.split(" +/- ")[0]
    return int(text.split(".")[0])


def _arb_ceil_to_int(x: arb) -> int:
    ceiled = x.upper().ceil()
    exact = ceiled.unique_fmpz()
    if exact is not None:
        return int(str(exact))
    text = str(ceiled)
    if " +/- " in text:
        text = text.split(" +/- ")[0]
    return int(text.split(".")[0])


def rbound_upper_arb(x: arb, denom: int = 10**18) -> RationalBound:
    return RationalBound(num=_arb_ceil_to_int(x * denom), den=denom)


def rbound_upper_arb_below_one(
    x: arb,
    *,
    denom: int = 10**18,
    max_steps: int = 8,
) -> RationalBound:
    if not (x < 1):
        raise ValueError("cannot certify a strict < 1 upper rational bound")
    current = denom
    for _ in range(max_steps + 1):
        rb = rbound_upper_arb(x, denom=current)
        if rb.to_fraction() < 1:
            return rb
        current *= 10
    raise ValueError("failed to find a strict < 1 rational upper bound")


def rho_to_t(c: Fraction, rho: Fraction) -> Fraction:
    rho2 = rho * rho
    return ((rho2 - c) ** 2) / (4 * c * rho2)


def phi_fraction(a: Fraction) -> Fraction:
    return Fraction(4) * a / (1 + a) ** 2


def log_k_t_derivative_lower(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 30,
) -> Fraction:
    t_lo = min(rho_to_t(c, lo), rho_to_t(c, hi))
    t_hi = max(rho_to_t(c, lo), rho_to_t(c, hi))

    dec_upper = -Fraction(1, 1) / (2 * (1 + t_hi) ** 2)
    for n in range(1, n_terms + 1):
        p = phi_fraction(c ** (2 * n))
        q = phi_fraction(c ** (2 * n - 1))
        dec_upper += q**2 / (1 + q * t_lo) ** 2 - p**2 / (1 + p * t_lo) ** 2
    dec_upper += 16 * c ** (4 * n_terms + 2)
    if dec_upper >= 0:
        raise ValueError("failed to certify decrease of d/dt log K")

    total = Fraction(1, 1) / (2 * (1 + t_hi))
    for n in range(1, n_terms + 1):
        p = phi_fraction(c ** (2 * n))
        q = phi_fraction(c ** (2 * n - 1))
        total += p / (1 + p * t_hi) - q / (1 + q * t_hi)

    tail = 4 * c ** (2 * n_terms + 1) / (1 + c)
    lower = total - tail
    if lower <= 0:
        raise ValueError("failed to certify positivity of d/dt log K")
    return lower


def k_upper_at_point(
    c: Fraction,
    rho: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
) -> arb:
    with ctx.workdps(dps):
        rho_arb = _arb_exact(rho)
        rho2 = rho_arb ** 2
        rho_inv2 = 1 / rho2

        total = 2 * rho_arb * (1 + _arb_exact(c) / rho2)
        c_powers = [_arb_exact(Fraction(1, 1))]
        for _ in range(2 * n_terms + 2):
            c_powers.append(c_powers[-1] * _arb_exact(c))

        for n in range(1, n_terms + 1):
            num1 = 1 + rho2 * c_powers[2 * n - 1]
            num2 = 1 + rho_inv2 * c_powers[2 * n + 1]
            num3 = (1 + c_powers[2 * n]) ** 2
            den1 = 1 + rho2 * c_powers[2 * n - 2]
            den2 = 1 + rho_inv2 * c_powers[2 * n]
            den3 = (1 + c_powers[2 * n - 1]) ** 2
            total *= (num1 * num2 * num3) / (den1 * den2 * den3)
        return total


def k_upper_on_interval(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
) -> arb:
    monotone_lb = log_k_t_derivative_lower(c, lo, hi, n_terms=min(n_terms, 30))
    if monotone_lb <= 0:
        raise ValueError("failed to certify K-monotonicity")

    t_lo = rho_to_t(c, lo)
    t_hi = rho_to_t(c, hi)
    rho_max = lo if t_lo >= t_hi else hi
    return k_upper_at_point(c, rho_max, n_terms=n_terms, dps=dps)


def k_sq_upper_on_interval(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    *,
    n_terms: int = 80,
    dps: int = 100,
    rat_denom: int = 10**18,
    k_sq_denom: int = 10**24,
) -> tuple[RationalBound, RationalBound]:
    with ctx.workdps(dps):
        k_upper = k_upper_on_interval(c, lo, hi, n_terms=n_terms, dps=dps)
        if k_upper < 1:
            k_upper_rb = rbound_upper_arb_below_one(k_upper, denom=rat_denom)
        else:
            k_upper_rb = rbound_upper_arb(k_upper, denom=rat_denom)
        k_sq_upper_rb = rbound_upper_arb_below_one(k_upper * k_upper, denom=k_sq_denom)
        return k_upper_rb, k_sq_upper_rb
