from __future__ import annotations

from fractions import Fraction


def lambda_upper_witness_ok(k_sq_upper: Fraction, lambda_upper: Fraction) -> bool:
    return (
        Fraction(0) <= k_sq_upper
        and k_sq_upper < 1
        and Fraction(0) <= 2 * lambda_upper - 1
        and 1 + 3 * k_sq_upper <= (2 * lambda_upper - 1) ** 2 * (1 - k_sq_upper)
    )


def mass_from_constant_box(
    c: Fraction,
    lo: Fraction,
    hi: Fraction,
    branch: int,
    alpha: Fraction,
) -> Fraction:
    if branch == 1:
        return alpha * (
            Fraction(2) * hi**6 / c**6
            - Fraction(3) * hi**4 / c**4
            - (Fraction(2) * lo**6 / c**6 - Fraction(3) * lo**4 / c**4)
        )
    if branch == 2:
        return alpha * ((hi**4 - lo**4) / c**4)
    raise ValueError(f"unknown branch {branch}")
