from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class RationalBound:
    num: int
    den: int

    def to_fraction(self) -> Fraction:
        return Fraction(self.num, self.den)

    def to_lean(self) -> str:
        return f"{self.num} / {self.den}"

    @property
    def value(self) -> float:
        return float(self.to_fraction())


@dataclass(frozen=True)
class BoxCertificate:
    index: int
    branch: int
    lo: RationalBound
    hi: RationalBound
    alpha: RationalBound
    beta: RationalBound
    mass_lower: RationalBound
    k_upper: RationalBound
    lambda_upper: RationalBound
    k_sq_upper: RationalBound | None = None


@dataclass(frozen=True)
class ScalarCertificate:
    target_c: RationalBound
    total_mass_lower: RationalBound
    boxes: tuple[BoxCertificate, ...]
    n_terms: int
    dps: int
    split_lo: RationalBound
    split_hi: RationalBound
    one_cut: RationalBound
