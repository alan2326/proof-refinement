"""Shared types for Numerical_Library functions."""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any


@dataclass
class OracleResult:
    """The output of a Numerical_Library bound function.

    Attributes:
        bound: An exact rational upper bound suitable for use in Lean as
            `def <field>_val : ℝ := <num> / <den>`. Constructed from `Fraction`
            so equality with the candidate's declared value is unambiguous.
        ball_value: The arb-ball value (or float approximation) before
            rationalization. For diagnostics only.
        prec: Precision (bits) the computation used.
        meta: Function-specific extra info (region parameters, intermediate
            sub-bounds, etc.). Must be JSON-serializable.
    """

    bound: Fraction
    ball_value: float
    prec: int
    meta: dict[str, Any] = field(default_factory=dict)

    def to_lean(self) -> str:
        """Render as a Lean rational literal: `<num> / <den>`."""
        return f"{self.bound.numerator} / {self.bound.denominator}"
