"""
Gaussian distribution utilities in Arb ball arithmetic.

Provides standard normal PDF, CDF, and related functions with rigorous
error tracking via arb balls.
"""

from __future__ import annotations

from flint import arb, ctx as flint_ctx


def normal_pdf_arb(x: arb) -> arb:
    """Standard normal PDF: phi(x) = (1/sqrt(2*pi)) * exp(-x^2/2)"""
    return (-x * x / arb(2)).exp() / (arb(2) * arb.pi()).sqrt()


def normal_cdf_arb(x: arb) -> arb:
    """Standard normal CDF: Phi(x) = (1 + erf(x/sqrt(2))) / 2"""
    return (arb(1) + (x / arb(2).sqrt()).erf()) / arb(2)


def erf_normalized_arb(x: arb) -> arb:
    """Normalized error function: erf(x/sqrt(2))"""
    return (x / arb(2).sqrt()).erf()


def gaussian_one_minus_2cdf_arb(x: arb) -> arb:
    """1 - 2*Phi(x) = -erf(x/sqrt(2))

    This is g_0(x) in the semi-analytic formula.
    """
    return -(x / arb(2).sqrt()).erf()
