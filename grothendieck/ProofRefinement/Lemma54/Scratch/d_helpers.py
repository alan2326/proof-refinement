"""Closed-form helpers for D(p,z) = (1−p)·H_0'(z) + p·H_η'(z).

H_0'(z) = 1/√(1−z²)
H_0''(z) = z / (1−z²)^{3/2}

Both sharp evaluation (acb) and chunk bounds (arb upper bounds over an
acb ball Z) are implemented here.

Used by v26_certify_md_par.py to build a rigorous lower bound on
m_D = inf_{p∈[0,1], z∈∂Ω} |D(p,z)|.
"""

from __future__ import annotations

import sys
from pathlib import Path

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))


# ----------------------------------------------------------------------
# Sharp closed-form evaluation
# ----------------------------------------------------------------------
def H0_prime_sharp(z: acb) -> acb:
    """H_0'(z) = 1/√(1−z²). Sharp value at acb z."""
    return acb(1) / (acb(1) - z * z).sqrt()


def H0_pp_sharp(z: acb) -> acb:
    """H_0''(z) = z/(1−z²)^{3/2}. Sharp value at acb z."""
    one_minus_z2 = acb(1) - z * z
    return z / (one_minus_z2 * one_minus_z2.sqrt())


# ----------------------------------------------------------------------
# Chunk bounds on |·| over an acb ball
# ----------------------------------------------------------------------
def bound_H0_prime_on_chunk(z_ball: acb) -> arb:
    """Upper bound on sup_{z∈Z} |H_0'(z)| = 1/√|1−z²|_lower."""
    one_minus_z2 = acb(1) - z_ball * z_ball
    abs_lo = one_minus_z2.abs_lower()
    if abs_lo <= arb(0):
        return arb("1e100")
    return arb(1) / abs_lo.sqrt()


def bound_H0_pp_on_chunk(z_ball: acb) -> arb:
    """Upper bound on sup_{z∈Z} |H_0''(z)| = |z|_upper / |1−z²|_lower^{3/2}.

    Strict triangle bound: |H_0''(z)| = |z| / |1−z²|^{3/2}, so
        sup |H_0''| ≤ sup|z| / inf|1−z²|^{3/2}.
    """
    one_minus_z2 = acb(1) - z_ball * z_ball
    abs_lo = one_minus_z2.abs_lower()
    if abs_lo <= arb(0):
        return arb("1e100")
    z_abs_ub = z_ball.abs_upper()
    den = abs_lo * abs_lo.sqrt()  # |1−z²|^{3/2}
    return z_abs_ub / den


# ----------------------------------------------------------------------
# Self-test
# ----------------------------------------------------------------------
if __name__ == "__main__":
    PREC = 200
    flint_ctx.prec = PREC

    print("=" * 72)
    print("Test: closed-form H_0'(z), H_0''(z) sharp + chunk bounds")
    print("=" * 72)

    # Sharp at z = 0.5 (real)
    z = acb(arb("0.5"), arb(0))
    print(f"\nz = {z}")
    print(f"  H_0'(0.5)  = {H0_prime_sharp(z)}  (expected: 1/√0.75 = 1.1547)")
    print(f"  H_0''(0.5) = {H0_pp_sharp(z)}  (expected: 0.5/0.75^1.5 = 0.7698)")

    # Sharp at corner-like z
    z2 = acb(arb("0.84"), arb("1.115"))
    print(f"\nz = {z2}")
    print(f"  H_0'(z)  = {H0_prime_sharp(z2)}")
    print(f"  H_0''(z) = {H0_pp_sharp(z2)}")
    print(f"  |H_0'|   = {H0_prime_sharp(z2).abs_upper().str(20)}")
    print(f"  |H_0''|  = {H0_pp_sharp(z2).abs_upper().str(20)}")

    # Chunk bounds: V26 corner chunk
    z_ball = acb(arb("0.8365"), arb.union(arb("0.97625"), arb("1.115")))
    print(f"\nz_ball = corner chunk: Re={z_ball.real}, Im={z_ball.imag}")
    print(f"  M_H0' = {bound_H0_prime_on_chunk(z_ball).str(20)}")
    print(f"  M_H0'' = {bound_H0_pp_on_chunk(z_ball).str(20)}")

    # Chunk bound: real edge chunk
    z_ball2 = acb(arb("0.8365"), arb.union(arb("-0.07"), arb("0.07")))
    print(f"\nz_ball = real edge chunk: Re={z_ball2.real}, Im={z_ball2.imag}")
    print(f"  M_H0' = {bound_H0_prime_on_chunk(z_ball2).str(20)}")
    print(f"  M_H0'' = {bound_H0_pp_on_chunk(z_ball2).str(20)}")

    print("\n" + "=" * 72)
