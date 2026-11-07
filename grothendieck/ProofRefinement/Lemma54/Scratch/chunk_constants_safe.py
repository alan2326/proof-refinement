"""Safe chunk-constants helper: avoids arb-ball squaring imprecision.

For arb x represented as midpoint ± radius, x*x can introduce a spurious
negative lower bound when the radius is large relative to |mid|. This breaks
|1-z|² computations when Im(z) is a wide interval.

Fix: compute (1-Re_z)² and Im_z² using ABSOLUTE-VALUE-BASED tight squaring,
which respects non-negativity.

For x with bounds [a, b]:
    x² lower = (max(0, a) if a ≥ 0 else (max(0, -b) if b ≤ 0 else 0))²
    x² upper = max(a², b²)
"""

from __future__ import annotations

from flint import arb, acb, ctx as flint_ctx


def safe_sqr(x: arb) -> arb:
    """Tight square of arb x, preserving non-negativity.

    Returns an arb whose interval [lo, hi] satisfies:
        lo ≥ 0  (whenever x is real)
        hi ≥ x² for all values of x
    """
    abs_lo = x.abs_lower()  # max(0, |x|) lower bound
    abs_hi = x.abs_upper()  # |x| upper bound
    sq_lo = abs_lo * abs_lo
    sq_hi = abs_hi * abs_hi
    return arb.union(sq_lo, sq_hi)


def safe_chunk_constants(z_ball: acb) -> tuple[arb, arb, arb, arb]:
    """Compute (d_Z, alpha_Z, beta_Z, |z|_ub) for a chunk acb-ball,
    using safe squaring throughout to avoid arb-ball imprecision.

    Returns:
        d_Z       : arb_lower of |1 - z²| over chunk (positive)
        alpha_Z   : arb_lower of Re(1/(1-z)) over chunk (positive)
        beta_Z    : arb_lower of Re(1/(1+z)) over chunk (positive)
        z_abs_ub  : arb_upper of |z| over chunk
    """
    re_z = z_ball.real
    im_z = z_ball.imag

    # 1 - Re(z), 1 + Re(z): may be wide if Re is wide.
    one_minus_re = arb(1) - re_z
    one_plus_re = arb(1) + re_z

    # Squared real parts (tight via safe_sqr — handles wide intervals)
    one_minus_re_sq = safe_sqr(one_minus_re)
    one_plus_re_sq = safe_sqr(one_plus_re)
    im_sq = safe_sqr(im_z)

    # |1-z|², |1+z|² (sums of non-negative arb intervals — preserves positivity)
    one_minus_z_abs_sq = one_minus_re_sq + im_sq
    one_plus_z_abs_sq = one_plus_re_sq + im_sq

    # |1-z²| via the identity |1-z²| = |1-z|·|1+z| (multiplicativity of |·|).
    # Computing as (acb(1)-z)*(acb(1)+z) and taking abs would re-square the wide
    # imag part inside acb arithmetic — same bug we're working around. Instead
    # build |1-z²|² = |1-z|²·|1+z|² from the safe-squared building blocks.
    # arb·arb in midpoint-radius form gives loose lower bounds even for
    # non-negative factors; use explicit .lower()·.lower() for a tight bound.
    omz_sq_lo = one_minus_z_abs_sq.lower()
    opz_sq_lo = one_plus_z_abs_sq.lower()
    if omz_sq_lo > arb(0) and opz_sq_lo > arb(0):
        d_Z_acb = (omz_sq_lo * opz_sq_lo).sqrt()
    else:
        d_Z_acb = arb(0)

    # alpha_Z = inf Re(1/(1-z)) = inf (1-Re(z)) / |1-z|²
    # For z in chunk (acb-ball with Re_z in some interval), this is the inf
    # of a real-valued function over the chunk.
    # Using interval arithmetic: bound numerator by inf, denominator by sup,
    # but only if numerator > 0 throughout the chunk.
    one_minus_re_lo = one_minus_re.lower()  # arb (sharp value)
    one_plus_re_lo = one_plus_re.lower()

    # If numerator can be negative anywhere in the chunk, alpha is not bounded
    # below by simple inf/sup. Require strict positivity.
    if not (one_minus_re_lo > arb(0)):
        alpha_Z = arb(0)
    else:
        # |1-z|² upper bound (arb supremum on chunk)
        denom_ub = one_minus_z_abs_sq.upper()
        if not (denom_ub > arb(0)):
            alpha_Z = arb(0)
        else:
            alpha_Z = one_minus_re_lo / denom_ub

    if not (one_plus_re_lo > arb(0)):
        beta_Z = arb(0)
    else:
        denom_ub = one_plus_z_abs_sq.upper()
        if not (denom_ub > arb(0)):
            beta_Z = arb(0)
        else:
            beta_Z = one_plus_re_lo / denom_ub

    z_abs_ub = z_ball.abs_upper()

    return d_Z_acb, alpha_Z, beta_Z, z_abs_ub


# ----------------------------------------------------------------------
if __name__ == "__main__":
    flint_ctx.prec = 200

    # Test on the failing chunk: Re=0.8465 sharp, Im in [-0.282, 0]
    z_test = acb(arb("8465/10000"), arb.union(arb(0), arb("-282/1000")))
    print(f"Test chunk: z = {z_test}")
    d_Z, alpha_Z, beta_Z, z_abs_ub = safe_chunk_constants(z_test)
    print(f"  d_Z = {d_Z.str(8)}")
    print(f"  alpha_Z = {alpha_Z.str(8)}")
    print(f"  beta_Z = {beta_Z.str(8)}")
    print(f"  |z|_ub = {z_abs_ub.str(8)}")

    # Compare to old chunk_constants
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from phi_prime_chunk_bound_certified import _chunk_constants
    print("\nOld chunk_constants on same chunk:")
    d_Z2, alpha_Z2, beta_Z2, z_abs_ub2 = _chunk_constants(z_test)
    print(f"  d_Z = {d_Z2.str(8)}")
    print(f"  alpha_Z = {alpha_Z2.str(8)}")
    print(f"  beta_Z = {beta_Z2.str(8)}")
    print(f"  |z|_ub = {z_abs_ub2.str(8)}")

    # Verify on a known-good chunk
    z_good = acb(arb("0.5"), arb.union(arb("-0.05"), arb("0.05")))
    print("\nKnown-good chunk: z = 0.5 ± 0.05i")
    d_Z, alpha_Z, beta_Z, z_abs_ub = safe_chunk_constants(z_good)
    print(f"  d_Z = {d_Z.str(8)}")
    print(f"  alpha_Z = {alpha_Z.str(8)}  (expect ~1.98)")
    print(f"  beta_Z = {beta_Z.str(8)}  (expect ~0.67)")

    d_Z2, alpha_Z2, beta_Z2, z_abs_ub2 = _chunk_constants(z_good)
    print(f"  old: alpha_Z = {alpha_Z2.str(8)}, beta_Z = {beta_Z2.str(8)}")
