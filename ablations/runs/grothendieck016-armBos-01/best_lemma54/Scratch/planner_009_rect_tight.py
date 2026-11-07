"""Planner sprint 009 numerical exploration.

Goal: tighten the Rouché-certified rectangle from (163/1000, 1115/1000) to
(1635/10000, 1115/1000) — the largest delta the Rouché margin certifies at
the same B. This shrinks the M oracle from ≈ 430.18 to ≈ 427.65, dropping
the integer ceiling M_val from 431 → 428 and Cr_val from 1148240000 → 1132310000
(a 1.387 % reduction).

Verifies, in this order:

1. The rectangle (1635/10000, 1115/1000) is Rouché-certified at r = 23/25
   (sin(disk r_outer) ⊆ Ω, Rouché margin > 0, p · M_d < margin).
2. The certified ball for `compute_M_rigorous` at this rectangle is
   ≈ [427.65 +/- ε], well below the integer ceiling 428.
3. The high-precision oracle (n_per_edge=8192, prec=600, safety_rel=1e-5)
   emits a rationalized bound `855827/2000 ≈ 427.9135 < 428`.
4. Cr_val = 1132310000 is the next clean multiple of 10000 above
   16 · 428² · (23/20) · (43/20) / (2/25)² = 1132306100, with nlinarith
   margin 624/25 = 24.96.
"""

from __future__ import annotations

import sys
from fractions import Fraction

sys.path.insert(0, '/home/rsaha/projects/grothendieck/ProofGraph')
sys.path.insert(0, '/home/rsaha/projects/grothendieck/ProofRefinement/Lemma54')

from flint import arb, ctx as flint_ctx
flint_ctx.prec = 400

from grothendieck.proof.certified.certify_invertibility import (  # noqa: E402
    certified_lt,
    certified_positive,
    certify_sin_r_disk_in_omega,
    choose_p,
    compute_perturbation_bound_omega,
    compute_rouche_margin_omega,
)
from grothendieck.proof.certified.compute_cr import compute_M_rigorous  # noqa: E402
from Numerical_Library import compute_M_bound  # noqa: E402


def main() -> None:
    r_arb = arb('23/25')
    r_outer = (arb(1) + r_arb) / arb(2)

    # Step 1 — Rouché certification at (1635/10000, 1115/1000).
    delta_arb = arb('1635/10000')
    B_arb = arb('1115/1000')

    print('=== Step 1: Rouché certification ===')
    check = certify_sin_r_disk_in_omega(r_outer, delta_arb, B_arb, prec=400)
    print(f'  sinh(r_outer) < B?    im={check["imaginary_check"]}')
    print(f'  max|Re sin| < 1−delta? re={check["real_check"]}')
    assert check['imaginary_check'] and check['real_check']

    m = compute_rouche_margin_omega(r_outer, delta_arb, B_arb, prec=400)
    print(f'  Rouché margin       m = {float(m):.6f}')
    assert certified_positive(m)

    Md = compute_perturbation_bound_omega(delta_arb, B_arb, prec=400, verbose=False)
    p = choose_p(m, Md)
    rouche_lhs = p * Md
    print(f'  p·M_d < m?            {certified_lt(rouche_lhs, m)}')
    assert certified_lt(rouche_lhs, m)

    # Step 2 — M ball.
    print()
    print('=== Step 2: M-ball at (1635/10000, 1115/1000) ===')
    M_arb = compute_M_rigorous(r_arb, delta_arb, B_arb, n_per_edge=8192, prec=600)
    print(f'  M_arb = {M_arb.str(20, more=True)}')
    print(f'  upper(M_arb) ≈ {float(M_arb.upper()):.4f}')
    assert float(M_arb.upper()) < 428.0, f'M upper {float(M_arb.upper())} should be < 428'

    # Step 3 — High-precision oracle bound.
    print()
    print('=== Step 3: oracle rationalized bound ===')
    res_low = compute_M_bound(
        r='23/25', eta=0.01,
        delta='1635/10000', B='1115/1000',
        n_per_edge=4096, prec=400,
        max_denom=10000, safety_rel=1e-4,
    )
    print(f'  V6-precision (4096/400/1e-4): bound = {res_low.bound} ≈ {float(res_low.bound):.4f}')

    res_hi = compute_M_bound(
        r='23/25', eta=0.01,
        delta='1635/10000', B='1115/1000',
        n_per_edge=8192, prec=600,
        max_denom=10000, safety_rel=1e-5,
    )
    print(f'  HighPrec (8192/600/1e-5):     bound = {res_hi.bound} ≈ {float(res_hi.bound):.4f}')
    assert float(res_hi.bound) < 428.0
    print(f'  → M_val = 428 admissible: bound {float(res_hi.bound):.4f} ≤ 428')

    # Step 4 — Cr_val arithmetic.
    print()
    print('=== Step 4: Cr_val arithmetic ===')
    M = Fraction(428)
    R = Fraction(23, 20)
    one_minus_r = Fraction(2, 25)
    Cr_min = 16 * M * M * R * (R + 1) / one_minus_r ** 2
    print(f'  Cr_min = 16·M²·R·(R+1)/(1−r)² = {Cr_min} = {float(Cr_min)}')

    Cr_val = Fraction(1132310000)
    assert Cr_val >= Cr_min, f'Cr_val {Cr_val} < Cr_min {Cr_min}'
    print(f'  Cr_val = {Cr_val} (= clean multiple of 10000 above Cr_min)')

    lhs = 16 * M * M * R * (R + 1)
    rhs = Cr_val * one_minus_r ** 2
    margin = rhs - lhs
    print(f'  nlinarith LHS_max = 16·M²·R·(R+1) = {lhs} = {float(lhs)}')
    print(f'  nlinarith RHS     = Cr_val·(2/25)² = {rhs} = {float(rhs)}')
    print(f'  nlinarith margin  = {margin} = {float(margin)}')
    assert margin > 0

    # Comparison with V6.
    Cr_v6 = Fraction(1148240000)
    ratio = Cr_val / Cr_v6
    print()
    print(f'  V6 score: {Cr_v6}')
    print(f'  V7 score: {Cr_val}')
    print(f'  ratio = {float(ratio):.6f}, reduction = {(1 - float(ratio)) * 100:.3f}%')


if __name__ == '__main__':
    main()
