"""Smoke test for the three new η-aware oracles in Numerical_Library/.

Runs each at low n_per_edge, low prec to verify:
  - The pipeline works (no exceptions)
  - The numbers are in the expected ballpark for a meaningful Cr_refined win

Expected ballparks at η=0.01, Ω(0.1635, 1.115), M=428:
  - M_phi      ≈ 4–10   (η-aware vs trivial 2M=856)
  - M_phi_prime≈ 4–10   (η-aware vs trivial 2M=856)
  - M_pp       ≈ 5–50   (sup |H_0''| + sup |H_η''|; existing Cauchy gave 8R/(1-r)² ≈ 1437,
                         and the M_pp · invFp³ chain wins iff M_pp < (1-r)/R² ≈ 0.06,
                         which is unrealistic — meaning the M_pp oracle alone CANNOT
                         beat the Cauchy step at our params; the win comes from M_phi
                         and M_phi_prime tightening, not M_pp.)

Usage:
    PYTHONPATH=. uv run python ProofRefinement/Lemma54/Scratch/sprint_proposal_001_smoke.py
"""
from __future__ import annotations

import time
import sys
from pathlib import Path

# Make Numerical_Library importable.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))

from Numerical_Library import (
    compute_M_phi_bound,
    compute_M_phi_prime_bound,
    compute_M_pp_bound,
)


# Production-grade params (matches existing compute_M_bound_tight scale).
SMOKE = dict(
    eta=0.01,
    delta="1635/10000",
    B="1115/1000",
    n_per_edge=512,
    prec=200,
    K_max=80,
)


def time_call(name: str, fn, **kw):
    t0 = time.time()
    r = fn(**kw)
    dt = time.time() - t0
    print(f"  {name}:")
    print(f"    bound (Fraction)   = {r.bound} ≈ {float(r.bound):.6f}")
    print(f"    ball_upper (float) = {r.ball_value:.6f}")
    print(f"    prec               = {r.prec}")
    if "M_phi_arb_str" in r.meta:
        print(f"    arb str            = {r.meta['M_phi_arb_str']}")
    if "M_phi_prime_arb_str" in r.meta:
        print(f"    arb str            = {r.meta['M_phi_prime_arb_str']}")
    if "M_pp_arb_str" in r.meta:
        print(f"    arb str            = {r.meta['M_pp_arb_str']}")
        print(f"    ├─ sup ‖H_0''‖    = {r.meta['max_H0_pp_arb_str']}")
        print(f"    └─ sup ‖H_η''‖    = {r.meta['max_H_eta_pp_arb_str']}")
    print(f"    wall time          = {dt:.2f}s")
    print()
    return r


def main():
    print("=" * 72)
    print("Smoke test: proposal_001 oracles (M_phi, M_phi_prime, M_pp)")
    print(f"  params: {SMOKE}")
    print("=" * 72)
    print()

    r_phi = time_call("M_phi (= sup |H_η − H_0| on dΩ)",
                      compute_M_phi_bound, **SMOKE)
    r_pp_prime = time_call("M_phi_prime (= sup |H_η' − H_0'| on dΩ)",
                           compute_M_phi_prime_bound, **SMOKE)
    r_pp = time_call("M_pp (= sup |F_ww| on Ω, triangle-bounded)",
                     compute_M_pp_bound, **SMOKE)

    # Cr_refined arithmetic at our params.
    M = 428
    R = 23 / 20      # V8's literal upper bound on R_val_paper
    one_minus_r = 2 / 25
    invFp = 2 * R / one_minus_r
    invFp_sq = invFp ** 2
    invFp_cube = invFp ** 3

    M_phi = float(r_phi.bound)
    M_phi_prime = float(r_pp_prime.bound)
    M_pp = float(r_pp.bound)

    # Cr_refined (half-Lagrange of ‖u''‖ bound):
    #   ‖u''‖ ≤ 2 M_phi_prime · M_phi · invFp² + (M_pp · invFp³) · M_phi²
    # Cr_refined = (1/2) · that = M_phi_prime · M_phi · invFp² + (1/2) M_pp · invFp³ · M_phi²
    term1 = M_phi_prime * M_phi * invFp_sq
    term2 = 0.5 * M_pp * invFp_cube * (M_phi ** 2)
    Cr_refined = term1 + term2

    Cr_V8 = 1132310000  # V8's current Cr_val
    Cr_tight_via_oracles = M_phi_prime * M_phi * invFp_sq + (8 * R / one_minus_r ** 2) * M_phi ** 2 / 2
    win_factor = Cr_V8 / Cr_refined if Cr_refined > 0 else float("inf")

    print("=" * 72)
    print("Cr_refined arithmetic at V8 params (M=428, R=23/20, 1-r=2/25):")
    print(f"  invFp² = {invFp_sq:.4f},  invFp³ = {invFp_cube:.4f}")
    print()
    print(f"  Term 1: M_phi_prime · M_phi · invFp²")
    print(f"        = {M_phi_prime:.4f} · {M_phi:.4f} · {invFp_sq:.4f}")
    print(f"        = {term1:.4e}")
    print()
    print(f"  Term 2: (1/2) M_pp · invFp³ · M_phi²")
    print(f"        = 0.5 · {M_pp:.4f} · {invFp_cube:.4f} · {M_phi**2:.4f}")
    print(f"        = {term2:.4e}")
    print()
    print(f"  Cr_refined = {Cr_refined:.4e}")
    print(f"  V8 Cr_val  = {Cr_V8:.4e}")
    print(f"  Win factor = {win_factor:.2f}×")
    print()
    print("  (For comparison: replacing only M_phi/M_phi_prime, leaving 8R/(1-r)² Cauchy:")
    print(f"    Cr would be ≈ {Cr_tight_via_oracles:.4e}, win {Cr_V8/Cr_tight_via_oracles:.2f}×)")
    print()
    print("=" * 72)


if __name__ == "__main__":
    main()
