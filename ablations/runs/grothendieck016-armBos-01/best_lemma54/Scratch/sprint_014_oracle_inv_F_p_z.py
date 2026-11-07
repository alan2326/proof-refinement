"""Smoke test for the new compute_inv_F_p_z_bound oracle.

Confirms the certified bound is ≤ 2, supporting `inv_F_p_z_val := 2`.
"""

import sys
from pathlib import Path

# Make the Numerical_Library importable.
sys.path.insert(0, str(Path(__file__).parent.parent))

from Numerical_Library import compute_inv_F_p_z_bound


def main():
    print("Computing inv_F_p_z bound at production-grade params...")
    result = compute_inv_F_p_z_bound(
        eta=0.01,
        delta="1635/10000",
        B="1115/1000",
        p_max="1",
        n_per_edge=512,
        prec=200,
        K_max=80,
    )
    print(f"  ball_value (sup 1/‖D‖ upper float): {result.ball_value}")
    print(f"  rationalised bound: {result.bound} = {float(result.bound):.6f}")
    print(f"  inf ‖H_0'‖ certified str: {result.meta['inf_H0p_arb_str']}")
    print(f"  sup ‖H_η' − H_0'‖ certified str: {result.meta['sup_phi_prime_arb_str']}")
    print(f"  inf ‖D‖ certified str: {result.meta['inf_D_arb_str']}")
    print(f"  inv_F_p_z arb str: {result.meta['inv_F_p_z_arb_str']}")

    # Decision: pick the smallest integer ceiling that dominates the bound.
    if result.bound <= 2:
        print()
        print("==> inv_F_p_z_val := 2 is feasible (oracle bound ≤ 2).")
    elif result.bound <= 5:
        print()
        print(f"==> inv_F_p_z_val := {int(result.bound) + 1} works "
              f"(oracle bound > 2 — would lift Cr_val).")
    else:
        print()
        print("==> oracle bound > 5: would lift Cr_val above V9's 5; "
              "BLOCKED for this sprint.")


if __name__ == "__main__":
    main()
