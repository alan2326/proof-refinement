"""
Run the certified pipeline (just Step 1 + Step 2) at r = 23/25, eta = 1/100,
and print the resulting M, R, Cr. This is the "paper proof" baseline that
Candidates/V0.lean is targeting; smaller Cr in any V_n means we've improved.
"""

import time

from flint import arb

from grothendieck.proof.certified.arb_utils import set_prec
from grothendieck.proof.certified.certify_invertibility import (
    certify_invertibility,
)
from grothendieck.proof.certified.compute_cr import compute_Cr_full


def main():
    r = 23 / 25       # = 0.92, matches SearchConfig.r
    eta = 1 / 100     # = 0.01, matches SearchConfig.eta
    prec = 128

    set_prec(prec)
    print(f"params: r = 23/25 = {r}, eta = 1/100 = {eta}, prec = {prec}")
    print()

    t0 = time.time()
    print("Step 1: certify_invertibility (Rouche at r_outer = (1+r)/2 = 24/25)")
    inv = certify_invertibility(r=r, eta=eta, prec=prec, verbose=True)
    t1 = time.time()
    print(f"  step 1 took {t1-t0:.1f}s\n")

    delta = inv["delta"]
    B = inv["B"]

    t2 = time.time()
    print("Step 2: compute_Cr_full")
    out = compute_Cr_full(
        r=arb(str(r)),
        delta=delta,
        B=B,
        prec=prec,
        verbose=True,
    )
    t3 = time.time()
    print(f"  step 2 took {t3-t2:.1f}s\n")

    print("=" * 60)
    print("baseline (paper formula, certified-arb):")
    print(f"  M     = {out['M']}")
    print(f"  R     = {out['R']}")
    print(f"  Cr    = {out['C_r']}")
    print("=" * 60)


if __name__ == "__main__":
    main()
