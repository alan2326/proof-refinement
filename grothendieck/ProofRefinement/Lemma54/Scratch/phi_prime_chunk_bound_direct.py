"""η²-aware chunk bound on sup_{z ∈ Z} |Φ'(z)| where Φ' = H_η' − H_0'.

Standard derivation (no triangle on H_η'/H_0' separately):

    Φ'(z) = H_η'(z) − H_0'(z)
          = (1/(π(1−z²))) · ∫∫ [(1+P'Q')·e^{−S_z[P,Q]} − e^{−S_z[0,0]}] dx dy

Decompose the bracket:
    (1+P'Q')·e^{−S_z[P,Q]} − e^{−S_z[0,0]}
        = P'·Q' · e^{−S_z[P,Q]}                        ← O(η²)
        + (e^{−S_z[P,Q]} − e^{−S_z[0,0]})              ← O(η²)

For the second term, |e^a − e^b| ≤ |a−b|·max(|e^a|, |e^b|), and
    |S_z[P,Q] − S_z[0,0]| = |P² + Q² − 2z·PQ| / |1−z²|
                          ≤ (P² + Q² + 2|z|·|PQ|) / |1−z²|

Real-majorant identity: E_Z[P,Q](x,y) ≤ E_Z[0,0](x,y) (adding the (P,Q)
coordinates to the squared distance can only decrease the Gaussian).

Combining (over z ∈ Z):
    |Φ'(z)| ≤ (1/(π·d_Z)) · ∫∫ E_Z[0,0]·[|P'Q'| + (P²+Q²+2|z|·|PQ|)/d_Z] dx dy

with chunk constants d_Z, α_Z, β_Z as in h_eta_prime_chunk_bound.py.

Both |P'Q'| and (P², Q², PQ) are O(η²) for our V26 curves — this
captures the η²-cancellation that the simple triangle bound loses.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Callable

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

from grothendieck.proof.certified.bk_rigor import (
    compute_gl_nodes_weights_arb,
    scale_gl_to_interval,
)
from h_eta_prime_chunk_bound import _chunk_constants


def bound_Phi_prime_on_chunk_direct(
    z_ball: acb,
    P: Callable, Pp: Callable,
    Q: Callable, Qp: Callable,
    L_outer: int = 8,
    n_panels: int = 8,
    n_gl: int = 20,
    prec: int = 200,
    gl_dps: int = 80,
    verbose: bool = False,
) -> arb:
    """η²-aware upper bound on sup_{z ∈ Z} |Φ'(z)|.

    Returns an arb upper bound. For typical V26 chunks at η=0.01, this
    should give ~ 10⁻⁴..10⁻³ rather than the loose triangle value ~3.
    """
    flint_ctx.prec = prec
    d_Z, alpha_Z, beta_Z, z_abs_ub = _chunk_constants(z_ball)

    if verbose:
        print(f"  d_Z = {float(d_Z):.4e}, α_Z = {float(alpha_Z):.4e}, "
              f"β_Z = {float(beta_Z):.4e}, |z|_ub = {float(z_abs_ub):.4f}")

    L_arb = arb(L_outer)
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, gl_dps, prec)
    panel_width = arb(2 * L_outer) / arb(n_panels)
    all_nodes = []
    for p in range(n_panels):
        a = -L_arb + arb(p) * panel_width
        b = a + panel_width
        s_nodes, s_weights = scale_gl_to_interval(ref_nodes, ref_weights, a, b)
        for nd, wt in zip(s_nodes, s_weights):
            all_nodes.append((nd, wt))
    n_total = len(all_nodes)

    P_at = [P(nd, prec) for nd, _ in all_nodes]
    Pp_at = [Pp(nd, prec) for nd, _ in all_nodes]
    Q_at = [Q(nd, prec) for nd, _ in all_nodes]
    Qp_at = [Qp(nd, prec) for nd, _ in all_nodes]

    half = arb(1) / arb(2)
    integral_sum = arb(0)
    two_z_ub = arb(2) * z_abs_ub

    for j in range(n_total):
        y_j, w_y = all_nodes[j]
        Q_y = Q_at[j]
        Qp_y = Qp_at[j]
        Q_abs = abs(Q_y)
        Q2 = Q_y * Q_y

        for i in range(n_total):
            x_i, w_x = all_nodes[i]
            P_x = P_at[i]
            Pp_x = Pp_at[i]
            P_abs = abs(P_x)
            P2 = P_x * P_x

            # Real majorant E_Z[0,0] = exp(-α/2·(x-y)² - β/2·(x+y)²)
            diff_x = x_i - y_j
            sum_x = x_i + y_j
            E_Z = (-half * (alpha_Z * diff_x * diff_x
                             + beta_Z * sum_x * sum_x)).exp()

            # |P'Q'| (η²-small)
            J_eta = abs(Pp_x * Qp_y)
            # (P² + Q² + 2|z|·|PQ|)/d_Z (η²-small)
            S_diff = (P2 + Q2 + two_z_ub * P_abs * Q_abs) / d_Z
            integrand = (J_eta + S_diff) * E_Z

            integral_sum += w_x * w_y * integrand

    return integral_sum / (arb.pi() * d_Z)


# ----------------------------------------------------------------------
# Self-test
# ----------------------------------------------------------------------
if __name__ == "__main__":
    PREC = 200
    flint_ctx.prec = PREC

    from h_eta_prime_integral import (
        make_v26_P, make_v26_Pprime, compute_H_eta_prime_sharp,
    )
    from d_helpers import H0_prime_sharp

    eta_arb = arb("0.01")
    P_plus = make_v26_P(eta_arb, +1)
    Pp_plus = make_v26_Pprime(eta_arb, +1)
    Q_minus = make_v26_P(eta_arb, -1)
    Qp_minus = make_v26_Pprime(eta_arb, -1)

    print("=" * 72)
    print("Test: η²-aware Φ' chunk bound vs sharp |Φ'(z_mid)|")
    print("=" * 72)

    test_chunks = [
        ("real, half=0.05", acb(arb("0.5"), arb.union(arb("-0.05"), arb("0.05")))),
        ("V26 corner-ish", acb(arb("0.84"), arb.union(arb("0.97"), arb("1.115")))),
        ("V26 spike (Im=0.21)", acb(arb("0.84"), arb.union(arb("0.14"), arb("0.28")))),
    ]

    for label, z_ball in test_chunks:
        print(f"\n>> chunk: {label}")
        # Sharp Φ' at midpoint
        z_mid = acb(z_ball.real.mid(), z_ball.imag.mid())
        Hp_sharp = compute_H_eta_prime_sharp(
            z_mid, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=PREC,
        )
        H0p_sharp = H0_prime_sharp(z_mid)
        Phi_p_sharp_abs = (Hp_sharp - H0p_sharp).abs_upper()
        print(f"  |Φ'(z_mid)|        = {Phi_p_sharp_abs.str(8)}")

        # Tight Φ' chunk bound
        t0 = time.time()
        bound = bound_Phi_prime_on_chunk_direct(
            z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=PREC, verbose=True,
        )
        t1 = time.time()
        print(f"  η²-aware bound     = {bound.str(8)}")
        ratio = bound / Phi_p_sharp_abs
        print(f"  bound/sharp ratio  = {ratio.str(8)}× (looseness factor)")

        # Compare to loose triangle (= M_Hp_chunk + M_H0p_chunk)
        from h_eta_prime_chunk_bound import bound_H_eta_prime_on_chunk
        from d_helpers import bound_H0_prime_on_chunk
        M_Hp = bound_H_eta_prime_on_chunk(
            z_ball, P_plus, Pp_plus, Q_minus, Qp_minus,
            L_outer=8, n_panels=8, n_gl=20, prec=PREC,
        )
        M_H0p = bound_H0_prime_on_chunk(z_ball)
        loose = M_Hp + M_H0p
        print(f"  loose triangle     = {loose.str(8)}")
        improv = loose / bound
        print(f"  improvement vs triangle: {improv.str(8)}× tighter")
        print(f"  time: {t1-t0:.2f}s")

    print("\n" + "=" * 72)
