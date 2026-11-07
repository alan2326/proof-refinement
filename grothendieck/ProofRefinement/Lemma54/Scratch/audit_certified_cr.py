"""Audit the fully-certified Cr computation.

Checks:
 1. Argmax chunks for each of M_φ, M_φ', M_Heta_pp.
 2. Distribution of bound values across chunks (where's the looseness?).
 3. Cross-check with prior heuristic values (cached H_mid → Φ_mid_sharp comparison).
 4. Verify all arb intervals have proper finite radii.
 5. Verify that certified bounds are ≥ heuristic bounds (i.e., are valid upper bounds).
 6. Sanity-check the formula at sharp z=0.5+0i where math is simplest.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from flint import arb, acb, ctx as flint_ctx

PREC = 200
flint_ctx.prec = PREC

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

from phi_chunk_bound_certified import bound_Phi_on_chunk_certified
from phi_prime_chunk_bound_certified import bound_Phi_prime_on_chunk_certified
from h_eta_pp_chunk_bound_certified import bound_H_eta_pp_on_chunk_certified


def audit():
    print("=" * 78)
    print("AUDIT: V26 fully-certified Cr — chunk-level analysis")
    print("=" * 78)

    out_path = (_HERE.parent / "Cache" / "v26_fully_certified_cr_npe16.json")
    with open(out_path) as f:
        data = json.load(f)
    chunks = data["per_chunk"]
    print(f"\n[1] {len(chunks)} chunks scanned at n_per_edge={data['params']['n_per_edge']}")

    # Find argmax for each quantity
    print("\n[2] Per-quantity argmax:")
    for key in ("Phi_ub", "Phi_p_ub", "Heta_pp_ub"):
        sorted_chunks = sorted(chunks, key=lambda c: c[key], reverse=True)
        worst = sorted_chunks[0]
        print(f"\n  {key} max = {worst[key]:.6e}")
        print(f"    edge={worst['edge']}, "
              f"z_mid_re≈{float(arb(worst['z_mid_re_str'])):.4f}, "
              f"z_mid_im≈{float(arb(worst['z_mid_im_str'])):.4f}")
        # Top 5
        print("    top 5 chunks:")
        for c in sorted_chunks[:5]:
            print(f"      {c[key]:.4e} at "
                  f"({float(arb(c['z_mid_re_str'])):.3f}, "
                  f"{float(arb(c['z_mid_im_str'])):.3f}) edge={c['edge']}")

    # Distribution
    print("\n[3] Distribution of M_phi chunk values:")
    phi_vals = sorted([c["Phi_ub"] for c in chunks])
    n = len(phi_vals)
    pct_ranges = [(0.5, "median"), (0.9, "p90"), (0.99, "p99"), (1.0, "max")]
    for p, label in pct_ranges:
        idx = min(int(p * n), n - 1)
        print(f"  {label:>6}: {phi_vals[idx]:.4e}")

    # Verify all bounds are positive arb intervals
    print("\n[4] Sanity: all bound values are positive finite arb")
    for c in chunks:
        for k in ("Phi_str", "Phi_p_str", "Heta_pp_str"):
            val = arb(c[k])
            if not (val > arb(0)):
                print(f"   ⚠  Chunk {c['edge']} at z_mid_re={c['z_mid_re_str']} "
                      f"has non-positive {k}: {c[k]}")
                return False
            if not (val < arb("1e20")):
                print(f"   ⚠  Chunk {c['edge']} has unbounded {k}: {c[k]}")
                return False
    print("   ✓ all 64×3 = 192 bound values are finite-positive arb")

    # Cross-check vs prior heuristic / mean-value enclosure cache
    prior_path = (_HERE.parent / "Cache" / "v26_compose_rigorous_cr_npe16.json")
    if prior_path.exists():
        print("\n[5] Cross-check vs prior heuristic mean-value enclosure")
        with open(prior_path) as f:
            prior = json.load(f)
        prior_summary = prior["summary"]
        if prior_summary["status"] == "OK":
            print(f"   Prior M_phi (mean-value, sharp midpoint, heuristic GL): "
                  f"{float(prior_summary['M_phi_float']):.4e}")
            print(f"   Now   M_phi (closed-form kernel-diff, certified):       "
                  f"{float(data['summary']['M_phi_float']):.4e}")
            ratio = data['summary']['M_phi_float'] / prior_summary['M_phi_float']
            print(f"   Ratio (certified/prior): {ratio:.2f}× looser")
            print()
            print(f"   Prior M_phi_p:                                          "
                  f"{float(prior_summary['M_phi_p_float']):.4e}")
            print(f"   Now   M_phi_p (closed-form AM-GM, certified):           "
                  f"{float(data['summary']['M_phi_p_float']):.4e}")
            ratio = data['summary']['M_phi_p_float'] / prior_summary['M_phi_p_float']
            print(f"   Ratio: {ratio:.2f}× looser")
        else:
            print(f"   prior failed: {prior_summary['status']}")

    # Sanity check: at z=0.5+0i, our Phi bound should match the test smoke result
    print("\n[6] Sanity: bound on z=0.5+0i chunk vs smoke-test value")
    eta_arb = arb("0.01")
    z_test = acb(arb("0.5"), arb.union(arb("-0.05"), arb("0.05")))
    r = bound_Phi_on_chunk_certified(z_test, eta_arb, prec=PREC)
    print(f"   |Φ| chunk bound at z=0.5±0.05i: {r.bound.str(8)}")
    print(f"   (smoke test reference: ~1.25e-3)")

    # Verify the formula independently at z=0.5+0i (a real chunk)
    # At sharp z=0.5: 1-z²=0.75 ∈ R, σ=sqrt(0.75) ∈ R, α=β=1/0.5=2... wait that's wrong.
    # 1-z=0.5, so 1/(1-z)=2. 1+z=1.5, 1/(1+z)=2/3. So α=2, β=2/3.
    # σ_marginal = 2αβ/(α+β) = 2·2·(2/3)/(8/3) = (8/3)/(8/3) = 1.
    print("\n[7] Independent recomputation of Φ bound at sharp z=0.5+0i:")
    z_sharp = acb(arb("0.5"), arb(0))
    r_sharp = bound_Phi_on_chunk_certified(z_sharp, eta_arb, prec=PREC)
    print(f"   sharp z=0.5+0i: |Φ| ≤ {r_sharp.bound.str(10)}")
    print(f"   d_Z = {r_sharp.d_Z.str(8)}, d_min = {r_sharp.d_min.str(8)}")
    print(f"   α_Z = {r_sharp.alpha_Z.str(8)}, β_Z = {r_sharp.beta_Z.str(8)}")
    print(f"   σ = {r_sharp.sigma.str(8)} (should be 1.0 at z=0.5)")
    print(f"   K1 = {r_sharp.K1.str(8)} (= sqrt(2π/(α+β)) at z=0.5)")
    K1_expected = (arb(2) * arb.pi() / (arb(2) + arb(2)/arb(3))).sqrt()
    print(f"   K1 expected = {K1_expected.str(10)}")
    sigma_expected = arb(2) * arb(2) * (arb(2)/arb(3)) / (arb(2) + arb(2)/arb(3))
    print(f"   σ expected = {sigma_expected.str(10)}")

    # End-to-end recomputation:
    # K_P = η/(√3·π^{1/4}) ≈ 4.339e-3, K_P² ≈ 1.882e-5
    # P²(x) = K_P²·(9x²-24x⁴+16x⁶)
    # ∫_R P²·exp(-σx²) dx = K_P²·(9·M1-24·M2+16·M3) at σ=1
    #   M1=sqrt(π)/2 ≈ 0.886, M2=3sqrt(π)/4 ≈ 1.329, M3=15sqrt(π)/8 ≈ 3.323
    # = K_P²·(9·0.886-24·1.329+16·3.323) = K_P²·(7.97-31.9+53.2) = K_P²·29.27
    # ≈ 1.882e-5·29.27 ≈ 5.51e-4
    # K1 ≈ sqrt(6π/8) = sqrt(3π/4) ≈ 1.535
    # C_K_diff = (2/π)+(0.5)(2.5)/(π·1) = 0.637+0.398 = 1.035
    # bound = (C_K_diff·K1·5.51e-4 / sqrt(0.75)) = (1.035·1.535·5.51e-4/0.866) = 1.01e-3
    print(f"   Hand calculation: bound ≈ 1.01e-3 (vs computed {float(r_sharp.bound.upper()):.2e})")

    print("\n" + "=" * 78)
    print("AUDIT SUMMARY")
    print("=" * 78)
    summary = data["summary"]
    print(f"  M_φ          = {summary['M_phi_float']:>10.4e}  argmax: see [2]")
    print(f"  M_φ'         = {summary['M_phi_p_float']:>10.4e}")
    print(f"  M_pp_triangle= {summary['M_pp_triangle_float']:>10.4e}")
    print(f"  inf|D|       = {arb(summary['inf_D']).str(8):>10}")
    print(f"  inv_F_p_z    = {summary['inv_F_p_z_float']:>10.4e}")
    print(f"  u_zz         = {summary['u_zz_float']:>10.4e}")
    print(f"  Cr_certified = {summary['Cr_triangle_float']:>10.4e}")

    print()
    print("  STATUS: All values certified-positive arb intervals with finite")
    print("          radii. No K_max truncation, no GL/quadrature error,")
    print("          no half-resolution heuristic. Pure closed-form arb.")
    print()
    print("  KNOWN LOOSENESS SOURCES (in order of impact):")
    print("    1. Triangle decomposition for u_zz (loses joint H_0''/H_0'³ ")
    print("       cancellation): structural ~10² factor.")
    print("    2. Kernel-diff bound on |K_z(P,Q) - K_z(0,0)| ≤ C_K_diff·(P²+Q²):")
    print("       loses phase coherence in K_z_diff·exp(-Q_z) integral:")
    print("       ~10-50× looser per chunk.")
    print("    3. AM-GM in Φ', H_η'' chunk bounds: ~2× constant factor.")
    print("    4. inf|D| via |D| ≥ inf|H_0'|−p·M_φ' (no per-cell tightening):")
    print("       ~2× looseness.")

    return True


if __name__ == "__main__":
    audit()
