"""
Sweep r and eta over the certified Lemma 5.4 paper-proof pipeline; print Cr,
Cr·p², input Δ = H_eta(i)/i - γ₀, and whether γ_lower > γ_0 was certified.

The point: at r=23/25, η=0.01 the paper proof fails Step 9 because
Cr·p² ≈ 6·10⁷ swamps the input Δ ≈ 5·10⁻⁸. Tighter (smaller-r) parameters
shrink Cr; we want to find an (r, η) where γ_lower > γ_0 is certified.
"""

import time

from grothendieck.proof.certified.run_proof import run_certified_proof


CONFIGS = [
    # (eta, r, label)
    (0.01, 0.5,  "r=0.50, η=0.01"),
    (0.01, 0.7,  "r=0.70, η=0.01"),
    (0.01, 0.85, "r=0.85, η=0.01"),
    (0.01, 0.92, "r=0.92, η=0.01  (V0 / paper baseline)"),
    (0.005, 0.5, "r=0.50, η=0.005"),
    (0.05, 0.5,  "r=0.50, η=0.05"),
]


def fmt_arb(s):
    """Compact rendering of arb interval strings."""
    s = str(s)
    return s if len(s) <= 30 else s[:27] + "..."


def main():
    rows = []
    for eta, r, label in CONFIGS:
        print("=" * 70)
        print(f"RUNNING: {label}")
        print("=" * 70)
        t0 = time.time()
        try:
            cert = run_certified_proof(
                eta=eta, r=r, prec=128, verbose=False,
            )
            ok = "PASS" if cert.all_checks_passed else "FAIL"
            failed = [k for k, v in cert.check_details.items() if not v]
            rows.append({
                "label":  label,
                "ok":     ok,
                "M":      fmt_arb(cert.M),
                "R":      fmt_arb(cert.R),
                "p":      fmt_arb(cert.p),
                "Cr":     fmt_arb(cert.C_r),
                "Δ":      fmt_arb(cert.H_eta_i_over_i) + " - γ₀",
                "γ>γ₀":   "✅" if cert.check_details.get("gamma_gt_gamma0") else "❌",
                "imprv":  fmt_arb(cert.improvement_over_baseline),
                "fails":  ",".join(failed) if failed else "-",
                "time":   f"{time.time()-t0:.0f}s",
            })
        except Exception as e:
            rows.append({
                "label": label,
                "ok": "EXCEPTION",
                "fails": str(e)[:80],
                "time": f"{time.time()-t0:.0f}s",
            })

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for r in rows:
        print(f"\n{r['label']}  [{r['ok']}, {r.get('time', '?')}]")
        for k in ("M", "R", "p", "Cr", "imprv", "γ>γ₀", "fails"):
            if k in r:
                print(f"  {k:8s}= {r[k]}")


if __name__ == "__main__":
    main()
