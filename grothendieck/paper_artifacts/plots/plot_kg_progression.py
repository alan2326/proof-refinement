"""Two simple paper-ready plots — values only, no annotations.

  Plot 1: Cr_val per iteration (log scale).
  Plot 2: K_G improvement over baseline = π/(2·ln(1+√2)) − 1/c_{f,g}.

c_{f,g} = (2/π)·γ where γ = γ_0 + Δγ ≥ γ_0 = atanh(1/√2) = ln(1+√2).
Equivalently c_{f,g} = c_baseline + ΔK_G with c_baseline = (2/π)·γ_0.
The Krivine constant π/(2·ln(1+√2)) = 1/c_baseline ≈ 1.7822 is the
classical upper bound on K_G; each iteration tightens 1/c_{f,g} below it.

V27 is excluded. V25, V26 use the patched Cr (≈ 0.3734) from the
post-K_max round-3 audit, with their ΔK_G recomputed via the certified
pipeline (cached in `v25_v26_patched.json`).

Edit / rerun this file; outputs land alongside it in paper_artifacts/plots/.
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib.pyplot as plt
from flint import arb, ctx as flint_ctx

PREC = 256
flint_ctx.prec = PREC

_HERE = Path(__file__).resolve().parent
REPO = _HERE.parents[1]  # paper_artifacts/plots/ → repo root
DATA = REPO / "ProofRefinement" / "Lemma54" / "Scratch" / "cr_progression_data.json"
PATCH = _HERE / "v25_v26_patched.json"

OUT_CR = _HERE / "cr_progression.pdf"
OUT_GAP = _HERE / "kg_improvement.pdf"


def main():
    raw = json.load(open(DATA))
    rows = {r["idx"]: r for r in raw["candidates"]}

    # Override V25, V26 with patched values; drop V27 entirely.
    patch = json.load(open(PATCH))
    for k, p in patch.items():
        idx = int(k[1:])
        rows[idx] = {
            "idx": idx,
            "Cr_str": p["Cr_str"],
            "Cr_float": p["Cr_float"],
            "p_x": p["p_x"],
            "delta_gamma_str": p["delta_gamma_str"],
            "delta_gamma_float": p["delta_gamma_float"],
            "delta_KG_str": p["delta_KG_str"],
            "delta_KG_float": p["delta_KG_float"],
        }
    rows.pop(27, None)

    idxs = sorted(rows)
    cr_arbs = [arb(rows[i]["Cr_str"]) for i in idxs]
    cr_lower = [float(c.lower()) for c in cr_arbs]

    # ----- K_G improvement over baseline (in arb) -----
    gamma_0 = (arb(1) / arb(2).sqrt()).atanh()
    two_over_pi = arb(2) / arb.pi()
    c_baseline = two_over_pi * gamma_0
    krivine = arb(1) / c_baseline

    gap_arbs = []
    for i in idxs:
        delta_KG = arb(rows[i]["delta_KG_str"])
        c_fg = c_baseline + delta_KG
        # Inversion-stability guard
        assert c_fg.lower() > arb("1/4"), f"V{i}: c_fg too close to zero"
        gap = krivine - arb(1) / c_fg
        gap_arbs.append(gap)

    gap_lowers = [float(g.abs_lower()) for g in gap_arbs]

    # ---------------- Plot 1: Cr ----------------
    fig1, ax1 = plt.subplots(figsize=(10, 6))
    ax1.set_yscale("log")
    ax1.plot(idxs, cr_lower, "-o", markersize=5, linewidth=1.2)
    ax1.set_title(r"$C_r$ progression over iterations", fontsize=13)
    ax1.set_xlabel("iteration", fontsize=12)
    ax1.set_ylabel(r"$C_r$  (log scale)", fontsize=12)
    ax1.set_xticks(idxs)
    ax1.tick_params(axis="x", labelsize=8)
    ax1.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    fig1.savefig(OUT_CR, bbox_inches="tight")
    fig1.savefig(OUT_CR.with_suffix(".png"), dpi=140, bbox_inches="tight")
    plt.close(fig1)
    print(f"Wrote {OUT_CR} (and .png)")

    # ---------------- Plot 2: K_G improvement ----------------
    fig2, ax2 = plt.subplots(figsize=(10, 6))
    ax2.set_yscale("log")
    ax2.plot(idxs, gap_lowers, "-o", markersize=5, linewidth=1.2, color="C2")
    ax2.set_title(r"$\mathcal{K}_G$ improvement over Krivine baseline", fontsize=13)
    ax2.set_xlabel("iteration", fontsize=12)
    ax2.set_ylabel(r"$\mathcal{K}_G$ improvement over baseline", fontsize=12)
    ax2.set_xticks(idxs)
    ax2.tick_params(axis="x", labelsize=8)
    ax2.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    fig2.savefig(OUT_GAP, bbox_inches="tight")
    fig2.savefig(OUT_GAP.with_suffix(".png"), dpi=140, bbox_inches="tight")
    plt.close(fig2)
    print(f"Wrote {OUT_GAP} (and .png)")

    # Diagnostic table
    print()
    print(f"{'V':>3}  {'Cr':>14}  {'ΔK_G improv.':>16}")
    for i in idxs:
        print(f"V{i:>2}  {cr_lower[idxs.index(i)]:>14.4e}  "
              f"{gap_lowers[idxs.index(i)]:>16.4e}")


if __name__ == "__main__":
    main()
