"""K_G improvement plot with novel-math iterations highlighted in red.

Variant of `plot_kg_progression.py` (plot 2 only). Iterations whose entry in
`cr_progression_data.json` has `"is_new_idea": true` are drawn as red dots;
all other iterations are drawn in the default colour. V27 is excluded; V25,
V26 use the patched values from `v25_v26_patched.json`.
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib.pyplot as plt
from flint import arb, ctx as flint_ctx

PREC = 256
flint_ctx.prec = PREC

_HERE = Path(__file__).resolve().parent
REPO = _HERE.parents[1]
DATA = REPO / "ProofRefinement" / "Lemma54" / "Scratch" / "cr_progression_data.json"
PATCH = _HERE / "v25_v26_patched.json"

OUT = _HERE / "kg_improvement_breakthroughs.pdf"


def main():
    raw = json.load(open(DATA))
    rows = {r["idx"]: r for r in raw["candidates"]}

    patch = json.load(open(PATCH))
    for k, p in patch.items():
        idx = int(k[1:])
        rows[idx] = {
            **rows.get(idx, {"idx": idx}),
            "Cr_str": p["Cr_str"],
            "Cr_float": p["Cr_float"],
            "p_x": p["p_x"],
            "delta_gamma_str": p["delta_gamma_str"],
            "delta_gamma_float": p["delta_gamma_float"],
            "delta_KG_str": p["delta_KG_str"],
            "delta_KG_float": p["delta_KG_float"],
            "is_new_idea": rows.get(idx, {}).get("is_new_idea", False),
        }
    rows.pop(27, None)

    idxs = sorted(rows)

    gamma_0 = (arb(1) / arb(2).sqrt()).atanh()
    two_over_pi = arb(2) / arb.pi()
    c_baseline = two_over_pi * gamma_0
    krivine = arb(1) / c_baseline

    gap_lowers = []
    for i in idxs:
        delta_KG = arb(rows[i]["delta_KG_str"])
        c_fg = c_baseline + delta_KG
        assert c_fg.lower() > arb("1/4"), f"V{i}: c_fg too close to zero"
        gap = krivine - arb(1) / c_fg
        gap_lowers.append(float(gap.abs_lower()))

    new_idea = [bool(rows[i].get("is_new_idea", False)) for i in idxs]

    fig, ax = plt.subplots(figsize=(10, 6))
    ax.set_yscale("log")
    ax.plot(idxs, gap_lowers, "-", color="C2", linewidth=1.2, zorder=1)

    base_xs = [i for i, nb in zip(idxs, new_idea) if not nb]
    base_ys = [g for g, nb in zip(gap_lowers, new_idea) if not nb]
    ax.plot(base_xs, base_ys, "o", color="C2", markersize=5, zorder=2,
            label="standard iteration (minor improvements)")

    new_xs = [i for i, nb in zip(idxs, new_idea) if nb]
    new_ys = [g for g, nb in zip(gap_lowers, new_idea) if nb]
    ax.plot(new_xs, new_ys, "o", color="red", markersize=7, zorder=3,
            label="novel mathematical insight")

    ax.set_title(r"$\mathcal{K}_G$ improvement over Krivine baseline "
                 r"(red = novel mathematical breakthroughs)",
                 fontsize=17)
    ax.set_xlabel("Iteration", fontsize=17)
    ax.set_ylabel(r"$\mathcal{K}_G$ improvement over baseline", fontsize=17)
    ax.set_xticks(idxs)
    ax.tick_params(axis="x", labelsize=8)
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="best", fontsize=17)

    plt.tight_layout()
    fig.savefig(OUT, bbox_inches="tight")
    fig.savefig(OUT.with_suffix(".png"), dpi=140, bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote {OUT} (and .png)")
    print()
    print(f"Highlighted iterations (is_new_idea=true): {new_xs}")


if __name__ == "__main__":
    main()
