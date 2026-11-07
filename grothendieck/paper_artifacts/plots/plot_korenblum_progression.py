"""Two simple paper-ready plots for the Korenblum harness.

  Plot 1: c_value per certified generation (step plot).
  Plot 2: c_value improvement over Wang's published baseline (c = 1777/5000).

The Korenblum constant κ satisfies the lower bound `ValidKorenblumBound c`
emitted by each candidate; larger c means a stronger statement. The seed
V0 ships with c = 1777/5000 = 0.3554 (Wang 2025, PAMS 153(3)). Subsequent
generations widen the certified c.

The harness logs every candidate compile to `Refinement_Log/log.jsonl`;
many entries are re-certifications of the same candidate, so we dedupe
by candidate path and keep only the first pass per version. Most
generations (V1..V48, V53..V63, V65) carry the same c as their parent —
they refactor the proof but do not push the constant. To keep the
plot legible we draw a step trajectory across **all** passing
generations but only label the x-axis at the iterations where c
strictly increased ("mathematically significant" improvements). Each
such improvement is marked with a red dot.

Edit / rerun this file; outputs land alongside it in paper_artifacts/plots/.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import matplotlib.pyplot as plt

_HERE = Path(__file__).resolve().parent
LOG = Path(__file__).resolve().parents[3] / "korenblum" / "ProofRefinement" / "Korenblum" / "Refinement_Log" / "log.jsonl"

OUT_C = _HERE / "korenblum_c_progression.pdf"
OUT_GAP = _HERE / "korenblum_c_improvement.pdf"

C_PAPER = Fraction(1777, 5000)


def load_unique_passes():
    seen: dict[str, dict] = {}
    order: list[str] = []
    with open(LOG) as f:
        for line in f:
            d = json.loads(line)
            if not d.get("pass"):
                continue
            cand = d.get("candidate")
            if cand in seen:
                continue
            seen[cand] = d
            order.append(cand)
    rows = []
    for cand in order:
        d = seen[cand]
        cv = d["def_vals"]["c_value"]
        rows.append({
            "label": Path(cand).stem,
            "c_str": cv,
            "c": Fraction(cv),
        })
    return rows


def main():
    rows = load_unique_passes()
    if not rows:
        raise SystemExit(f"No passing entries in {LOG}")

    xs = list(range(len(rows)))
    cs = [float(r["c"]) for r in rows]
    gaps = [float(r["c"] - C_PAPER) for r in rows]

    # Identify improvement events: indices where c strictly increased.
    improv_idx = []
    prev = None
    for i, r in enumerate(rows):
        if prev is None or r["c"] > prev:
            improv_idx.append(i)
            prev = r["c"]

    improv_labels = [rows[i]["label"] for i in improv_idx]
    improv_cs = [cs[i] for i in improv_idx]
    improv_gaps = [gaps[i] for i in improv_idx]

    # Genuine novel mathematical insights — strict classification.
    #
    # Most c-improvement events refine numerics inside Wang's eq (15) frame
    # (V49–V52) or extend an existing window architecture by adding more
    # modes (V67, V68). Only two events introduce *new* mathematical
    # structure into the proof:
    #
    #   V64 (sprint 083): per-mode τ-partition with sqrt endpoints and
    #                     direct annulus-slice closure, bypassing Wang's
    #                     eq (15) chain entirely.
    #   V66 (sprint 088): mixed-kernel multi-window reducer, allowing
    #                     branch1 (Wang eq (5)) fallback windows
    #                     alongside per-mode windows.
    #
    # V0 is the seed (Wang 2025 baseline), not an insight.
    NOVEL_LABELS = {"V64", "V66"}
    novel_idx = [i for i, r in enumerate(rows) if r["label"] in NOVEL_LABELS]
    novel_gaps = [gaps[i] for i in novel_idx]

    # ---------------- Plot 1: c_value ----------------
    fig1, ax1 = plt.subplots(figsize=(10, 6))
    ax1.step(xs, cs, where="post", linewidth=1.2, color="C0")
    ax1.plot(improv_idx, improv_cs, "o", color="red", markersize=7,
             zorder=5, label="improvement")
    ax1.set_title(
        r"Korenblum constant $\kappa$: certified lower bound $c$ over generations",
        fontsize=13,
    )
    ax1.set_xlabel("generation", fontsize=12)
    ax1.set_ylabel(r"certified lower bound on $\kappa$", fontsize=12)
    ax1.set_xticks(improv_idx)
    ax1.set_xticklabels(improv_labels, fontsize=9, rotation=45, ha="right")
    ax1.set_xlim(-0.5, len(rows) - 0.5)
    ax1.grid(True, which="both", alpha=0.3)
    ax1.legend(loc="lower right", fontsize=10)
    plt.tight_layout()
    fig1.savefig(OUT_C, bbox_inches="tight")
    fig1.savefig(OUT_C.with_suffix(".png"), dpi=140, bbox_inches="tight")
    plt.close(fig1)
    print(f"Wrote {OUT_C} (and .png)")

    # ---------------- Plot 2: c improvement over paper baseline ----------------
    novel_set = set(novel_idx)
    standard_idx = [i for i in xs if i not in novel_set]
    standard_gaps = [gaps[i] for i in standard_idx]

    fig2, ax2 = plt.subplots(figsize=(10, 6))
    ax2.plot(xs, gaps, "-", linewidth=1.2, color="green", zorder=1)
    ax2.plot(standard_idx, standard_gaps, "o", color="green", markersize=7,
             zorder=4, label="standard iteration (minor improvements)")
    ax2.plot(novel_idx, novel_gaps, "o", color="red", markersize=7,
             zorder=5, label="novel mathematical insight")
    ax2.set_title(
        r"$\mathcal{K}_K$ improvement over Wang 2025 baseline "
        r"(red = novel mathematical breakthroughs)",
        fontsize=17,
    )
    ax2.set_xlabel("Iteration", fontsize=17)
    ax2.set_ylabel(r"$\mathcal{K}_K$ improvement over baseline", fontsize=17)
    tick_stride = 5
    tick_idx = sorted(set(list(range(0, len(rows), tick_stride)) + [len(rows) - 1]))
    ax2.set_xticks(tick_idx)
    ax2.set_xticklabels([str(i) for i in tick_idx], fontsize=13)
    ax2.tick_params(axis="y", labelsize=13)
    ax2.set_xlim(-0.5, len(rows) - 0.5)
    ax2.grid(True, which="both", alpha=0.3)
    ax2.legend(loc="upper left", fontsize=16)
    plt.tight_layout()
    fig2.savefig(OUT_GAP, bbox_inches="tight")
    fig2.savefig(OUT_GAP.with_suffix(".png"), dpi=140, bbox_inches="tight")
    plt.close(fig2)
    print(f"Wrote {OUT_GAP} (and .png)")

    print()
    print(f"total passing generations: {len(rows)}")
    print(f"improvement events:       {len(improv_idx)}")
    print()
    print(f"{'V':>5}  {'iter':>5}  {'c (rational)':>16}  {'c (float)':>12}  {'Δc':>14}")
    for i in improv_idx:
        r = rows[i]
        print(f"{r['label']:>5}  {i:>5}  {r['c_str']:>16}  "
              f"{cs[i]:>12.7f}  {gaps[i]:>14.7f}")


if __name__ == "__main__":
    main()
