#!/usr/bin/env python3
"""
Generate the three illustrative Grothendieck exposition figures:

  1. matrix_heatmap.png
  2. vector_solution.png
  3. projection_partition.png

The toy instance is a 6 x 6 integer bilinear optimization problem

    max_{eps_i, delta_j in {+-1}} sum_ij A_ij eps_i delta_j.

For the vector plot we use the 2D vector relaxation

    max_{unit u_i, unit v_j in R^2} sum_ij A_ij <u_i, v_j>.

The cached angles below are the result of scipy.optimize.differential_evolution
with seed=2, aligned by a reflection/rotation so that u_3 points east.  Running
with --solve recomputes them.

The final partition plot is intentionally a didactic schematic: it uses a fixed
cubic curve and hand-placed projected points so the rounded signs are legible.
It is not meant to be a faithful random Gaussian projection from the previous
2D angle solution.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap


# -----------------------------------------------------------------------------
# Toy instance
# -----------------------------------------------------------------------------

A = np.array(
    [
        [ 2,  2,  2,  3,  0, -3],
        [ 3,  0,  0, -1,  2,  1],
        [-2,  0,  1,  0,  0, -3],
        [-1,  3,  2, -1, -1, -1],
        [-2, -2, -2, -1, -2, -1],
        [ 0, -2,  3,  0,  1,  2],
    ],
    dtype=float,
)

# Rounded signs used in the partition picture.  This assignment has score 30.
EPS = np.array([ 1, -1,  1,  1,  1, -1], dtype=int)
DELTA = np.array([-1,  1,  1,  1, -1, -1], dtype=int)

# Cached optimizer result before visual alignment.
# Objective value: 35.5509915350...
CACHED_THETA_U_RAW = np.array([0.2289, 1.9976, -0.8042, -0.4479, -2.0621, 1.8579])
CACHED_THETA_V_RAW = np.array([1.6642, -0.1609, 0.6580, 0.3573, 1.7824, 2.4217])


# -----------------------------------------------------------------------------
# Utilities
# -----------------------------------------------------------------------------

def vector_score(theta_u: np.ndarray, theta_v: np.ndarray) -> float:
    """2D vector-relaxation objective for angles theta_u, theta_v."""
    return float(np.sum(A * np.cos(theta_u[:, None] - theta_v[None, :])))


def sign_score(eps: np.ndarray, delta: np.ndarray) -> float:
    """Integer sign objective."""
    return float(np.sum(A * eps[:, None] * delta[None, :]))


def solve_2d_vector_relaxation(seed: int = 2) -> tuple[np.ndarray, np.ndarray]:
    """Recompute a good 2D vector solution via nonconvex angle optimization."""
    from scipy.optimize import differential_evolution

    def objective(x: np.ndarray) -> float:
        return -vector_score(x[:6], x[6:])

    result = differential_evolution(
        objective,
        bounds=[(-np.pi, np.pi)] * 12,
        seed=seed,
        tol=1e-9,
        maxiter=1000,
        popsize=15,
        polish=True,
        workers=1,
    )
    return result.x[:6], result.x[6:]


def align_for_display(theta_u_raw: np.ndarray, theta_v_raw: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """
    Reflect and rotate the angles so u_3 points to the right.

    This does not change any dot products.  It just makes the plot easier to read.
    """
    anchor = theta_u_raw[2]
    theta_u = -theta_u_raw + anchor
    theta_v = -theta_v_raw + anchor
    return theta_u, theta_v


def unit_points(theta: np.ndarray) -> np.ndarray:
    return np.column_stack([np.cos(theta), np.sin(theta)])


def savefig(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(path, dpi=240, bbox_inches="tight", pad_inches=0.12)
    plt.close()


# -----------------------------------------------------------------------------
# Figure 1: heatmap of integer weights
# -----------------------------------------------------------------------------

def make_matrix_heatmap(outdir: Path) -> None:
    colors = ["#497f9f", "#f7f7f7", "#f0b949"]
    cmap = LinearSegmentedColormap.from_list("soft_blue_white_gold", colors, N=256)

    fig, ax = plt.subplots(figsize=(7.2, 6.1))
    im = ax.imshow(A, cmap=cmap, vmin=-3, vmax=3)

    ax.set_title(r"integer weights $a_{ij}$", fontsize=22, pad=18, fontweight="normal")
    ax.set_xticks(np.arange(6))
    ax.set_yticks(np.arange(6))
    ax.set_xticklabels([rf"$v_{j}$" for j in range(1, 7)], fontsize=16)
    ax.set_yticklabels([rf"$u_{i}$" for i in range(1, 7)], fontsize=16)

    ax.set_xticks(np.arange(-0.5, 6, 1), minor=True)
    ax.set_yticks(np.arange(-0.5, 6, 1), minor=True)
    ax.grid(which="minor", color="white", linewidth=3)
    ax.tick_params(which="minor", bottom=False, left=False)
    ax.tick_params(axis="both", length=0)

    for spine in ax.spines.values():
        spine.set_visible(False)

    for i in range(6):
        for j in range(6):
            val = int(A[i, j])
            text_color = "white" if abs(val) >= 3 else "#222222"
            ax.text(
                j,
                i,
                str(val),
                ha="center",
                va="center",
                fontsize=17,
                fontweight="bold",
                color=text_color,
            )

    savefig(outdir / "matrix_heatmap.png")


# -----------------------------------------------------------------------------
# Figure 2: vector solution on a circle
# -----------------------------------------------------------------------------

def make_vector_solution(
    outdir: Path,
    solve: bool = False,
    u_marker_size: float = 100,
    v_marker_size: float = 170,
) -> tuple[np.ndarray, np.ndarray]:
    if solve:
        theta_u_raw, theta_v_raw = solve_2d_vector_relaxation(seed=2)
    else:
        theta_u_raw, theta_v_raw = CACHED_THETA_U_RAW, CACHED_THETA_V_RAW

    theta_u, theta_v = align_for_display(theta_u_raw, theta_v_raw)
    U = unit_points(theta_u)
    V = unit_points(theta_v)
    score = vector_score(theta_u, theta_v)

    blue = "#477fa3"
    pale_blue = "#d7ebf3"
    orange = "#e66e52"
    pale_orange = "#fff1e4"
    grey = "#e7e7e7"
    dark = "#222222"

    fig, ax = plt.subplots(figsize=(7.2, 6.2))
    ax.set_aspect("equal")
    ax.set_xlim(-1.45, 1.55)
    ax.set_ylim(-1.45, 1.45)
    ax.axis("off")

    circle = plt.Circle((0, 0), 1.0, edgecolor=grey, facecolor="none", linewidth=3)
    ax.add_patch(circle)
    ax.axhline(0, color=grey, linewidth=2)
    ax.axvline(0, color=grey, linewidth=2)

    for i, p in enumerate(U, start=1):
        ax.plot([0, p[0]], [0, p[1]], color=blue, linewidth=2.2)
        ax.scatter(
            [p[0]], [p[1]], s=u_marker_size, marker="o",
            facecolors=pale_blue, edgecolors=blue, linewidths=2.8, zorder=3,
        )
        ax.text(p[0] * 1.13, p[1] * 1.13, rf"$u_{i}$", color=blue, fontsize=10, fontweight="bold")

    for j, p in enumerate(V, start=1):
        ax.plot([0, p[0]], [0, p[1]], color=orange, linewidth=2.2)
        ax.scatter(
            [p[0]], [p[1]], s=v_marker_size, marker="^",
            facecolors=pale_orange, edgecolors=orange, linewidths=2.8, zorder=4,
        )
        ax.text(p[0] * 1.18, p[1] * 1.18, rf"$v_{j}$", color=orange, fontsize=10, fontweight="bold")

    # Small custom legend at the top-left.
    ax.scatter([-1.36], [1.47], s=170, marker="o", facecolors=pale_blue, edgecolors=blue, linewidths=2.6, clip_on=False)
    ax.text(-1.25, 1.46, r"left vectors $u_i$", fontsize=13, va="center", clip_on=False)
    ax.scatter([0.6], [1.47], s=185, marker="^", facecolors=pale_orange, edgecolors=orange, linewidths=2.6, clip_on=False)
    ax.text(0.7, 1.46, r"right vectors $v_j$", fontsize=13, va="center", clip_on=False)

    # ax.text(-1.2, -1.32, rf"vector score $\approx$ {score:.2f}", fontsize=16, color=dark)
    savefig(outdir / "vector_solution.png")
    return theta_u, theta_v


# -----------------------------------------------------------------------------
# Figure 3: projection + partition schematic
# -----------------------------------------------------------------------------

def make_projection_partition(outdir: Path) -> None:
    navy = "#172b49"
    light_blue = "#dcecf4"
    cream = "#fff6e6"
    gold = "#f3b546"
    dark = "#222222"

    # Hand-placed projected points, chosen only to make the schematic readable.
    pts_u = np.array([
        [1.10, 1.03],    # u1 +
        [-1.85, -0.55],  # u2 -
        [2.10, 1.25],    # u3 +
        [1.95, 1.34],    # u4 +
        [0.70, -0.12],   # u5 +
        [-1.98, -0.72],  # u6 -
    ])
    pts_v = np.array([
        [-1.65, -0.40],  # v1 -
        [1.65, 1.50],    # v2 +
        [0.24, 0.68],    # v3 +
        [0.88, 0.94],    # v4 +
        [-1.75, -0.34],  # v5 -
        [-1.88, -0.97],  # v6 -
    ])

    def boundary(x: np.ndarray) -> np.ndarray:
        return 0.35 * (x**3 - 3 * x)

    fig, ax = plt.subplots(figsize=(8.0, 5.9))
    ax.set_xlim(-3.0, 3.0)
    ax.set_ylim(-1.8, 2.3)
    ax.axis("off")

    xs = np.linspace(-3.1, 3.1, 800)
    ys = boundary(xs)
    ax.fill_between(xs, ys, 3.0, color=cream, zorder=0)
    ax.fill_between(xs, -3.0, ys, color=light_blue, zorder=0)
    ax.axhline(0, color="white", linewidth=1.5, zorder=1)
    ax.axvline(0, color="white", linewidth=1.5, zorder=1)
    ax.plot(xs, ys, color=navy, linewidth=3.2, zorder=2)

    # Draw points; marker color encodes the rounded sign.
    for i, (x, y) in enumerate(pts_u, start=1):
        sgn = EPS[i - 1]
        fill = gold if sgn > 0 else navy
        ax.scatter([x], [y], s=210, marker="o", facecolors=fill, edgecolors="white", linewidths=2.4, zorder=4)
        ax.text(x + 0.08, y + 0.08, rf"$u_{i}$", fontsize=14, color=dark, fontweight="bold", zorder=5)

    for j, (x, y) in enumerate(pts_v, start=1):
        sgn = DELTA[j - 1]
        fill = gold if sgn > 0 else navy
        ax.scatter([x], [y], s=250, marker="^", facecolors=fill, edgecolors="white", linewidths=2.4, zorder=4)
        ax.text(x + 0.08, y + 0.08, rf"$v_{j}$", fontsize=14, color=dark, fontweight="bold", zorder=5)

    ax.text(-2.75, 1.95, r"$+1$", fontsize=28, color=navy)
    ax.text(2.45, -1.42, r"$-1$", fontsize=28, color=navy)
    ax.text(0.32, 1.98, r"$y = 0.35(x^3 - 3x)$", fontsize=18, color=navy)
    ax.text(-2.85, -1.58, rf"rounded score $= {int(sign_score(EPS, DELTA))}$", fontsize=18, color=dark)

    savefig(outdir / "projection_partition.png")


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=Path("grothendieck_figures"))
    parser.add_argument("--solve", action="store_true", help="recompute the nonconvex 2D vector relaxation with scipy")
    parser.add_argument("--u-marker-size", type=float, default=20, help="scatter size for u_i circles in vector_solution.png")
    parser.add_argument("--v-marker-size", type=float, default=20, help="scatter size for v_j triangles in vector_solution.png")
    args = parser.parse_args()

    make_matrix_heatmap(args.outdir)
    make_vector_solution(
        args.outdir,
        solve=args.solve,
        u_marker_size=args.u_marker_size,
        v_marker_size=args.v_marker_size,
    )
    make_projection_partition(args.outdir)

    print(f"wrote figures to {args.outdir.resolve()}")
    print(f"integer rounded score: {sign_score(EPS, DELTA):.0f}")
    print(f"cached 2D vector score: {vector_score(*align_for_display(CACHED_THETA_U_RAW, CACHED_THETA_V_RAW)):.4f}")


if __name__ == "__main__":
    main()