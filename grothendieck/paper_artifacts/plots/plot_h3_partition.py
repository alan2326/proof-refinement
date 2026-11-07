"""Partition of the plane induced by the physicist's Hermite h_3.

Above the curve y = h_3(x) → orange.
Below → black.
Outside the inscribed disk → transparent (image shape is circular, not rectangular).
No axes, no labels, no margins — just the partition image.
"""
from __future__ import annotations

from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt

_HERE = Path(__file__).resolve().parent
OUT = _HERE / "h3_partition_circle.png"


def h3(x: np.ndarray) -> np.ndarray:
    # Physicist's normalized Hermite: H_3(x) = 8x^3 - 12x,
    # normalized by sqrt(2^3 · 3! · sqrt(pi)) = sqrt(48 sqrt(pi)).
    norm = np.sqrt(48.0 * np.sqrt(np.pi))
    return (8.0 * x**3 - 12.0 * x) / norm


def main():
    x_lim = 2.5
    y_lim = 2.5
    n = 2000

    xs = np.linspace(-x_lim, x_lim, n)
    ys = np.linspace(-y_lim, y_lim, n)
    X, Y = np.meshgrid(xs, ys)
    above = Y > h3(X)

    rgba = np.zeros((*above.shape, 4), dtype=np.float32)
    rgba[above]  = (0.91, 0.51, 0.18, 1.0)   # warm pumpkin orange
    rgba[~above] = (0.10, 0.10, 0.12, 1.0)   # soft charcoal

    R = min(x_lim, y_lim)
    inside = (X**2 + Y**2) <= R * R
    rgba[..., 3] = inside.astype(np.float32)

    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(rgba, origin="lower", extent=(-x_lim, x_lim, -y_lim, y_lim),
              interpolation="nearest")
    ax.set_axis_off()
    fig.patch.set_alpha(0.0)
    fig.subplots_adjust(left=0, right=1, top=1, bottom=0)
    fig.savefig(OUT, dpi=200, bbox_inches="tight", pad_inches=0,
                transparent=True)
    plt.close(fig)
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
