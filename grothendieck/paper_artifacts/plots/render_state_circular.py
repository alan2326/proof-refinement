"""Render state{1,2}.npy as a circular orange/black partition with
transparent corners (PNG with alpha = 0 outside the disk).

Reads:    outputs/<run>/state{1,2}.npy + outputs/<run>/x_grid.npy
Writes:   paper_artifacts/plots/<run>__state{1,2}_circle.png

Defaults to outputs/20260310_211533/. Pass --run to point at any other run.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = Path(__file__).resolve().parent

ORANGE = (0.91, 0.51, 0.18)   # warm pumpkin
BLACK  = (0.10, 0.10, 0.12)   # soft charcoal


def render(state_path: Path, x_grid_path: Path, out_path: Path,
           radius_frac: float = 1.0) -> None:
    f = np.load(state_path).astype(np.float32)
    x = np.load(x_grid_path).astype(np.float32)
    assert f.shape == (x.size, x.size), (f.shape, x.size)

    rgba = np.zeros((*f.shape, 4), dtype=np.float32)
    pos = f > 0
    rgba[pos]  = (*ORANGE, 1.0)
    rgba[~pos] = (*BLACK,  1.0)

    X, Y = np.meshgrid(x, x)
    R = float(x.max()) * radius_frac
    inside = (X**2 + Y**2) <= R * R
    rgba[..., 3] = inside.astype(np.float32)

    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(rgba, origin="lower",
              extent=(x.min(), x.max(), x.min(), x.max()),
              interpolation="nearest")
    ax.set_axis_off()
    fig.patch.set_alpha(0.0)
    fig.subplots_adjust(left=0, right=1, top=1, bottom=0)
    fig.savefig(out_path, dpi=200, bbox_inches="tight", pad_inches=0,
                transparent=True)
    plt.close(fig)
    print(f"Wrote {out_path}")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--run", default="outputs/20260310_211533",
                   help="path (relative to repo root or absolute) to a run dir "
                        "containing stateN.npy + x_grid.npy")
    p.add_argument("--states", nargs="+", default=["state1", "state2"])
    p.add_argument("--radius-frac", type=float, default=1.0,
                   help="disk radius as a fraction of |x|.max() (default 1.0)")
    args = p.parse_args()

    run_dir = Path(args.run)
    if not run_dir.is_absolute():
        run_dir = REPO / run_dir

    x_grid = run_dir / "x_grid.npy"
    if not x_grid.exists():
        raise SystemExit(f"missing {x_grid}")

    tag = run_dir.name
    for s in args.states:
        sp = run_dir / f"{s}.npy"
        if not sp.exists():
            print(f"skip {sp} (missing)")
            continue
        render(sp, x_grid,
               OUT_DIR / f"{tag}__{s}_circle.png",
               radius_frac=args.radius_frac)


if __name__ == "__main__":
    main()
