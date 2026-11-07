# Paper artifacts

Stable home for paper-facing outputs (plots, tables, figures) and the
scripts that produce them. Anything in here is meant to be cited / included
in the paper directly.

## Layout

```
paper_artifacts/
├── README.md                  ← this file
└── plots/
    ├── plot_kg_progression.py     ← main plot script (run / edit this)
    ├── _recompute_v25_v26.py      ← one-time helper, see below
    ├── v25_v26_patched.json       ← cached output of the helper
    ├── cr_progression.{pdf,png}   ← Plot 1: C_r per iteration (log scale)
    └── kg_improvement.{pdf,png}   ← Plot 2: K_G improvement over baseline
```

## Plots

### `plot_kg_progression.py`

Two plots, paper-ready (PDF + PNG):

1. **`cr_progression`** — `C_r` per iteration, log scale.
2. **`kg_improvement`** — `K_G` improvement over baseline =
   `π/(2·ln(1+√2)) − 1/c_{f,g}` per iteration, log scale.

Both axes labeled for paper inclusion (X = iteration, Y = the quantity).
No annotations, just the values. Computed in arb at prec=256 throughout.

**To rerun:**
```bash
uv run --with python-flint --with matplotlib \
    python paper_artifacts/plots/plot_kg_progression.py
```

### `_recompute_v25_v26.py`

V25 and V26's `delta_KG_str` in the upstream `Scratch/cr_progression_data.json`
still holds the K_max-era (non-rigorous) values. This helper recomputes
their ΔK_G from the post-K_max audit's patched `Cr ≈ 0.3734` using the
certified `solve_gamma` pipeline, and caches the result in
`v25_v26_patched.json`. The main plot script reads the cache.

V27 is excluded entirely (the post-K_max-patch re-baseline).

Run only if `Scratch/cr_progression_data.json` changes upstream:
```bash
uv run --with python-flint --with matplotlib \
    python paper_artifacts/plots/_recompute_v25_v26.py
```
