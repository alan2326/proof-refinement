# Subdivision rounds — 2026-05-03

Three rounds of corner-subdivision computation on top of the
`2026-05-03_production/` baseline (V26 production chunk certifier output,
Cr=34.47 rigorous).

## Trajectory

| File | Cr_certified | Subdivisions applied | Wall-time |
|---|---|---|---|
| `../2026-05-03_production/joint_merged_cr_rigorous_full64.json` | 34.47 | none (64 chunks, npe=16) | 158 min (production) |
| `round1_v26_corner_split.json` | 2.27 | corners 2× (8 chunks split into 16 sub-chunks) | 11 min |
| `round2_v26_corner_split_v2.json` | 1.23 | + near-corners 2× (chunks 1, 14, 17, 30) | 16 min |
| `round3_v26_corner_split_v3.json` | **0.383** | + next-tier 2× (chunks 0, 11, 12, 23 in v2 numbering) | 17 min |

Each round used **V26 4-fold symmetry**: only Q1 (a≥0, b≥0) chunks computed
as primaries, other 3 quadrants populated by reflection
(`H_η(z̄)=̄H_η(z)`, `H_η(-z)=-H_η(z)`).

## Rigor

All chunks (subdivided or not) hold rigorous arb intervals:
- Sharp `H_η(c)`: path-integration via `h_eta_parallel_path` with
  adaptive-ρ Bernstein error per panel
- Sharp `H_η'(c)`: `h_prime_complex_certified` (Price formula + closed-form
  Gaussian-tail bound on outer integrand, **no phi-series truncation**)
- Sharp `H_η''(c)`: `h_pp_complex_certified` (same machinery + Price's
  `(2z/D - S_z')` factor)
- Chunk bounds: `bound_Phi_prime_on_chunk_certified`,
  `bound_H_eta_pp_on_chunk_certified`, `bound_Phi_pp_eta_tight_certified`
  (post-λ-fix, anisotropic Gaussian)

Joint oracle (`joint_merged_uderiv.py`) applies:
- Denominator fix (`|D| ≥ inf|H_0'| - p_hi · M_phi_p`)
- 2nd-order Taylor pad (uses sharp Φ', Φ'' midpoints + Cauchy M_phi_ppp)
- min(interval, norm) score per (chunk, p-cell)

## What this proves

- **V11** (Cr_val = 1): ✅ rigorously certifiable using `round3` data
  (Cr = 0.383 ≤ 1, margin 2.6×). This replaces V11's K_max=80
  truncated `compute_M_phi_bound` etc. with truncation-free oracles.
- V12 onwards (Cr_val ≤ 1/32): not yet reachable; needs further
  subdivision or sharper Hpp(c) at corner sub-chunks.

## Running joint oracle on these

```bash
# Re-run on round-3 output to confirm Cr ≈ 0.38
uv run --with python-flint python -u Scratch/joint_merged_uderiv.py \
  --chunks Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json \
  --n_p_cells 8
```

## Code state references

Subdivision script: `Scratch/corner_subdivision_certifier.py`
Joint oracle: `Scratch/joint_merged_uderiv.py`
Anisotropic Φ'' bound: `Scratch/phi_pp_chunk_bound_eta_tight.py` (post-λ-fix, post-aniso)
