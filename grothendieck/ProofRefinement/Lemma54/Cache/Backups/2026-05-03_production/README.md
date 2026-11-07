# Production chunk certifier backup — 2026-05-03

Captured immediately after the V26 production chunk certifier run completed at 00:42 UTC, after 158 min wall-time on 96 workers.

## Files

| File | Purpose | Re-creation cost |
|---|---|---|
| `v26_chunk_certifier_npe16.json` | Assembled chunks JSON (64 chunks × Hp/Hpp/Heta + chunk geometry). Direct input to `joint_merged_uderiv.py`. | ~3 hr at 96 workers |
| `v26_chunk_certifier_npe16_raw.json` | Raw cache: 4224 work-unit results (`center`, `center_pp`, `path_node`). Lets us re-assemble or re-run joint oracle with different downstream choices without re-computing `acb.integral`. | ~3 hr at 96 workers |
| `joint_merged_cr_rigorous_full64.json` | Joint oracle Cr=34.47 result on full 64 chunks (n_p_cells=8). Includes per-(chunk, p_cell) scores. | ~30 sec |
| `parallel_chunk_certifier_prod.log` | Run log with progress lines (rate, ETA, errors). 0 errors. | — |

## Run parameters

```
n_per_edge = 16              # 64 chunks total
n_gl_path = 16               # 16 GL nodes per panel
n_panels_path = 2            # 2 panels per segment, 2 segments per chunk
n_workers = 96               # capped to avoid SSH stall
prec = 100                   # arb working precision (~30 dec digits)
rel_acc_bits = 22            # acb.integral target precision
rho_path = 1.5               # Bernstein ellipse radius
L_inner = 6                  # inner integration half-width
eta = 1/100                  # V26 framework
delta = 1635/10000           # V26 rectangle params
B = 1115/1000
P_kind = "v26"               # P̃(z) = η·h₃(√2·z)/√2, Q = -P
```

## Restoring

To use these in a future session:

```bash
cp Backups/2026-05-03_production/v26_chunk_certifier_npe16.json ../
cp Backups/2026-05-03_production/v26_chunk_certifier_npe16_raw.json ../
```

Then run joint oracle:

```bash
uv run --with python-flint python -u Scratch/joint_merged_uderiv.py \
  --chunks Cache/v26_chunk_certifier_npe16.json --n_p_cells 8
```

Or re-assemble from raw (e.g., if joint oracle code or chunk-bound code changes):

```bash
uv run --with python-flint python -u Scratch/assemble_partial_chunks.py \
  --raw_cache Cache/v26_chunk_certifier_npe16_raw.json \
  --out Cache/v26_chunk_certifier_npe16.json
```

## Result summary

- 4224/4224 work units completed; 0 errors
- Joint oracle (patched: denom fix + 2nd-order Taylor + anisotropic Φ'' + min(interval, norm)) gives **Cr_certified = 34.47**
- Dominated by chunks 0/15/16/31 (right/left edge corners) at p_cell=7 with score 68.94
- Next-tier: chunk 32 (top-left corner) with score 8.63
- Production version satisfies Lemma 5.4 candidates **down to V11 (Cr_val = 1)** after corner subdivision (preview shows Cr ≈ 0.55 with corners 2× + near 2×)

## Code commit reference

Inputs ran with the following key files at the state captured:
- `parallel_chunk_certifier.py` (incremental save + resume)
- `h_eta_parallel_path.py` (path integration with adaptive ρ)
- `h_prime_complex_certified.py` (Price formula H_η')
- `h_pp_complex_certified.py` (Price formula H_η'')
- `phi_pp_chunk_bound_eta_tight.py` (η²-tight chunk bound, post-λ-fix)
- `joint_merged_uderiv.py` (patched per LLM recommendations: denom + 2nd-order Taylor + Cauchy M_phi_ppp + min(interval,norm))
