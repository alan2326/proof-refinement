# Numerical_Library

Python functions backing the certified-arb oracles in
`ProofRefinement/Lemma54/Candidates/V*.lean`.

## Quick reference

| You want                                  | Use                                                    |
|-------------------------------------------|--------------------------------------------------------|
| A truncation-free `M_phi` / `M_phi_prime` / `M_pp` / `inv_F_p_z` / `u_zz_bound` / `joint_phi_phip_invD2` / `uzz_phi_sq` / `merged_uderiv` for a new candidate | [`truncfree.compute_*_truncfree_bound`](truncfree/oracle.py) |
| The full eight-oracle bundle for round-3 subdivided chunks (`Cr ≈ 0.38`) | [`truncfree.round3()`](truncfree/oracle.py) |
| The full bundle for production chunks (no subdivision, `Cr ≈ 34.47`) | [`truncfree.production()`](truncfree/oracle.py) |
| The patched `Cr_val` for V9..V26 (Cr_phi_* formula applied to the truncation-free bundle) | [`truncfree.audit_candidate("V11")`](truncfree/candidate_audit.py) |
| Recompute oracles from a fresh chunks JSON | [`truncfree.compute_bundle("path/to/chunks.json")`](truncfree/oracle.py) |
| The legacy K_max-truncated `compute_M_phi_bound` etc. | top-level imports — **deprecated**, do not use |

## The deprecation (2026-05-03)

Every top-level oracle in this directory — `m_phi.py`,
`m_phi_prime.py`, `m_pp.py`, `inv_F_p_z.py`, `u_zz.py`,
`joint_phi_phip_invD2.py`, `uzz_phi_sq.py`, `merged_uderiv.py` —
imports `eval_H_eta_at_acb` from
`grothendieck/proof/certified/compute_cr_v2.py`. That function
truncates the φ-series at `K_max` terms with **no rigorous tail
bound** (its docstring admits this). All eight oracles inherit the
non-rigorous step. The Evaluator's gate **G7.a** fails any candidate
whose oracle path reaches `eval_H_eta_*at_acb`.

The K_max-era oracles are kept here so V0..V26 still parse and the
log can be replayed; they should not back any new candidate. The
replacement is the `truncfree` subpackage below.

See [`PATCH_NOTES.md`](../PATCH_NOTES.md) for the full bug write-up
and the binding rules R1–R5.

## `truncfree/` — the post-patch oracle suite

```
truncfree/
├── __init__.py        — public API
├── oracle.py          — TruncFreeBundle + compute_bundle + presets
└── candidate_audit.py — Cr_phi_* formula evaluators + audit_candidate
```

### Bundle shape

A `TruncFreeBundle` carries the eight `arb` quantities computed from
**one** chunks JSON, plus metadata:

```python
@dataclass
class TruncFreeBundle:
    M_phi: arb
    M_phi_prime: arb
    M_pp: arb
    inv_F_p_z: arb
    u_zz_bound: arb
    joint_phi_phip_invD2: arb
    uzz_phi_sq: arb
    merged_uderiv: arb
    inf_D: arb
    label: str
    chunks_path: str
    n_p_cells: int
    n_chunks: int
    prec: int = 200
    audit_json_path: str | None = None
    info: dict[str, Any] = field(default_factory=dict)

    def as_arb(name: str) -> arb: ...
    def as_oracle_result(name: str, **kw) -> OracleResult: ...
    def as_dict() -> dict: ...
    def summary() -> str: ...
```

### Caching

`compute_bundle(chunks_path, …)` writes its output to
`<chunks_path>.parent/<chunks_path>.stem__truncfree_audit.json` by
default and re-reads it on subsequent calls when
`(chunks_path, n_p_cells, prec)` matches. Use `use_cache=False` to
force recomputation; pass `audit_path=...` to override the
location.

The two canonical bundles ship pre-cached:

| Preset | Chunks JSON | Audit JSON | Cr |
|---|---|---|---|
| `production()` | `Cache/Backups/2026-05-03_production/v26_chunk_certifier_npe16.json` | `Cache/Backups/2026-05-03_production/audit_naive_results.json` | 34.47 |
| `round3()` | `Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json` | `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` | 0.383 |

So `from Numerical_Library.truncfree import round3; b = round3()` is
a milliseconds-fast JSON load. `b.summary()` prints the eight
oracles for a quick eyeball.

### Per-oracle compute_*_truncfree_bound

Each of the eight oracles has a thin wrapper that returns an
`OracleResult` (Fraction + ball value + meta) like the legacy API:

```python
from Numerical_Library.truncfree import (
    compute_M_phi_truncfree_bound,
    compute_merged_uderiv_truncfree_bound,
)

m_phi = compute_M_phi_truncfree_bound(source="round3")
merged = compute_merged_uderiv_truncfree_bound(source="round3")
print(m_phi.bound)            # Fraction
print(merged.ball_value)      # float
```

These are the "drop-in" entry points for sprints that mint a new
inline oracle. They do **not** import `eval_H_eta_at_acb` and so
satisfy G7.a.

### Per-candidate audit (Cr_phi_* formula)

```python
from Numerical_Library.truncfree import (
    round3, audit_candidate, audit_all_candidates,
    CANDIDATE_FORMULAS, PAPER_CONSTANTS,
)

# Fast: load cached bundle, evaluate V11's Cr_phi_uzz formula
a = audit_candidate("V11")
print(a.formula, a.Cr_patched_float, a.Cr_decl_float)
# → "Cr_phi_uzz", 0.3255..., 1.0

# All eighteen candidates against the same bundle
b = round3()
for r in audit_all_candidates(bundle=b):
    print(f"{r.candidate:>4}: {r.Cr_patched_float:.3e}  ({r.formula})")

# Audit a custom (unmapped) candidate
a = audit_candidate(
    "V27_draft",
    bundle=b,
    formula="Cr_phi_uzz_merged",
    Cr_decl="1/2",
)
```

Paper constants (`r = 23/25`, `R = 23/20`, `p_max = 1`) live in
`PAPER_CONSTANTS`. The candidate → (formula, Cr_decl) mapping lives
in `CANDIDATE_FORMULAS`.

### Recomputing from a fresh chunks JSON

If a sprint produces a new chunks JSON (e.g. a 4th subdivision
round, an alternative-contour run), build the bundle directly:

```python
from Numerical_Library.truncfree import compute_bundle

b = compute_bundle(
    "Cache/Backups/2026-05-04_round4/round4_corner_split.json",
    n_p_cells=8,
    prec=200,
    use_cache=True,                    # default; reads cache if present
    label="round4_subdivided",
    verbose=True,
)
print(b.summary())
```

This runs the chunk-sup-bounds sweep + per-cell joint sweep
(typically 30s for 88 chunks at `n_p_cells=8`) and writes the
audit JSON next to the chunks. Subsequent calls are cache hits.

### What's actually under the hood

`truncfree/oracle.py` adds `Scratch/` to `sys.path` and imports the
patched chunk-bound chain:

- `chunk_constants_safe.py` — interval-arithmetic safe `(d_Z, z_ub)`
- `gaussian_tail_bounds.py` — closed-form Gaussian moment bounds
- `phi_prime_chunk_bound_certified.py` — η²-tight `sup |Φ'(z)|`
- `h_eta_pp_chunk_bound_certified.py` — `sup |H_η''(z)|` via real majorant
- `phi_pp_chunk_bound_eta_tight.py` — η²-tight `sup |Φ''(z)|`,
  post-anisotropic-Gaussian + post-λ-decay-fix
- `joint_merged_uderiv.py` — patched per-(chunk, p-cell) merged
  oracle with denom-fix + 2nd-order Taylor pad + Cauchy `M_phi_ppp`
  + `min(interval, norm)` per cell
- `_naive_audit.py::_eval_three_at_cell` — same Taylor-pad
  evaluator extended to return joint, uzz_phi_sq, merged in one pass

None of these touch `eval_H_eta_at_acb`. Sharp midpoint values come
from path-integration (`h_eta_parallel_path.py`) / Price-formula
derivatives (`h_prime_complex_certified.py`,
`h_pp_complex_certified.py`) — the whole point of the post-patch
infrastructure.

### Adding a NEW truncation-free oracle

If your sprint needs a sup-norm bound on a quantity not already in
the bundle:

1. Read [`PATCH_NOTES.md`](../PATCH_NOTES.md) §2 to confirm none of
   the existing patched evaluators already give it.
2. Add a per-chunk evaluator under `Scratch/` that uses the
   path-integration / Price-formula / chunk-bound primitives. See
   `Scratch/joint_merged_uderiv.py` and
   `Scratch/_naive_audit.py::_eval_three_at_cell` as templates.
3. Add a field to `TruncFreeBundle` and accumulate it inside
   `_compute_bundle_fresh` (or extend `_eval_three_at_cell` to
   return it).
4. Wrap with `_make_compute_fn("<name>")` in `truncfree/oracle.py`.
5. Update `Numerical_Library/__init__.py` and this README.
6. **Do NOT** import `eval_H_eta_at_acb`,
   `eval_H_eta_deriv_at_acb`, `eval_phi_at_acb`, or
   `eval_phi_and_deriv_at_acb` — that fails Evaluator G7.a.

## Top-level files (still rigorous)

These four are NOT affected by the K_max truncation; they bound
non-`H_η` quantities and remain in production use:

- `m_bound.py` — sup |F_inv| on disk(r), via Rouché-certified rectangle
- `r_bound.py` — `R_val_paper r ≤ 23/20` (algebraic; no φ-series)
- `_arb_helpers.py` — `arb_to_rational_ub` rationaliser + `cached_run`
- `types.py` — `OracleResult` dataclass

## Auxiliary / loader files

- `_phi_loader.py` — caches the b-series JSON
  (`outputs/b_series_eta0p01_K250_dps100.json`). Currently used only
  by the deprecated K_max-truncated oracles. The `truncfree`
  subpackage does not call it.
