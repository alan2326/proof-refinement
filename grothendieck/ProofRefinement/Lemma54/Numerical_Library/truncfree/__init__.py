"""Truncation-free oracle suite (post-2026-05-03 patch).

The default entry point for any sprint that needs `M_phi`, `M_phi_prime`,
`M_pp`, `inv_F_p_z`, `u_zz_bound`, `joint_phi_phip_invD2`,
`uzz_phi_sq`, or `merged_uderiv`. Replaces the `K_max`-truncated
oracles in `Numerical_Library/{m_phi,m_phi_prime,...}.py` (deprecated;
see `PATCH_NOTES.md`).

Quick start:

    from Numerical_Library.truncfree import round3, production, compute_bundle

    # Use the canonical cached round-3 subdivided chunks (Cr ≈ 0.38).
    b = round3()
    print(b.M_phi, b.merged_uderiv)
    res: OracleResult = b.as_oracle_result("M_phi")

    # Or recompute from a fresh chunks JSON (rebuilds the audit cache).
    b2 = compute_bundle("path/to/my_chunks.json", n_p_cells=8)

    # Or load directly from a saved audit JSON.
    from Numerical_Library.truncfree import from_audit_json
    b3 = from_audit_json("Cache/.../audit_naive_results.json")

The bundle exposes raw `arb` intervals; `as_oracle_result(name, ...)`
converts them to a Lean-consumable `OracleResult` (Fraction + meta)
using the same `arb_to_rational_ub` rationaliser the deprecated
oracles use.

`compute_bundle` is cached: it writes / reads
`audit_naive_results.json` next to the chunks JSON, keyed on
`(chunks_path, n_p_cells, prec)`. Pass `use_cache=False` to force
recomputation.

Per-oracle convenience functions
(`compute_M_phi_truncfree_bound(source="round3")` etc.) wrap
`round3()` / `production()` / `from_audit_json()` and rationalise to
`OracleResult` so they match the calling convention of the
deprecated `compute_*_bound` family. These do NOT touch
`eval_H_eta_at_acb` and so satisfy Evaluator G7.a.
"""

from __future__ import annotations

from .oracle import (
    TruncFreeBundle,
    compute_bundle,
    from_audit_json,
    round3,
    production,
    canonical_chunks_path,
    canonical_audit_path,
    compute_M_phi_truncfree_bound,
    compute_M_phi_prime_truncfree_bound,
    compute_M_pp_truncfree_bound,
    compute_inv_F_p_z_truncfree_bound,
    compute_u_zz_bound_truncfree_bound,
    compute_joint_phi_phip_invD2_truncfree_bound,
    compute_uzz_phi_sq_truncfree_bound,
    compute_merged_uderiv_truncfree_bound,
)
from .candidate_audit import (
    audit_candidate,
    audit_all_candidates,
    CANDIDATE_FORMULAS,
    PAPER_CONSTANTS,
)

__all__ = [
    "TruncFreeBundle",
    "compute_bundle",
    "from_audit_json",
    "round3",
    "production",
    "canonical_chunks_path",
    "canonical_audit_path",
    "compute_M_phi_truncfree_bound",
    "compute_M_phi_prime_truncfree_bound",
    "compute_M_pp_truncfree_bound",
    "compute_inv_F_p_z_truncfree_bound",
    "compute_u_zz_bound_truncfree_bound",
    "compute_joint_phi_phip_invD2_truncfree_bound",
    "compute_uzz_phi_sq_truncfree_bound",
    "compute_merged_uderiv_truncfree_bound",
    "audit_candidate",
    "audit_all_candidates",
    "CANDIDATE_FORMULAS",
    "PAPER_CONSTANTS",
]
