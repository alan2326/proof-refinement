"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from `Evaluator.py`'s `ORACLE_REGISTRY` so the evaluator can
    re-run the function and check the candidate's declared rational lies above
    the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`.
  2. Register it in `Evaluator.ORACLE_REGISTRY` with the matching axiom name
     and bound field (the `def <field>_val : ℝ := <rat>` in the candidate).
  3. The Lean axiom statement must be regex-matchable by the registry's
     `expected_pattern`.

The certified-arb pipeline at `grothendieck/proof/certified/` provides the
underlying rigorous arithmetic; the wrappers in this module convert its
`flint.arb` outputs into Lean-consumable rationals.

================================================================
2026-05-03 — TRUNCATION-FREE ORACLES (use these in new candidates)
================================================================

The eight oracles below — `compute_M_phi_bound`,
`compute_M_phi_prime_bound`, `compute_M_pp_bound`,
`compute_inv_F_p_z_bound`, `compute_u_zz_bound`,
`compute_joint_phi_phip_invD2_bound`,
`compute_uzz_phi_sq_bound`, `compute_merged_uderiv_bound` — are
**deprecated** because they import the K_max-truncated
`eval_H_eta_at_acb` (see PATCH_NOTES.md). The Evaluator's G7.a
fails any candidate whose oracle path reaches them.

Their replacements live in the `truncfree` subpackage:

    from Numerical_Library.truncfree import (
        round3, production, compute_bundle, audit_candidate,
        compute_M_phi_truncfree_bound,
        compute_M_phi_prime_truncfree_bound,
        compute_M_pp_truncfree_bound,
        compute_inv_F_p_z_truncfree_bound,
        compute_u_zz_bound_truncfree_bound,
        compute_joint_phi_phip_invD2_truncfree_bound,
        compute_uzz_phi_sq_truncfree_bound,
        compute_merged_uderiv_truncfree_bound,
    )

Each `compute_*_truncfree_bound(source="round3"|"production")`
returns an `OracleResult` derived from the canonical 2026-05-03
chunk certifier output (cached as `audit_naive_results.json`
next to the chunks JSON in `Cache/Backups/2026-05-03_*`).

For the per-candidate Cr_phi_* audit (PATCH_NOTES R5 / G7.b):

    from Numerical_Library.truncfree import audit_candidate, audit_all_candidates
    rows = audit_all_candidates()              # default: round-3 preset
    audit_candidate("V11").Cr_patched_float    # → ~0.3255

See `Numerical_Library/truncfree/__init__.py` for the full API and
`PATCH_NOTES.md` for the bug write-up.
"""

from .types import OracleResult
from .m_bound import (
    compute_M_bound, compute_M_bound_tight, compute_M_bound_production,
)
from .r_bound import compute_R_bound, compute_R_bound_tight

# --- Deprecated K_max-truncated oracles (kept for V0-V26 backwards-compat) --
from .m_phi import compute_M_phi_bound
from .m_phi_prime import compute_M_phi_prime_bound
from .m_pp import compute_M_pp_bound
from .inv_F_p_z import compute_inv_F_p_z_bound
from .u_zz import compute_u_zz_bound
from .joint_phi_phip_invD2 import compute_joint_phi_phip_invD2_bound
from .uzz_phi_sq import compute_uzz_phi_sq_bound
from .merged_uderiv import compute_merged_uderiv_bound

# --- Truncation-free oracle suite (post-2026-05-03 patch) -------------------
# These do NOT import eval_H_eta_at_acb and satisfy Evaluator G7.a.
# Re-exported at the top level so `lemma.toml`'s `oracle_fn = "compute_*_
# truncfree_bound"` resolves through `getattr(Numerical_Library, fn_name)`
# in `Evaluator._resolve_oracle_fn`.
from . import truncfree  # subpackage; see truncfree/__init__.py
from .truncfree import (
    compute_M_phi_truncfree_bound,
    compute_M_phi_prime_truncfree_bound,
    compute_M_pp_truncfree_bound,
    compute_inv_F_p_z_truncfree_bound,
    compute_u_zz_bound_truncfree_bound,
    compute_joint_phi_phip_invD2_truncfree_bound,
    compute_uzz_phi_sq_truncfree_bound,
    compute_merged_uderiv_truncfree_bound,
)

__all__ = [
    "OracleResult",
    "compute_M_bound",
    "compute_M_bound_tight",
    "compute_M_bound_production",
    "compute_R_bound",
    "compute_R_bound_tight",
    # Deprecated; do NOT use in new candidates (see PATCH_NOTES.md)
    "compute_M_phi_bound",
    "compute_M_phi_prime_bound",
    "compute_M_pp_bound",
    "compute_inv_F_p_z_bound",
    "compute_u_zz_bound",
    "compute_joint_phi_phip_invD2_bound",
    "compute_uzz_phi_sq_bound",
    "compute_merged_uderiv_bound",
    # Post-2026-05-03 truncation-free suite (use these in new candidates)
    "truncfree",
    "compute_M_phi_truncfree_bound",
    "compute_M_phi_prime_truncfree_bound",
    "compute_M_pp_truncfree_bound",
    "compute_inv_F_p_z_truncfree_bound",
    "compute_u_zz_bound_truncfree_bound",
    "compute_joint_phi_phip_invD2_truncfree_bound",
    "compute_uzz_phi_sq_truncfree_bound",
    "compute_merged_uderiv_truncfree_bound",
]
