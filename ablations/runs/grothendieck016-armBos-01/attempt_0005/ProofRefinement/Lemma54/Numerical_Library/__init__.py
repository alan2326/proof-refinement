"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from a `[[oracles]]` row in `lemma.toml` (`oracle_fn`) so the
    evaluator can re-run the function and check the candidate's declared
    rational lies above the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`, callable
     with no arguments (all parameters keyword-only with pinned defaults).
  2. Add a matching `[[oracles]]` row in `lemma.toml` with the axiom name
     (namespace-stripped), the candidate's `bound_field` def, and `oracle_fn`.
  3. Declare the corresponding axiom in the candidate and use it in the proof.

The certified-arb pipeline at `grothendieck/proof/certified/` provides the
underlying rigorous arithmetic; the wrappers in this module convert its
`flint.arb` outputs into Lean-consumable rationals.
"""

from .types import OracleResult
from .m_bound import (
    compute_M_bound, compute_M_bound_tight, compute_M_bound_production,
)
from .r_bound import compute_R_bound, compute_R_bound_tight
from .m_phi import compute_M_phi_bound
from .m_phi_prime import compute_M_phi_prime_bound
from .m_pp import compute_M_pp_bound
from .m_pp_tight import compute_M_pp_tight_bound
from .inv_F_p_z import compute_inv_F_p_z_bound

__all__ = [
    "OracleResult",
    "compute_M_bound",
    "compute_M_bound_tight",
    "compute_M_bound_production",
    "compute_R_bound",
    "compute_R_bound_tight",
    "compute_M_phi_bound",
    "compute_M_phi_prime_bound",
    "compute_M_pp_bound",
    "compute_M_pp_tight_bound",
    "compute_inv_F_p_z_bound",
]
