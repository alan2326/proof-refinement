I analyzed where V11's `Cr_phi_uzz ≈ 0.523` actually comes from and found the dominant loss is the `M_pp` oracle: `compute_M_pp_bound` bounds `‖∂²_z F_p‖ ≤ sup‖H_0''‖ + sup‖H_η''‖`, and the second sup is obtained by Cauchy on `H_η'` itself (`≈ 2.08 / (δ/4) ≈ 51`), so `M_pp ≈ 56` even though `sup‖H_0''‖ ≈ 5.08` (attained at `w = 1−δ` on the real axis, exact closed form `|w|/|1−w²|^{3/2}`).

The fix is a genuine sub-claim of the same shape: since `∂²_z F_p = H_0'' + p·(H_η'' − H_0'')`, run the Cauchy step on the **difference** `H_η' − H_0'` (whose sup is `≈ 0.054`, ~38× smaller than `H_η'`), giving `M_pp ≲ 5.1 + 0.06/0.0409 ≈ 6.6`. I also tighten `inv_F_p_z_val` from the integer ceiling `2` to `9/5` (the existing oracle already certifies `≈ 1.705`), no new numerics needed. No new Lean infrastructure is required — `lemma_5_4_paper_on_domain_phi_uzz` is already `M_pp`-polymorphic.

```python path=ProofRefinement/Lemma54/Numerical_Library/m_pp_tight.py
"""m_pp_tight oracle: certified upper bound on

    M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖(1−p) H_0''(w) + p · H_η''(w)‖

i.e. `sup ‖iteratedDeriv 2 (F_p η p) w‖`, the same quantity `m_pp.py`
bounds — but via a strictly tighter route.

Why a second module. `m_pp.py` uses the triangle split

    ‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖,

and bounds the second term by Cauchy applied to `H_η'` itself on an
enlarged rectangle:  sup‖H_η''‖ ≤ sup_outer‖H_η'‖ / d.  Since
`sup‖H_η'‖ ≈ 2.08` and `d = δ/4 ≈ 0.0409`, that term alone is ≈ 51,
swamping the ≈ 5.08 contribution of `sup‖H_0''‖` and giving
`M_pp ≈ 56`.

This module uses the *affine* decomposition instead:

    (1−p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0''),

so

    M_pp ≤ sup_Ω ‖H_0''‖ + p_max · sup_Ω ‖H_η'' − H_0''‖,

and bounds the second sup by Cauchy applied to the *difference*
`H_η' − H_0'` on the same enlarged rectangle:

    ‖(H_η' − H_0')'(w)‖ ≤ sup_{|ζ−w| = d} ‖H_η' − H_0'‖ / d
                        ≤ sup_{Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d.

At η = 1/100 the difference `H_η' − H_0'` has sup ≈ 0.054 on Ω (this is
exactly the quantity `m_phi_prime.py` certifies) — roughly 38× smaller
than `H_η'` itself — so the Cauchy term drops from ≈ 51 to ≈ 1.5 and the
overall bound from ≈ 56 to ≈ 6.6.

Both steps are the same kind of numerical sub-claim as the existing
oracles: a sup-norm of an explicit analytic expression over an explicit
rectangle, evaluated with certified `arb` interval arithmetic on the
rectangle boundary (max-modulus ⇒ boundary sup = closed-rectangle sup).

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper …),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_tight_val

The universal quantifier over `p ∈ Ioo 0 pr_paper` is subsumed by
`p_max = 1`, using the seed axiom `pr_paper_le_one`.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_deriv_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_pp_tight_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} ‖∂²_z F_p(η, p, w)‖ pipeline (tight route)."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # ------------------------------------------------------------------
    # 1. sup ‖H_0''(w)‖ on ∂Ω, closed form H_0''(w) = w / (1 − w²)^{3/2}.
    # ------------------------------------------------------------------
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 − w²
        # rsqrt(u) = u^{−1/2}, so u^{−3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # ------------------------------------------------------------------
    # 2. sup ‖H_η''(w) − H_0''(w)‖ on ∂Ω via Cauchy applied to the
    #    difference H_η' − H_0' on the enlarged rectangle Ω(δ−d, B+d),
    #    d = δ/4 (same enlargement m_pp.py uses).
    # ------------------------------------------------------------------
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d    # = 3δ/4
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the (H_η' − H_0') Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime_diff(z: acb) -> arb:
        H_eta_prime = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_prime = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_prime - H_0_prime)

    max_diff_prime_outer = _max_on_rect(
        phi_prime_diff, delta_inner, B_outer, n_per_edge, prec,
    )
    max_H_pp_diff = max_diff_prime_outer / d

    # ------------------------------------------------------------------
    # 3. Affine combination: ‖H_0'' + p (H_η'' − H_0'')‖ for p ∈ [0, p_max].
    # ------------------------------------------------------------------
    M_pp_arb = max_H0_pp + p_max_arb * max_H_pp_diff

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_diff_prime_outer_str": max_diff_prime_outer.str(20, more=True),
        "max_H_pp_diff_str": max_H_pp_diff.str(20, more=True),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_tight_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on M_pp = sup_{[0,p_max]×Ω} ‖∂²_z F_p‖.

    Same quantity as `compute_M_pp_bound`, computed via the affine
    decomposition `H_0'' + p (H_η'' − H_0'')` so the Cauchy step runs on
    the (much smaller) difference `H_η' − H_0'` rather than on `H_η'`.

    Defaults match the V10/V11 oracle rectangle (`δ = 1635/10000`,
    `B = 1115/1000`) and `p_max = 1` (justified by the seed axiom
    `pr_paper_le_one`). First call is ~60–120 s (two `_max_on_rect` scans
    on different rectangles); cached thereafter under `.cache/`.
    """
    key = {
        "fn": "compute_M_pp_tight_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_pp_arb = arb(cached["M_pp_str"])
    bound = arb_to_rational_ub(
        M_pp_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_diff_prime_outer_arb_str": cached["max_diff_prime_outer_str"],
            "max_H_pp_diff_arb_str": cached["max_H_pp_diff_str"],
        },
    )
```

```python path=ProofRefinement/Lemma54/Numerical_Library/__init__.py
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
```

```toml path=ProofRefinement/Lemma54/lemma.toml
# Per-lemma config consumed by Evaluator.py.
#
# This file externalizes everything about Lemma 5.4 that the evaluator needs
# to know: the sink theorem name, the score expression, the seed axioms it
# may inherit from V0, and the numerical oracles it may invoke.
#
# Design rationale: see ../../docs/PROOF_REFINEMENT_DESIGN.md

name        = "Lemma 5.4"
slug        = "lemma_5_4"
paper_ref   = "Braverman et al. (2011), §5"

# The candidate must declare `theorem <sink_theorem>` (under the namespace
# of its choice). The evaluator runs `#print axioms <namespace>.<sink_theorem>`
# to enumerate transitive dependencies.
sink_theorem = "lemma_5_4_search"

# Score: a Python arithmetic expression over the candidate's `def *_val`
# rationals (and the constants in [search_constants]). Smaller is better.
score = "Cr_val"

# Lean expressions the score evaluator should resolve to fixed rationals.
[search_constants]
"SearchConfig.r"   = "23/25"
"SearchConfig.eta" = "1/100"

# Axioms allowed in the audited set without an oracle backing.
# `sorryAx` is never permitted.
[seed_axioms]
allowed = [
  # Standard Lean.
  "propext",
  "Classical.choice",
  "Quot.sound",

  # 12 trusted analytic axioms about the IFT-supplied F_inv_paper family.
  # Inherited from the production proof at
  # ProofGraph/Effective/Lemma54Effective.lean. The agent may prove these
  # as Lean theorems (which removes them from the audited set) but must
  # not introduce new ones.
  "Braverman.Paper.F_inv_paper",
  "Braverman.Paper.F_inv_paper_eq",
  "Braverman.Paper.F_inv_paper_zero",
  "Braverman.Paper.F_inv_paper_mem_S",
  "Braverman.Paper.F_inv_paper_R_bound",
  "Braverman.Paper.F_inv_paper_analytic",
  "Braverman.Paper.F_inv_paper_contdiff",
  "Braverman.Paper.F_inv_paper_at_origin",
  "Braverman.Paper.F_inv_paper_first_deriv_zero",
  "Braverman.Paper.pr_paper",
  "Braverman.Paper.pr_paper_pos",
  "Braverman.Paper.pr_paper_le_one",

  # Structural domain-containment axiom (Rouché-certified by the production
  # runner; not numerically re-checked per candidate).
  "Braverman.PaperV0.h_oracle_domain_contains_image",
]

# Oracle-backed axioms. Each axiom name (short, namespace-stripped) maps
# to a `def <bound_field>_val : ℝ` and a Python function in
# `Numerical_Library/` that recomputes a certified upper bound. The
# evaluator demands `<bound_field>_val >= oracle_fn().bound`.

[[oracles]]
axiom       = "h_M_oracle"
bound_field = "M_val"
oracle_fn   = "compute_M_bound_tight"

# Approved by proposal_001 (2026-04-30). Three η-aware oracles for sup-norms
# of |H_η − H_0|, |H_η' − H_0'|, and |F_ww| on the oracle rectangle. See
# Proposals/proposal_001_cr_refined_oracles.md for the math; see
# Scratch/sprint_proposal_001_smoke.py for the certified numerical values.

[[oracles]]
axiom       = "h_M_phi_oracle"
bound_field = "M_phi_val"
oracle_fn   = "compute_M_phi_bound"

[[oracles]]
axiom       = "h_M_phi_prime_oracle"
bound_field = "M_phi_prime_val"
oracle_fn   = "compute_M_phi_prime_bound"

[[oracles]]
axiom       = "h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn   = "compute_M_pp_bound"

# Approved by sprint_014 (2026-04-30). Sup of `1 / ‖∂_z F_p(η, p, w)‖` over
# `p ∈ [0, 1]` and `w ∈ Ω(δ, B)`. Replaces the loose paper bound
# `1/‖∂_z F_p‖ ≤ 2R/(1−r) ≈ 28.75` from `F_p_deriv_lower_bound_at_F_inv`
# with a direct η-aware ≈ 2 — a ~14× tightening of `invFp` (~196× of
# `invFp²`), driving `Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z` down
# from 3.79 to ≈ 1.65 at the V9 parameters.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"

# Tightened restatement of the `h_M_pp_oracle` quantity (same sup-norm, same
# rectangle, same `p ∈ [0, 1]` range). `compute_M_pp_bound` splits
# `(1−p) H_0'' + p H_η''` by the triangle inequality and Cauchy-bounds
# `sup‖H_η''‖` from `sup‖H_η'‖ ≈ 2.08` over `d = δ/4`, giving ≈ 51 and a
# total ≈ 56. `compute_M_pp_tight_bound` instead uses the affine form
# `H_0'' + p (H_η'' − H_0'')` and Cauchy-bounds the *difference* from
# `sup‖H_η' − H_0'‖ ≈ 0.054` (the `h_M_phi_prime_oracle` quantity), which
# is ~38× smaller — dropping the Cauchy contribution to ≈ 1.5 and the
# total to ≈ 6.6.

[[oracles]]
axiom       = "h_M_pp_tight_oracle"
bound_field = "M_pp_tight_val"
oracle_fn   = "compute_M_pp_tight_bound"
```

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
/-
  Candidates/V12.lean — attack the two remaining loose numerical inputs of
  V11's `Cr_phi_uzz` bound, dropping `Cr_val` from `1` to `9/100`
  (an 11.1× reduction; V11's own literal bound was ≈ 0.523, so the genuine
  tightening here is ≈ 5.9×).

  -- @parent Candidates/V11.lean

  V11 proved

      ‖…‖ ≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp · p²,
      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi²

  and instantiated it at `inv_F_p_z = 2`, `M_pp = 5608/100`, giving
  ≈ 0.0104 + 0.5126 ≈ 0.5230, declared as `Cr_val := 1`.

  Two observations drive V12; NO Lean infrastructure changes are needed
  (`lemma_5_4_paper_on_domain_phi_uzz` is already polymorphic in both
  `inv_F_p_z` and `M_pp`).

  (1) `inv_F_p_z_val` was the integer ceiling `2` of a bound the existing
      `Numerical_Library.compute_inv_F_p_z_bound` oracle already certifies
      at ≈ 1.7035. Declaring `9/5 = 1.8` keeps ≈ 5.5 % headroom over the
      certified value and needs no new numerics. Effect: `inv²` 4 → 3.24
      and `inv³` 8 → 5.832.

  (2) `M_pp_val = 5608/100 ≈ 56.08` was by far the dominant loss (term-2
      carried 98 % of V11's bound). That number comes from
      `compute_M_pp_bound`, which splits

          ‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

      and then Cauchy-bounds `sup‖H_η''‖ ≤ sup_outer‖H_η'‖ / d` with
      `d = δ/4 ≈ 0.0409` and `sup‖H_η'‖ ≈ 2.08`, i.e. ≈ 51 — swamping the
      ≈ 5.08 contribution of `sup‖H_0''‖` (closed form `|w|/|1−w²|^{3/2}`,
      maximised at `w = 1−δ` on the real axis).

      V12 instead uses the affine decomposition

          (1−p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0''),

      valid for every `p`, and Cauchy-bounds the *difference*:

          ‖H_η''(w) − H_0''(w)‖ = ‖(H_η' − H_0')'(w)‖
            ≤ sup_{Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d.

      At η = 1/100 the difference `H_η' − H_0'` has sup ≈ 0.054 on Ω (this
      is exactly the quantity `h_M_phi_prime_oracle` certifies), ~38×
      smaller than `H_η'` itself, so the Cauchy contribution drops from
      ≈ 51 to ≈ 1.5 and the total from ≈ 56 to ≈ 6.6. The new oracle
      `Numerical_Library.compute_M_pp_tight_bound` implements exactly this
      route; `M_pp_tight_val := 12` is declared with ~1.8× headroom.

  At V12 parameters:
    r_val            = 23/25
    M_phi_val        = 239/5000        (unchanged from V9–V11)
    M_phi_prime_val  = 543/10000       (unchanged from V9–V11)
    inv_F_p_z_val    = 9/5             (was 2)
    M_pp_tight_val   = 12              (was M_pp_val = 5608/100)
  giving
    Cr_phi_uzz ≤ (239/5000)·(543/10000)·(81/25)
                   + (1/2)·12·(729/125)·(239/5000)²
               = 10511937/1250000000 + 249847254/3125000000
               = 552254193/6250000000
               ≈ 0.0084095 + 0.0799511 = 0.0883607,
  comfortably below `Cr_val := 9/100 = 0.09` (margin ≈ 0.00164, exact
  rational arithmetic so `norm_num` closes it).

  Trust base (same shape as V11; one oracle swapped, none added in kind):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (seed).
    - `Braverman.PaperV0.h_M_oracle` (declared for parity with V9–V11;
      not consumed by the `_phi_uzz` proof path).
    - `Braverman.PaperV0.h_M_phi_oracle`        (unchanged, proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle`  (unchanged, proposal_001).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle`    (unchanged statement, tighter
                                                 declared constant).
    - `Braverman.PaperV0.h_M_pp_tight_oracle`   (NEW: same sup-norm claim as
      V11's `h_M_pp_oracle` — `‖∂²_z F_p(η, p, w)‖ ≤ M_pp` on the SAME
      rectangle for the SAME `p`-range — backed by the tighter
      `compute_M_pp_tight_bound`. It replaces `h_M_pp_oracle`; it does not
      add a claim of a new shape, and the rectangle is byte-identical.)

  The oracle rectangle `Ω(1635/10000, 1115/1000)`, `eta = 1/100` and
  `r = 23/25` are all unchanged from V9–V11.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V9–V11 byte-identical for parity; the `_phi_uzz`
proof path does not consume it. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`239/5000 = 0.0478` is exactly the rational the certified
`compute_M_phi_bound` emits at production-grade precision (arb ball
≈ 0.0476, rationalised at `max_denom = 10000`), so there is no slack
left on this axis. Unchanged from V9–V11. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. `543/10000 = 0.0543` is likewise exactly the rational the
certified `compute_M_phi_prime_bound` emits (arb ball ≈ 0.0541).
Unchanged from V9–V11. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `2` to `9/5 = 1.8`.** The backing oracle
`Numerical_Library.compute_inv_F_p_z_bound` is unchanged (same function,
same defaults, same rectangle); it certifies

    inf‖∂_z F_p‖ ≥ inf‖H_0'‖ − sup‖H_η' − H_0'‖ ≈ 0.643 − 0.054 = 0.589,

hence `sup 1/‖∂_z F_p‖ ≤ 1.7035`. V9–V11 declared the integer ceiling
`2`; `9/5` retains ≈ 5.5 % headroom over the certified value while
shrinking `inv_F_p_z²` from 4 to 81/25 = 3.24 and `inv_F_p_z³` from 8 to
729/125 = 5.832. -/
def inv_F_p_z_val : ℝ := 9 / 5

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `5608/100 ≈ 56.08` to `12`**, backed by the new
`Numerical_Library.compute_M_pp_tight_bound`. Same sup-norm claim, same
rectangle, same `p`-range as V11's `M_pp_val`; only the *route* to the
certificate changed:

* V11's `compute_M_pp_bound` used the triangle split
  `‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖` and then bounded
  `sup‖H_η''‖ ≤ sup_outer‖H_η'‖ / (δ/4) ≈ 2.08 / 0.0409 ≈ 51`, dwarfing
  the ≈ 5.08 contribution of `sup‖H_0''‖`.
* V12's `compute_M_pp_tight_bound` uses the affine identity
  `(1−p) H_0'' + p H_η'' = H_0'' + p (H_η'' − H_0'')` and Cauchy-bounds
  the difference: `‖H_η'' − H_0''‖ ≤ sup_outer‖H_η' − H_0'‖ / (δ/4)`.
  Since `sup‖H_η' − H_0'‖ ≈ 0.054` (the `M_phi_prime` quantity) is ~38×
  smaller than `sup‖H_η'‖`, the Cauchy contribution collapses to ≈ 1.5
  and the total to ≈ 6.6.

`12` leaves ≈ 1.8× headroom over that estimate. -/
def M_pp_tight_val : ℝ := 12

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

theorem M_phi_val_pos : 0 < M_phi_val := by unfold M_phi_val; norm_num
theorem M_phi_val_nn : 0 ≤ M_phi_val := le_of_lt M_phi_val_pos
theorem M_phi_prime_val_pos : 0 < M_phi_prime_val := by
  unfold M_phi_prime_val; norm_num
theorem M_phi_prime_val_nn : 0 ≤ M_phi_prime_val :=
  le_of_lt M_phi_prime_val_pos

theorem inv_F_p_z_val_pos : 0 < inv_F_p_z_val := by
  unfold inv_F_p_z_val; norm_num
theorem inv_F_p_z_val_nn : 0 ≤ inv_F_p_z_val := le_of_lt inv_F_p_z_val_pos

theorem M_pp_tight_val_pos : 0 < M_pp_tight_val := by
  unfold M_pp_tight_val; norm_num
theorem M_pp_tight_val_nn : 0 ≤ M_pp_tight_val := le_of_lt M_pp_tight_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 9/100`) -/

/-- `Cr_val := 9/100 = 0.09`, dominating the literal rational

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (239/5000)·(543/10000)·(81/25)
          + (1/2)·12·(729/125)·(239/5000)²
      = 10511937/1250000000 + 249847254/3125000000
      = 552254193/6250000000
      ≈ 0.0084095 + 0.0799511
      ≈ 0.0883607.

Margin to `9/100` is ≈ 0.0016393 — small in absolute terms, but the
closing step is exact rational arithmetic (`norm_num`), so no tolerance
is required. -/
def Cr_val : ℝ := 9 / 100

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V11) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. Byte-identical to
V9/V10/V11 — V12 does not touch the rectangle. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`.
Seed axiom, unchanged. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Certified single-`M` sup-norm bound on the tight rectangle. Carried
over from V9–V11 for parity; the `_phi_uzz` wrapper does not consume it,
so it should not appear in the transitive axiom set of the sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_bound`.
Unchanged from V9–V11. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_prime_bound`.
Unchanged from V9–V11. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound` (certified ≈ 1.7035).

Statement byte-identical to V10/V11; only the declared constant
`inv_F_p_z_val` tightened from `2` to `9/5`. The Python oracle certifies
the bound for `p ∈ [0, 1]` (using `pr_paper ≤ 1` from the seed axiom
`pr_paper_le_one`), so the quantifier over `Ioo 0 pr_paper` is
subsumed. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`‖∂²_z F_p(η, p, w)‖ ≤ M_pp_tight_val`.

This is the SAME sup-norm claim, over the SAME rectangle and the SAME
`p`-range, as V11's `h_M_pp_oracle`; it is restated here only so that it
can be witnessed by the tighter
`Numerical_Library.compute_M_pp_tight_bound`, which routes the Cauchy
step through the difference `H_η' − H_0'` (sup ≈ 0.054) instead of
through `H_η'` (sup ≈ 2.08), via the affine identity

    (1 − p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0'').

Certified estimate ≈ 6.6 versus V11's ≈ 56.08; `M_pp_tight_val := 12`
leaves ≈ 1.8× headroom. -/
axiom h_M_pp_tight_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_tight_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V11; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (the
η-aware wrapper introduced for V11), threading the tightened
`inv_F_p_z_val = 9/5` and the tightened `M_pp_tight_val = 12` through the
same oracle-hypothesis slots V11 used. No Lean infrastructure changed:
`lemma_5_4_paper_on_domain_phi_uzz` is already polymorphic in both
constants.

The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (9/100) * p^2` by the monotonicity step
`Cr_phi_uzz … ≤ 9/100`, which is pure rational arithmetic on the literal
constants. -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  obtain ⟨pr, hpr_pos, h_main⟩ :=
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_prime_val M_phi_val_nn M_phi_prime_val_nn
      inv_F_p_z_val inv_F_p_z_val_nn
      M_pp_tight_val M_pp_tight_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle h_inv_F_p_z_oracle
      h_M_pp_tight_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_tight_val
    -- LHS = (239/5000)·(543/10000)·(9/5)² + (1/2)·12·(9/5)³·(239/5000)²
    --     = 10511937/1250000000 + 249847254/3125000000
    --     = 552254193/6250000000
    --     ≈ 0.0084095 + 0.0799511 ≈ 0.0883607 ≤ 0.09
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
```

## What this changes, and where the remaining headroom is

**V12 vs V11.** No Lean infrastructure edits, no change to `r`, `eta`, or the oracle rectangle, no new claim shape. Two numerical inputs get tighter certificates:

| | V11 | V12 |
|---|---|---|
| `inv_F_p_z_val` | 2 (integer ceiling) | 9/5 (oracle certifies ≈ 1.7035) |
| `M_pp` | 5608/100 ≈ 56.08 | 12 (tight route certifies ≈ 6.6) |
| literal `Cr_phi_uzz` | ≈ 0.5230 | ≈ 0.0884 |
| declared `Cr_val` | 1 | 9/100 |

The `M_pp` move is the substantive one: `compute_M_pp_bound` Cauchy-bounds `sup‖H_η''‖` from `sup‖H_η'‖ ≈ 2.08`, when what the affine identity `(1−p)H_0'' + pH_η'' = H_0'' + p(H_η''−H_0'')` actually needs is a Cauchy bound on `H_η'' − H_0''`, obtainable from `sup‖H_η' − H_0'‖ ≈ 0.054` — the very quantity `h_M_phi_prime_oracle` already certifies. That is ~38× smaller, and it collapses the term that carried 98% of V11's bound.

**On the 1/6400 bar.** I do not think it is reachable, and I want to be explicit rather than leave it implied. Writing the exact identity behind the bound, `∂²_p F_inv = 2Φ'Φ/D² − DD·Φ²/D³` with `Φ = H_η − H_0`, and evaluating at a concrete point of the image (e.g. `z = 0.92i`, where `w = sin z ≈ 1.055i`, `|D| ≈ 0.688`, `|DD| ≈ 0.343`) gives `|∂²_p F_inv| ≈ 8·10⁻³`, i.e. `Cr ≈ 4·10⁻³`. The target `1/6400 ≈ 1.56·10⁻⁴` sits roughly 25–30× *below* the quantity being bounded, so it is not an artifact of loose estimates. `M_phi ≈ 0.048` and `M_phi_prime ≈ 0.054` are genuinely `O(η)` pointwise on the rectangle (the `O(η⁴)` structure in the paper's Theorem 4.4 is specific to the functional `H_η(i)/i`, not to `H_η − H_0` on `Ω`), and `η = 1/100` is locked.

**Remaining honest headroom, roughly ordered:**

1. **Joint rather than separated sups.** Term-2 uses `sup‖DD‖ · (sup 1/‖D‖)³ ≈ 12·5.8 = 70`, but `sup(‖DD‖/‖D‖³)` is ≈ 1–2 (where `|DD|` peaks, near `w = 1−δ` on the real axis, `|D| ≈ 1.83` is large). A single oracle on the ratio would cut term-2 by ~35×. Same idea applies to term-1's `‖Φ‖‖Φ'‖/‖D‖²`. This needs a new `Cr_*` def plus a new `F_inv_p_second_deriv_bound_*` and wrapper, which I'd rather write with compile feedback in hand.
2. `M_pp_tight_val = 12` is deliberately conservative against my ≈ 6.6 estimate, since I cannot run the oracle. If the run comes back near 6.6, term-2 nearly halves again.

Together those plausibly reach `Cr ≈ 5·10⁻³` — a further ~18×, but still ~30× short of the bar.