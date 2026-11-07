# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_at_acb`-family helpers from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The bound returned inherits
# an unbounded heuristic step.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the bug write-up, the truncation-free replacement infrastructure
# (Scratch/h_pp_complex_certified.py — Price 2nd-derivative formula;
# Scratch/phi_pp_chunk_bound_eta_tight.py — η²-tight chunk bound,
# post-anisotropic-Gaussian, post-λ-decay-fix), and the binding rules
# R1–R5. The Evaluator's G7.a will fail any candidate whose oracle path
# reaches `eval_H_eta_*at_acb`.
# =============================================================================
"""M_pp oracle: certified upper bound on

    M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖(1−p) H_0''(w) + p · H_η''(w)‖

This is `sup ‖iteratedDeriv 2 (F_p η p) w‖` — the second `w`-derivative of
the joint family `F_p(η, p, w) = (1−p) H_0(w) + p H_η(w)` over the oracle
rectangle.

In `Lemma54_Paper_Pderiv_Single.lean`, the bound `‖u_zz‖ ≤ 8R/(1−r)²`
(Cauchy on disk r₂) is currently used to bound the second z-derivative of
F_inv. By the implicit-function chain `u_zz = −F_ww · h_z² / D` (line 86
of that file) with `h_z = 1/D`, we have `‖u_zz‖ = ‖F_ww‖ / ‖D‖³ ≤
M_pp · invFp³` where `invFp = 2R/(1−r)`. The new oracle replaces the
direct Cauchy on F_inv with this two-step indirect bound, which is tighter
when `M_pp · invFp³ < 8R/(1−r)²`, i.e. `M_pp < (1−r)/R²`.

Backs the proposed Lean axiom

    axiom h_M_pp_oracle :
      ∀ p ∈ Set.Ico (0 : ℝ) p_max_val,
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_val

Implementation: triangle bound

    M_pp ≤ sup_{Ω} ‖H_0''(w)‖ + sup_{Ω} ‖H_η''(w)‖

with:
  - sup ‖H_0''‖: direct point-eval (closed form `H_0''(w) = w/(1−w²)^{3/2}`)
  - sup ‖H_η''‖: Cauchy on enlarged rectangle (mirrors existing M oracle's
    treatment of H_η').

The triangle bound is sound for any `p ∈ [0, 1]` and is tight up to
cancellation (which we don't try to exploit here).
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_deriv_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_pp_for_params(
    eta: float,
    delta: str,
    B: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{Ω} ‖F_ww‖ pipeline."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ‖H_0''(w)‖ on dΩ via closed form: H_0''(w) = w/(1−w²)^{3/2}.
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 − w²
        # rsqrt(u) = u^{−1/2}; so u^{−3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # 2. sup ‖H_η''(w)‖ on dΩ via Cauchy on enlarged rectangle.
    # Use d = δ/4 (matches existing compute_M_rigorous's enlargement).
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d   # = 3δ/4
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for H_η'' Cauchy bound: "
            f"delta_inner = {delta_inner}"
        )

    # sup ‖H_η'‖ on enlarged dΩ(δ-d, B+d).
    def H_eta_prime(z: acb) -> arb:
        return abs_ub(eval_H_eta_deriv_at_acb(phi_series, z, prec))

    max_H_eta_prime_outer = _max_on_rect(
        H_eta_prime, delta_inner, B_outer, n_per_edge, prec,
    )
    max_H_eta_pp = max_H_eta_prime_outer / d

    M_pp_arb = max_H0_pp + max_H_eta_pp

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_H_eta_pp_str": max_H_eta_pp.str(20, more=True),
        "delta": delta,
        "B": B,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on M_pp = sup_{Ω} ‖F_ww‖.

    See module docstring for the math. Defaults match the V8 oracle rectangle.
    First call is ~60–120s (cold cache, two _max_on_rect scans on different
    rectangles); cached thereafter.
    """
    key = {
        "fn": "compute_M_pp_bound",
        "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_for_params(
        eta=eta, delta=delta, B=B,
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
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_H_eta_pp_arb_str": cached["max_H_eta_pp_str"],
        },
    )
