# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_*at_acb` family from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The bound inherits an
# unbounded heuristic step.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the truncation-free replacement (Scratch/joint_merged_uderiv.py
# computes inf|D| = inf|H_0'| − p_hi · M_phi_p chunk-by-chunk using the
# truncation-free chunk bounds), the cached round-3 chunks, and the
# binding rules R1–R5. The Evaluator's G7.a will fail any candidate whose
# oracle path reaches `eval_H_eta_*at_acb`.
# =============================================================================
"""inv_F_p_z oracle: certified upper bound on

    inv_F_p_z = sup_{p ∈ [0, 1], w ∈ Ω(δ, B)}
                  1 / ‖(1−p) · H_0'(w) + p · H_η'(w)‖

This bounds `1 / ‖∂_z F_p(η, p, w)‖` uniformly in `p ∈ [0, 1]` and
`w ∈ Ω(δ, B)`. The current paper-faithful Step 5 derivation
(`F_p_deriv_lower_bound_at_F_inv` in `Lemma54_Paper_Identity.lean`)
gives the loose bound `‖D‖ ≥ (1−r)/(2R)`, hence `1/‖D‖ ≤ 2R/(1−r) ≈
28.75` at the candidate parameters. At η = 1/100 the actual sup of
`1/‖D‖` over the oracle rectangle is ≈ 1.85 (η = p = 0 limit gives
≈ 1.55, the η/p perturbation adds ≈ 0.30), so this oracle replaces the
14× loose paper bound with a direct arb-certified ≈ 2.

Backs the proposed Lean axiom

    axiom h_inv_F_p_z_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper η_val r_val ...),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p η_val p) w‖ * inv_F_p_z_val

(equivalently `1/‖∂_z F_p(η, p, w)‖ ≤ inv_F_p_z_val`).

Strategy. Use the decomposition

    D(η, p, w) = H_0'(w) + p · (H_η'(w) − H_0'(w))

so that

    ‖D‖ ≥ ‖H_0'(w)‖ − p · ‖H_η'(w) − H_0'(w)‖
        ≥ inf_w ‖H_0'(w)‖ − p_max · sup_w ‖H_η'(w) − H_0'(w)‖
        ≥ inf_w ‖H_0'(w)‖ − M_phi_prime

at `p_max = 1` (since `pr_paper ≤ 1` per the seed axiom
`pr_paper_le_one`). The first term `inf_w ‖H_0'(w)‖` is bounded below
by certified arb on the rectangle (closed form
`H_0'(w) = (1 − w²)^{−1/2}`, attaining minimum on the corner
`u = 1−δ, v = B`). The second term `M_phi_prime ≈ 0.054` is the same
quantity certified by `compute_M_phi_prime_bound`; we re-bound it here
inline (we don't import the cached result, to keep the oracle
self-contained).

The returned bound is `1 / inf‖D‖`, rationalised by
`arb_to_rational_ub` exactly as the other oracles in this module.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_lb, abs_ub
from grothendieck.proof.certified.certify_invertibility import (
    _max_on_rect,
    _min_on_rect,
)
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_deriv_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_inv_F_p_z_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} 1/‖∂_z F_p(η,p,w)‖ pipeline.

    Computes `1 / inf‖D‖` where `inf‖D‖ ≥ inf‖H_0'‖ − p_max · sup‖H_η' − H_0'‖`.
    """
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. inf ‖H_0'(w)‖ over Ω(δ, B). H_0'(w) = (1 − w²)^{−1/2}.
    #    A certified lower bound on |1/sqrt(1-w²)|.
    def H0_prime_abs_lb(z: acb) -> arb:
        # H_0'(z) = (1 − z²)^{−1/2}; lower bound on its absolute value.
        H0p = (acb(1) - z * z).rsqrt()
        return abs_lb(H0p)

    inf_H0p_arb = _min_on_rect(H0_prime_abs_lb, delta_arb, B_arb,
                               n_per_edge, prec)

    # 2. sup ‖H_η'(w) − H_0'(w)‖ over Ω(δ, B) (the M_phi_prime quantity).
    def phi_prime_abs_ub(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H0_p)

    sup_phi_prime_arb = _max_on_rect(phi_prime_abs_ub, delta_arb, B_arb,
                                     n_per_edge, prec)

    # 3. Lower bound on inf‖D(η, p, w)‖ for p ∈ [0, p_max], w ∈ Ω(δ, B):
    #      ‖D‖ ≥ ‖H_0'‖ − p · ‖H_η' − H_0'‖
    #           ≥ inf‖H_0'‖ − p_max · sup‖H_η' − H_0'‖
    inf_D_arb = inf_H0p_arb - p_max_arb * sup_phi_prime_arb

    # 4. The oracle bound: 1 / inf‖D‖ — an upper bound on sup 1/‖D‖.
    #    arb division returns an arb whose upper bound contains 1/inf‖D‖.
    inv_F_p_z_arb = arb(1) / inf_D_arb

    return {
        "inv_F_p_z_str": inv_F_p_z_arb.str(20, more=True),
        "inv_F_p_z_upper_float": float(inv_F_p_z_arb.upper()),
        "inf_H0p_str": inf_H0p_arb.str(20, more=True),
        "sup_phi_prime_str": sup_phi_prime_arb.str(20, more=True),
        "inf_D_str": inf_D_arb.str(20, more=True),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_inv_F_p_z_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 512,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    inv_F_p_z = sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} 1/‖(1−p) H_0'(w) + p H_η'(w)‖.

    Defaults match the V9 oracle rectangle (`δ = 1635/10000, B = 1115/1000`)
    and `p_max = 1` (uses the `pr_paper ≤ 1` seed axiom for the universal
    quantifier in the corresponding Lean axiom).

    Performance: scans the rectangle boundary at `n_per_edge=512` with `prec=200`,
    same complexity profile as `compute_M_phi_prime_bound`.
    """
    key = {
        "fn": "compute_inv_F_p_z_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_inv_F_p_z_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    inv_F_p_z_arb = arb(cached["inv_F_p_z_str"])
    bound = arb_to_rational_ub(
        inv_F_p_z_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["inv_F_p_z_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "inv_F_p_z_arb_str": cached["inv_F_p_z_str"],
            "inf_H0p_arb_str": cached["inf_H0p_str"],
            "sup_phi_prime_arb_str": cached["sup_phi_prime_str"],
            "inf_D_arb_str": cached["inf_D_str"],
        },
    )
