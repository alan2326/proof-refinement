# =============================================================================
# DEPRECATED 2026-05-03 — non-rigorous (K_max truncation).
#
# This oracle calls `eval_H_eta_*at_acb` family from
# `grothendieck.proof.certified.compute_cr_v2`, which truncates the φ-series
# at K_max terms with no rigorous tail bound. The merged_uderiv bound
# inherits an unbounded heuristic step — and because V25/V26 declare
# Cr_val = 1/240000 .. 1/268000 (~10⁻⁶ scale), the heuristic 10⁻⁸ tail
# claim is at most one order of magnitude away from the certified bound
# itself. The K_max-era win in V25/V26 is not rigorous.
#
# Do NOT use in new candidates. See ProofRefinement/Lemma54/PATCH_NOTES.md
# for the truncation-free replacement: Scratch/joint_merged_uderiv.py
# (with denom-fix + 2nd-order Taylor pad + Cauchy M_phi_ppp +
# min(interval, norm) + λ-decay-fix + anisotropic-Gaussian patches; see
# §2c of PATCH_NOTES). The Evaluator's G7.a will fail any candidate
# whose oracle path reaches `eval_H_eta_*at_acb`.
# =============================================================================
"""merged_uderiv oracle: certified upper bound on the *exact* `|u''|` quotient

    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)}
        ‖2·Phi(w)·Phi'(w)·D(p, w) − DD(p, w)·Phi(w)²‖ / ‖D(p, w)‖³

where
    Phi(w)     = H_eta(w) − H_0(w)
    Phi'(w)    = H_eta'(w) − H_0'(w)
    D(p, w)    = (1−p)·H_0'(w)  + p·H_eta'(w)
    DD(p, w)   = (1−p)·H_0''(w) + p·H_eta''(w)

By the form-A identity (Proof/Lib/Lemma54_Paper_Pderiv_Single.lean:546-557)
combined with the closed form `u'(p, z) = -Phi(w(p,z))/D(p, w(p,z))`,

    D · u'' + 2·Phi'·u' + DD·u'·u' = 0
        ⇒ D · u'' = -(2·Phi'·u' + DD·u'·u')
                  = -(2·Phi'·(-Phi/D) + DD·Phi²/D²)
                  = (2·Phi·Phi'/D − DD·Phi²/D²),
        ⇒ u'' = (2·Phi·Phi'·D − DD·Phi²) / D³.

Hence ‖u''‖ = ‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³ exactly.

Triangle on the merged numerator gives the V23 active bound

    ‖u''‖ ≤ 2·‖Phi·Phi'/D²‖ + ‖DD·Phi²/D³‖
         = 2·joint_phi_phip_invD2 + uzz_phi_sq

(see Numerical_Library/{joint_phi_phip_invD2,uzz_phi_sq}.py). The merged
oracle here keeps the difference inside one acb interval per cell, so
destructive interference between `2·Phi·Phi'·D` and `DD·Phi²` (which have
opposite signs at our (η, r) configuration) is captured cell-by-cell
rather than discarded by triangle splitting. Empirically (sprint_030
verification probe at n_per_edge=262144), the merged sup is `~0.871`×
the naive triangle sum, giving a `~1.15×` direct factor on the active
bound that translates into an ~1.16× win on `Cr_val`.

Backs the proposed Lean axiom

    axiom h_merged_uderiv_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper ...),
      ∀ w ∈ oracle_domain,
        ‖2 * Phi(w) * Phi'(w) * D(p, w) - DD(p, w) * Phi(w)^2‖
          ≤ ‖D(p, w)‖^3 * merged_uderiv_val

(equivalently `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³ ≤ merged_uderiv_val`).

Strategy. We scan the boundary `∂Ω` in `w` at high resolution. For each
`w`-cell, the per-cell numerator merges the two terms inside a single
acb interval (so any common sign is preserved by interval cancellation),
the divisor `|D|^3` and numerator-multiplicand `D` and `DD` are
subdivided in `p` for tighter D-bounds. The per-cell ratio
`abs_ub(2·Phi·Phi'·D − DD·Phi²) / abs_lb(D)^3` upper-bounds the merged
quotient on the cell. The max over cells is a certified upper bound on
the joint sup.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_lb, abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _iter_rect_boundary
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_at_acb,
    eval_H_eta_deriv_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult
from .u_zz import _eval_H_eta_p_pp_at_acb


def _H0_at_acb(w: acb) -> acb:
    """H_0(w) = arcsin(w)."""
    return w.asin()


def _H0_prime_at_acb(w: acb) -> acb:
    """H_0'(w) = (1 − w²)^{−1/2}."""
    return (acb(1) - w * w).rsqrt()


def _H0_pp_at_acb(w: acb) -> acb:
    """H_0''(w) = w · (1 − w²)^{−3/2}."""
    u = acb(1) - w * w
    return w * u.rsqrt() / u


def _compute_merged_uderiv_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    n_p_subdiv: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{p,w} ‖2·Phi·Phi'·D − DD·Phi²‖/‖D‖³ pipeline.

    For each w-cell on ∂Ω(δ, B):
      - compute `Phi_iv = H_eta(w) - H_0(w)` (p-independent),
        `Phi_p_iv = H_eta'(w) - H_0'(w)` (p-independent),
        `Phi_sq = Phi_iv * Phi_iv` (p-independent).
      - compute `H_0', H_0'', H_eta', H_eta''` at w (all p-independent).
      - For each p-subinterval `[p_lo, p_hi] ⊂ [0, p_max]`:
        - `D_iv  = H_0'  + p_iv · (H_eta' - H_0')`,
          `DD_iv = H_0'' + p_iv · (H_eta'' - H_0'')`.
        - `|D|_lb = abs_lb(D_iv)`, abort if non-positive.
        - merged numerator (single acb interval — destructive-interference
          aware): `num = 2·Phi·Phi_p·D - DD·Phi²`.
        - per-cell ratio = `abs_ub(num) / |D|_lb^3`.
        - track running max.

    The global max is a certified upper bound on the joint sup.
    """
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    max_g = arb(0)
    n_failed = 0
    n_total = 0
    for w_acb in _iter_rect_boundary(delta_arb, B_arb, n_per_edge, prec):
        # Phi, Phi' are p-independent.
        H0_v = _H0_at_acb(w_acb)
        H_eta_v = eval_H_eta_at_acb(phi_series, w_acb, prec)
        Phi_iv = H_eta_v - H0_v

        H0_p_val = _H0_prime_at_acb(w_acb)
        H0_pp_val = _H0_pp_at_acb(w_acb)
        H_eta_p_val = eval_H_eta_deriv_at_acb(phi_series, w_acb, prec)
        He_p_val_b, He_pp_val = _eval_H_eta_p_pp_at_acb(phi_series, w_acb)

        Phi_p_iv = H_eta_p_val - H0_p_val
        D_diff = H_eta_p_val - H0_p_val
        DD_diff = He_pp_val - H0_pp_val

        Phi_sq = Phi_iv * Phi_iv

        for j in range(n_p_subdiv):
            p_lo = p_max_arb * arb(j) / arb(n_p_subdiv)
            p_hi = p_max_arb * arb(j + 1) / arb(n_p_subdiv)
            p_iv = arb.union(p_lo, p_hi)

            D_iv = H0_p_val + acb(p_iv) * D_diff
            DD_iv = H0_pp_val + acb(p_iv) * DD_diff

            D_lb = abs_lb(D_iv)
            if not certified_positive(D_lb):
                n_failed += 1
                n_total += 1
                continue

            # Merged numerator: 2·Phi·Phi'·D − DD·Phi² (single acb interval).
            num = acb(2) * Phi_iv * Phi_p_iv * D_iv - DD_iv * Phi_sq
            num_ub = abs_ub(num)

            denom_lb_cube = D_lb ** 3
            ratio = num_ub / denom_lb_cube
            max_g = arb.max(max_g, ratio)
            n_total += 1

    if n_failed > 0:
        raise ValueError(
            f"compute_merged_uderiv_bound: {n_failed}/{n_total} cells "
            f"could not certify |D|>0; increase n_per_edge or n_p_subdiv."
        )

    return {
        "merged_uderiv_str": max_g.str(20, more=True),
        "merged_uderiv_upper_float": float(max_g.upper()),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "n_p_subdiv": n_p_subdiv,
        "prec": prec,
        "K_max": K_max,
        "n_total": n_total,
    }


def compute_merged_uderiv_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 1048576,
    n_p_subdiv: int = 4,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 100000000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-9,
) -> OracleResult:
    """Certified rational upper bound on
    sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³.

    Defaults match the V23 oracle rectangle (δ = 1635/10000,
    B = 1115/1000) and `p_max = 1` (uses the `pr_paper ≤ 1` seed
    axiom for the universal quantifier in the corresponding Lean axiom).

    Default `n_per_edge=1048576` (sprint_032 doubling from V26's 524288):
    at this resolution, sprint_032's Generator verification probe measures
    the merged sup; the per-doubling history is
    `n=131072: 9.7548e-6`, `n=262144: 8.0865e-6` (-17.1%),
    `n=524288: 7.3095e-6` (-9.6%), `n=1048576: ~6.6-6.8e-6` projected
    (-7-9% deceleration). For comparison the naive triangle sum
    `2·joint + uzz_phi_sq` is near `9.0·10⁻⁶`; the merged formulation
    captures destructive-interference savings inside one acb interval
    per cell. Lower resolutions (e.g. `n_per_edge=131072`) give merged
    sup `≈ 9.755·10⁻⁶`, *worse* than the V23 triangle bound — destructive-
    interference savings only overcome the per-cell interval slack at
    n_per_edge ≥ 262144.

    Note `safety_abs = 1e-9` and `max_denom = 100000000` (sprint_032
    rationaliser tightening from V26's `safety_abs=1e-8, max_denom=1e7`):
    the finer rationaliser reduces the rationalisation slack from ~1.2%
    (at 1e-8/1e7) to ~0.14% (at 1e-9/1e8), composing multiplicatively
    with the resolution doubling for a tighter declared bound.

    Performance: scans 4·n_per_edge·n_p_subdiv ≈ 16.78M cells at
    n_per_edge=1048576, prec=200; sprint_032 verify-probe projected
    `~2050s` fresh on the Generator host (vs ~989s at n=524288).
    Cache populated.
    """
    key = {
        "fn": "compute_merged_uderiv_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "n_p_subdiv": n_p_subdiv,
        "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_merged_uderiv_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, n_p_subdiv=n_p_subdiv,
        prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    merged_arb = arb(cached["merged_uderiv_str"])
    bound = arb_to_rational_ub(
        merged_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["merged_uderiv_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "n_p_subdiv": cached["n_p_subdiv"],
            "K_max": cached["K_max"],
            "n_total": cached["n_total"],
            "merged_uderiv_arb_str": cached["merged_uderiv_str"],
        },
    )
