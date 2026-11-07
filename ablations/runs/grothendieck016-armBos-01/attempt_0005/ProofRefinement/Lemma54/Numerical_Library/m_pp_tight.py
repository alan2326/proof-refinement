"""M_pp_tight oracle: a strictly tighter certificate for the SAME sup-norm
claim that `m_pp.py` backs, namely

    M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖(1−p) H_0''(w) + p H_η''(w)‖
         = sup_{(p, w)} ‖∂²_z F_p(η, p, w)‖.

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper …),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_tight_val

with the same domain `oracle_domain = Braverman.Omega delta_val B_val` and
the same quantity as `h_M_pp_oracle`. Nothing about the claim is weakened;
only the numerical route to it is sharper.

Why `m_pp.py` is loose
----------------------
`m_pp.py` uses the triangle split

    ‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

and then bounds `sup‖H_η''‖` by Cauchy on `H_η'` over the enlarged
rectangle: `sup_{∂Ω_outer}‖H_η'‖ / d` with `d = δ/4`. At the production
rectangle Ω(1635/10000, 1115/1000) that is ≈ 2.082 / 0.040875 ≈ 51 — the
*whole* size of `H_η'`, which is ≈ `H_0'` and has nothing to do with η. The
`H_0''` term contributes only ≈ 5.08, so the certificate lands at ≈ 56.

The tighter decomposition
-------------------------
`F_p` is affine in `p`, so

    DD(η, p, w) = ∂²_z F_p = H_0''(w) + p · (H_η − H_0)''(w),

whence, for `p ∈ [0, p_max]`,

    ‖DD‖ ≤ sup_Ω ‖H_0''‖ + p_max · sup_Ω ‖(H_η − H_0)''‖            (1)
         ≤ sup_Ω ‖H_0''‖ + p_max · sup_{Ω_outer} ‖H_η' − H_0'‖ / d.  (2)

(1) is the triangle inequality on the affine family; `p_max = 1` is licensed
on the Lean side by the seed axiom `pr_paper_le_one`. (2) is Cauchy's
estimate for a second derivative: for `w ∈ Ω`, the closed disk of radius `d`
about `w` lies in `Ω_outer = Ω(δ − d, B + d)` (which widens the real half-
width by exactly `d` and the imaginary half-height by exactly `d`), and
`H_η − H_0` is analytic on the closure of `Ω_outer` because
`|Re w| ≤ 1 − (δ − d) < 1`. Sup on `∂Ω_outer` bounds sup on the closure by
max-modulus — the same justification `m_pp.py` and `m_phi.py` already rely on.

The point is that (2) measures the η-deformation rather than `H_η'` itself:
`sup_Ω ‖H_η' − H_0'‖ ≈ 0.054` (the `M_phi_prime` quantity), growing only
mildly on the slightly larger `Ω_outer`, so the second summand drops from
≈ 51 to ≈ 1.5–2.5 and the total from ≈ 56.0 to ≈ 6.6–7.6.

Both summands are computed with the same primitives `m_pp.py` uses, so this
module adds no new numerical machinery — only a different (sharper) algebraic
split before the interval arithmetic.
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
    """Run the certified `sup_{[0,p_max] × Ω} ‖∂²_z F_p‖` pipeline via the
    η-aware split (1)–(2) of the module docstring."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # --- Term 1: sup ‖H_0''(w)‖ on ∂Ω via the closed form
    #             H_0''(w) = w · (1 − w²)^{−3/2}.
    # `H_0''` is analytic on the closure of Ω (its only singularities are at
    # w = ±1, and |Re w| ≤ 1 − δ < 1), so the boundary scan bounds the sup on
    # Ω̄ by max-modulus. Same expression as m_pp.py's first component.
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 − w²
        # rsqrt(u) = u^{−1/2}, so u^{−3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # --- Term 2: sup ‖(H_η − H_0)''(w)‖ on Ω via Cauchy on Ω_outer.
    # d = δ/4 matches m_pp.py's enlargement, so the enlarged rectangle here is
    # exactly the one m_pp.py already evaluates the phi-series on.
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d   # widens the real half-width by d
    B_outer = B_arb + d           # widens the imaginary half-height by d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the (H_η − H_0)'' Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H0_p)

    max_phi_prime_outer = _max_on_rect(
        phi_prime, delta_inner, B_outer, n_per_edge, prec,
    )
    max_phi_pp = max_phi_prime_outer / d

    # --- Combine per (1): ‖DD‖ ≤ sup‖H_0''‖ + p_max · sup‖(H_η − H_0)''‖.
    M_pp_arb = max_H0_pp + p_max_arb * max_phi_pp

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_phi_prime_outer_str": max_phi_prime_outer.str(20, more=True),
        "max_phi_pp_str": max_phi_pp.str(20, more=True),
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
    n_per_edge: int = 512,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    `M_pp = sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖∂²_z F_p(η, p, w)‖`,
    via the η-aware split of the module docstring.

    Defaults match the V9–V12 oracle rectangle (`δ = 1635/10000`,
    `B = 1115/1000`) and `p_max = 1` (licensed on the Lean side by the seed
    axiom `pr_paper_le_one`). Precision settings mirror
    `compute_inv_F_p_z_bound` (`n_per_edge = 512`, `prec = 200`,
    `K_max = 80`), which is known to evaluate the phi-series happily on the
    enlarged rectangle. Callable with no arguments; the JSON cache in
    `.cache/` makes repeat calls free.

    Expected magnitude at the pinned defaults: `sup_Ω‖H_0''‖ ≈ 5.08`
    (attained on ∂Ω at `Re w = 1 − δ`, `Im w = 0`) plus
    `sup_{Ω_outer}‖H_η' − H_0'‖ / d ≈ 0.06–0.10 / 0.040875 ≈ 1.5–2.5`,
    for a total ≈ 6.6–7.6 — versus ≈ 56.0 from `compute_M_pp_bound`.
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
            "max_phi_prime_outer_arb_str": cached["max_phi_prime_outer_str"],
            "max_phi_pp_arb_str": cached["max_phi_pp_str"],
        },
    )
