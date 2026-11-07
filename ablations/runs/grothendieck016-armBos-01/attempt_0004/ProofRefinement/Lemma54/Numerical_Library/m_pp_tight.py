"""M_pp_tight oracle: a tighter certified upper bound on

    M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)}
             ‖(1 − p) · H_0''(w) + p · H_η''(w)‖

i.e. on `sup ‖iteratedDeriv 2 (F_p η p) w‖`, the same quantity that
`m_pp.py` bounds — but via the *difference* decomposition rather than the
triangle split.

Why this is tighter
-------------------
`m_pp.py` splits

    ‖(1 − p) H_0'' + p H_η''‖ ≤ sup_Ω ‖H_0''‖ + sup_Ω ‖H_η''‖

and obtains the second summand by Cauchy's estimate on `H_η'` over a
`δ/4`-enlargement of `Ω`, i.e. `sup‖H_η'‖ / (δ/4)`. At the production
rectangle `Ω(1635/10000, 1115/1000)` that is `≈ 2.08 / 0.0409 ≈ 51`,
which is what makes its answer `≈ 56`.

Writing instead

    (1 − p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0'')

gives, for `p ∈ [0, p_max]`,

    ‖DD‖ ≤ sup_Ω ‖H_0''‖ + p_max · sup_Ω ‖H_η'' − H_0''‖
         ≤ sup_Ω ‖H_0''‖ + p_max · (sup_{Ω_d} ‖H_η' − H_0'‖) / d,

where `Ω_d` is `Ω` enlarged by `d` in both directions and the last step is
Cauchy's estimate applied to the analytic function `Φ' = H_η' − H_0'` on
the `d`-neighbourhood of `Ω`: for `w ∈ Ω` the closed `d`-disc about `w`
lies in `Ω_d`, so `|Φ''(w)| ≤ sup_{∂Ω_d} |Φ'| / d`. Requiring `d < δ`
keeps `Ω_d` inside the strip `S = {|Re| < 1}`, so `Φ'` stays analytic
there, and by the maximum-modulus principle scanning `∂Ω_d` suffices.

The gain is that `Φ'` is `O(η²)`: at `η = 1/100` the certified
`sup_Ω ‖Φ'‖ ≈ 0.054` (see `m_phi_prime.py`) versus `‖H_η'‖ ≈ 2`, so the
Cauchy summand shrinks by roughly 40×. The remaining summand
`sup_Ω ‖H_0''‖ = sup |w| / |1 − w²|^{3/2}` is `≈ 5.09`, attained on the
vertical edge at `w = (1 − δ) + 0i` (the horizontal edges give `≤ 0.73`,
since there `|1 − w²| ≥ 1.54`). Net: `≈ 6–8` in place of `≈ 56`.

Robustness
----------
Rather than fixing one enlargement, `compute_M_pp_tight_bound` evaluates
several (`d = δ/4`, `d = δ/2` by default) and returns the *minimum*
certified bound. Small `d` keeps `sup_{Ω_d} ‖Φ'‖` close to `sup_Ω ‖Φ'‖`
but inflates `1/d`; large `d` does the reverse, so the optimum is
interior and taking a min is insensitive to how fast `Φ'` grows off `Ω`.
Each enlargement is attempted independently: if one fails (e.g. the
`H_η` series is evaluated too far out), it is skipped and the others
still produce an answer. Only if *every* enlargement fails does the
function raise.

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper …),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_tight_val

The `p_max = 1` default covers `Ioo 0 pr_paper` via the seed axiom
`Braverman.Paper.pr_paper_le_one`.
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
    d_div: int,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified `sup_{Ω} ‖DD‖` pipeline at one enlargement `d = δ/d_div`."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ‖H_0''(w)‖ on ∂Ω via the closed form H_0''(w) = w / (1 − w²)^{3/2}.
    #    (rsqrt(u) = u^{-1/2}, so u^{-3/2} = rsqrt(u) / u.)
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(H0_double_prime, delta_arb, B_arb, n_per_edge, prec)

    # 2. Cauchy on Φ' = H_η' − H_0' over the d-enlarged rectangle
    #    Ω_d = Ω(δ − d, B + d).  Need d < δ so that Ω_d ⊆ S.
    d = delta_arb / arb(d_div)
    delta_outer = delta_arb - d
    B_outer = B_arb + d

    if not certified_positive(delta_outer):
        raise ValueError(
            f"enlarged rectangle degenerate for d_div={d_div}: "
            f"delta_outer = {delta_outer}"
        )

    def phi_prime_abs_ub(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H_0_p)

    max_phi_prime_outer = _max_on_rect(
        phi_prime_abs_ub, delta_outer, B_outer, n_per_edge, prec
    )
    max_phi_pp = max_phi_prime_outer / d

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
        "d_div": d_div,
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
    d_divisors: tuple = (4, 2),
    n_per_edge: int = 512,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on `M_pp = sup_Ω ‖∂²_z F_p‖`, uniform
    in `p ∈ [0, p_max]`, via the difference decomposition.

    Defaults match the V9–V12 oracle rectangle `Ω(1635/10000, 1115/1000)`
    and `p_max = 1` (which subsumes `Ioo 0 pr_paper`, since
    `pr_paper ≤ 1`). Each entry of `d_divisors` gives one enlargement
    `d = δ / d_div`; the smallest certified bound among the enlargements
    that succeed is returned.

    Performance: two `_max_on_rect` boundary scans per enlargement at
    `n_per_edge=512`, `prec=200` — the same complexity profile as
    `compute_M_pp_bound`. Results are JSON-cached per enlargement in
    `.cache/`, so re-verification on later audits is cheap.
    """
    best_bound = None
    best_cached = None
    failures: list = []

    for d_div in d_divisors:
        key = {
            "fn": "compute_M_pp_tight_bound",
            "eta": eta,
            "delta": delta,
            "B": B,
            "p_max": p_max,
            "d_div": d_div,
            "n_per_edge": n_per_edge,
            "prec": prec,
            "K_max": K_max,
        }
        try:
            cached = cached_run(
                key,
                lambda: _compute_M_pp_tight_for_params(
                    eta=eta,
                    delta=delta,
                    B=B,
                    p_max=p_max,
                    d_div=d_div,
                    n_per_edge=n_per_edge,
                    prec=prec,
                    K_max=K_max,
                ),
            )
            flint_ctx.prec = prec
            M_pp_arb = arb(cached["M_pp_str"])
            candidate = arb_to_rational_ub(
                M_pp_arb,
                safety_rel=safety_rel,
                safety_abs=safety_abs,
                max_denom=max_denom,
            )
        except Exception as exc:  # one bad enlargement must not sink the oracle
            failures.append(f"d_div={d_div}: {exc!r}")
            continue

        if best_bound is None or candidate < best_bound:
            best_bound = candidate
            best_cached = cached

    if best_bound is None:
        raise RuntimeError(
            "compute_M_pp_tight_bound: every enlargement failed: "
            + "; ".join(failures)
        )

    return OracleResult(
        bound=best_bound,
        ball_value=best_cached["M_pp_upper_float"],
        prec=best_cached["prec"],
        meta={
            "delta": best_cached["delta"],
            "B": best_cached["B"],
            "p_max": best_cached["p_max"],
            "d_div": best_cached["d_div"],
            "n_per_edge": best_cached["n_per_edge"],
            "K_max": best_cached["K_max"],
            "M_pp_arb_str": best_cached["M_pp_str"],
            "max_H0_pp_arb_str": best_cached["max_H0_pp_str"],
            "max_phi_prime_outer_arb_str": best_cached["max_phi_prime_outer_str"],
            "max_phi_pp_arb_str": best_cached["max_phi_pp_str"],
            "enlargements_tried": list(d_divisors),
            "enlargement_failures": failures,
        },
    )
