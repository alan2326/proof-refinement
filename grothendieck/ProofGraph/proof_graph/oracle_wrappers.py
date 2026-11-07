"""Thin wrappers around `grothendieck.proof.certified` so each proof-graph
node maps to a single callable that returns a dict.

Each wrapper here corresponds to one node in `ProofGraph/nodes/`. The
underlying certified-arb functions sometimes require a 2-step composition
(e.g., `choose_rho` then `compute_M_rho`); the wrapper composes them and
exposes the relevant outputs as a dict.

Naming convention: `<slug>_pipeline` — matches the proof-graph node slug.
"""

from __future__ import annotations

from typing import Any


def certify_invertibility_with_override(
    r: float, eta: float, p_override: str | None = None,
    delta_override: str | None = None, B_override: str | None = None,
    prec: int = 128, verbose: bool = False,
) -> dict[str, Any]:
    """Run Step 1 with either auto-chosen or user-specified rectangle data,
    then (optionally) replace its certified `p` with a smaller user-supplied
    value.

    The override is sound because Rouche's theorem applies for any
    `p ≤ p_certified`; downstream Taylor bounds become tighter as p shrinks.

    When `delta_override` / `B_override` are supplied, the Step 1 checks are
    rerun on that exact rational rectangle rather than on the auto-chosen one.
    This lets Lean and Python share the same explicit oracle domain.

    Outputs:
        r       : arb       — radius of the target disk.
        p       : arb       — possibly overridden p (≤ p_certified).
        p_certified : arb   — original p from `certify_invertibility`.
        delta, B   : arb    — Rouche rectangle parameters.
    """
    from flint import arb, ctx as flint_ctx
    from grothendieck.proof.certified.certify_invertibility import (
        certify_invertibility,
        certify_sin_r_disk_in_omega,
        compute_rouche_margin_omega,
        compute_perturbation_bound_omega,
        choose_p,
    )
    from grothendieck.proof.certified.arb_utils import certified_positive, certified_lt

    use_fixed_domain = bool(str(delta_override or "").strip()) or bool(str(B_override or "").strip())
    if not use_fixed_domain:
        res = dict(certify_invertibility(r=r, eta=eta, prec=prec, verbose=verbose))
    else:
        if not (str(delta_override or "").strip() and str(B_override or "").strip()):
            raise ValueError("delta_override and B_override must be provided together")
        old_prec = flint_ctx.prec
        flint_ctx.prec = prec
        try:
            r_arb = arb(str(r))
            r_outer = (arb(1) + r_arb) / arb(2)
            delta = arb(str(delta_override))
            B = arb(str(B_override))

            if verbose:
                print(f"Step 1: Certifying analytic invertibility on fixed rectangle")
                print(f"  r = {r}, r_outer = (1+r)/2 = {r_outer}")
                print(f"  Omega: delta={delta}, B={B}")

            check = certify_sin_r_disk_in_omega(r_outer, delta, B, prec)
            if not (check["imaginary_check"] and check["real_check"]):
                raise RuntimeError(
                    f"Containment check failed at fixed rectangle delta={delta}, B={B}: "
                    f"im={check['imaginary_check']}, re={check['real_check']}"
                )

            margin = compute_rouche_margin_omega(r_outer, delta, B, prec=prec)
            if not certified_positive(margin):
                raise RuntimeError(
                    f"Rouche margin not certified positive at fixed rectangle delta={delta}, B={B}: "
                    f"m = {margin}"
                )

            M_partial = compute_perturbation_bound_omega(
                delta, B, prec=prec, verbose=verbose,
            )
            p_certified = choose_p(margin, M_partial)
            rouche_ok = certified_lt(p_certified * M_partial, margin)

            res = {
                "r": r_arb,
                "r_outer": r_outer,
                "delta": delta,
                "B": B,
                "n": 0,
                "containment_check": check,
                "margin": margin,
                "M_partial": M_partial,
                "p": p_certified,
                "rouche_ok": rouche_ok,
                "all_checks_passed": (
                    check["imaginary_check"] and check["real_check"]
                    and certified_positive(margin) and rouche_ok
                ),
            }
        finally:
            flint_ctx.prec = old_prec

    res["p_certified"] = res["p"]
    if p_override is not None and str(p_override).strip():
        res["p"] = arb(str(p_override))
    return res


def compute_phi_taylor_pipeline(
    b_series_path: str, K_max: int = 50, prec: int = 128, verbose: bool = False
) -> dict[str, Any]:
    """Load the cached b-series and compute φ Taylor coefficients.

    Outputs:
        h_eta_series : arb_series — H_η Taylor series (centered at 0).
        phi          : arb_series — φ(z) := (z − H_η(sin z))·cos z.
    """
    from grothendieck.proof.certified.h_eta_evaluator import load_b_series_from_json
    from grothendieck.proof.certified.phi_taylor import compute_phi_coefficients
    h_eta_series = load_b_series_from_json(
        b_series_path, K_max=K_max, prec=prec, verbose=verbose,
    )
    phi = compute_phi_coefficients(h_eta_series, K_max, prec, verbose=verbose)
    return {"h_eta_series": h_eta_series, "phi": phi}


def compute_m_rho_pipeline(
    phi: Any, alpha: float, prec: int = 128, verbose: bool = False
) -> dict[str, Any]:
    """Choose ρ from α, then compute M_ρ = sup_{|z|=ρ} |φ(z)|.

    Outputs:
        rho   : arb — radius for the Cauchy bound.
        M_rho : arb — sup-norm of φ on |z|=ρ.
    """
    from grothendieck.proof.certified.compute_m_rho import (
        choose_rho, compute_M_rho,
    )
    rho = choose_rho(alpha=alpha, prec=prec, verbose=verbose)
    M_rho = compute_M_rho(rho, phi, prec=prec, verbose=verbose)
    return {"rho": rho, "M_rho": M_rho}


def head_contribution_pipeline(
    p: Any, phi: Any, K_max: int = 50, n_head: int | None = None,
    prec: int = 128, verbose: bool = False,
) -> dict[str, Any]:
    """Sum the first `n_head` odd Taylor coefficients of φ, weighted by p^k.

    Outputs:
        head_contribution : arb
        n                 : int — number of terms used.
    """
    from grothendieck.proof.certified.head_contribution import compute_head_contribution
    n = n_head if n_head is not None else (K_max - 1) // 2
    return compute_head_contribution(p, phi, n=n, prec=prec, verbose=verbose)


def lipschitz_bounds_pipeline(
    p: Any, h_eta_series: Any, K_max: int = 50, prec: int = 128, verbose: bool = False,
) -> dict[str, Any]:
    """Compute the Lipschitz constant `L` for the Taylor map.

    Outputs:
        L : arb — Lipschitz constant.
    """
    from grothendieck.proof.certified.lipschitz_bounds import compute_L
    return compute_L(p, h_eta_series, K_max=K_max, prec=prec, verbose=verbose)


def tail_bound_pipeline(
    M_rho: Any, alpha: float, n_for_tail: int, prec: int = 128, verbose: bool = False,
) -> dict[str, Any]:
    """Compute the tail-bound ε := M_ρ · (γ₀/ρ)^{n_for_tail} / (1 − γ₀/ρ).

    With ρ = γ₀ · α, we have γ₀/ρ = 1/α (independent of γ₀).

    Outputs:
        epsilon : arb — tail-bound ε.
    """
    from flint import arb
    from grothendieck.proof.certified.tail_bound import compute_epsilon
    gamma_over_rho = arb(1) / arb(alpha)
    epsilon = compute_epsilon(M_rho, gamma_over_rho, n_for_tail, prec, verbose)
    return {"epsilon": epsilon}


def solve_gamma_pipeline(
    p: Any, H_eta_i_over_i: Any, L: Any, head_contribution: Any, epsilon: Any,
    C_r: Any, r: Any, prec: int = 128, verbose: bool = False,
) -> dict[str, Any]:
    """Compute `series_error := head + p · ε` and solve for γ.

    Outputs:
        gamma_best : arb — best γ found such that the summability condition holds.
        plus other diagnostics from the underlying `solve_gamma`.
    """
    from grothendieck.proof.certified.solve_gamma import solve_gamma as _solve_gamma
    from grothendieck.proof.certified.h_eta_evaluator import gamma_0_arb
    series_error = head_contribution + p * epsilon
    gamma_0 = gamma_0_arb(prec)
    result = _solve_gamma(
        gamma_0, p, H_eta_i_over_i, L, series_error, C_r, r,
        prec=prec, verbose=verbose,
    )
    # Also include the derived `series_error` for downstream / certificate.
    result = dict(result)
    result["series_error"] = series_error
    result["gamma_0"] = gamma_0
    return result
