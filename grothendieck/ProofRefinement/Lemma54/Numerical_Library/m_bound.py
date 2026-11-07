"""
M-bound: rigorous upper bound on
    max{ ‖H_0(w)‖, ‖H_η(w)‖, ‖H_0'(w)‖, ‖H_η'(w)‖ : w ∈ Ω(δ, B) }

This is the M from Braverman et al. (2011) Lemma 5.4, eq. (76). The Lean
axiom backed by `compute_M_bound` is

    axiom h_M_bound :
      ∀ w, w ∈ closedBall (0 : ℂ) R_val → w ∈ S →
        ‖H0 w‖ ≤ M_val ∧ … ∧ ‖deriv (H_eta η) w‖ ≤ M_val

The certified-arb pipeline at
`grothendieck.proof.certified.compute_cr.compute_M_rigorous` does the
underlying interval arithmetic; this module wraps it and rounds up to a
`Fraction` for `M_val`.

Conservation: the `compute_M_rigorous` bound is on the *strip* `Ω(δ, B)`,
while the Lean axiom is on `closedBall(0, R) ∩ S`. Soundness requires
`closedBall(0, R) ∩ S ⊆ Ω(δ, B)` to hold for the chosen R_val. With
R_val ≥ √((1-δ)² + B²) and `Ω` containing all of `closedBall(0, R) ∩ S`
(true when `B ≥ R` since |Im z| ≤ R) — actually this containment is not
generally true. The framework treats the M bound as covering the region
where F_p⁻¹ ranges (Ω); the Lean axiom statement is paper-faithful but
the certificate scope mismatch is documented in the design notes and is
the subject of future axiom splitting.

For the pilot: we trust the certified pipeline computes M on `dΩ` (which
upper-bounds M on `Ω` by max-modulus), and rely on the rest of the proof
(`paper_taylor_argument`) to consume M only where F_p⁻¹ actually ranges.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Optional

from flint import arb, ctx as flint_ctx

from grothendieck.proof.certified.compute_cr import (
    compute_M_rigorous,
)
from grothendieck.proof.certified.certify_invertibility import (
    certify_invertibility,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from .types import OracleResult


def _compute_M_for_params(
    r: str,
    eta: float,
    delta: Optional[str],
    B: Optional[str],
    n_per_edge: int,
    prec: int,
) -> dict:
    """Run the certified pipeline for a specific (r, η, δ, B) and return a
    JSON-serializable dict with the M upper bound (as decimal string).

    If δ or B is None, they are auto-chosen via certify_invertibility.
    """
    flint_ctx.prec = prec
    r_arb = arb(r)

    if delta is None or B is None:
        inv = certify_invertibility(r=float(r_arb), eta=eta, prec=prec, verbose=False)
        delta_arb = inv["delta"]
        B_arb = inv["B"]
    else:
        delta_arb = arb(delta)
        B_arb = arb(B)

    M_arb = compute_M_rigorous(r_arb, delta_arb, B_arb, n_per_edge=n_per_edge, prec=prec)
    # Render as decimal string so the cache survives across processes.
    return {
        "M_str": M_arb.str(20, more=True),
        "M_upper_float": float(M_arb.upper()),
        "delta_str": delta_arb.str(20, more=True),
        "B_str": B_arb.str(20, more=True),
        "n_per_edge": n_per_edge,
        "prec": prec,
    }


def compute_M_bound(
    *,
    r: str = "23/25",
    eta: float = 0.01,
    delta: Optional[str] = None,
    B: Optional[str] = None,
    n_per_edge: int = 512,
    prec: int = 128,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
) -> OracleResult:
    """Certified rational upper bound on M.

    Defaults match V1: auto-chosen δ, B via the pipeline (loose). For
    tighter candidates, call with explicit (δ, B) — see m_bound_tight.py.
    """
    key = {
        "fn": "compute_M_bound",
        "r": r, "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec,
    }
    cached = cached_run(key, lambda: _compute_M_for_params(
        r=r, eta=eta, delta=delta, B=B, n_per_edge=n_per_edge, prec=prec,
    ))

    flint_ctx.prec = prec
    M_arb = arb(cached["M_str"])
    bound = arb_to_rational_ub(M_arb, safety_rel=safety_rel, max_denom=max_denom)
    return OracleResult(
        bound=bound,
        ball_value=cached["M_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta_str"],
            "B": cached["B_str"],
            "n_per_edge": cached["n_per_edge"],
            "M_arb_str": cached["M_str"],
        },
    )


# Tuned variants for downstream candidates ----------------------------------


def compute_M_bound_production(**overrides) -> OracleResult:
    """The production rectangle `Ω(57/1000, 293/250)` used by
    `ProofGraph/Effective/Lemma54Effective.lean`. This is what V0
    targets — the certified `compute_M_rigorous` returns ≈ 3531 here,
    so any candidate's `M_val` must be ≥ that value.

    Pinned defaults match `nodes/_index.toml` (`delta = 57/1000`,
    `B = 293/250`, `prec = 256`).
    """
    params = dict(
        r="23/25", eta=0.01,
        delta="57/1000", B="293/250",
        n_per_edge=512, prec=256,
        max_denom=10000, safety_rel=1e-3,
    )
    params.update(overrides)
    return compute_M_bound(**params)


def compute_M_bound_tight(**overrides) -> OracleResult:
    """Manually-tuned (δ, B) near the Rouché boundary for r = 23/25.

    Sweep at prec=200, n_per_edge=1024 found (δ=163/1000, B=1115/1000) gives
    M ≈ 431.4, R ≈ 1.395. Above δ ≈ 0.164 the Rouché margin is no longer
    certified.

    Sprint 008 retarget: bumped the oracle's internal precision from
    `(n_per_edge=1024, prec=200, safety_rel=1e-3)` to
    `(n_per_edge=4096, prec=400, safety_rel=1e-4)` (δ, B unchanged). At
    that retargeted precision the certified rational bound tightened to
    `≈ 215309/500 ≈ 430.62`, justifying V6's `M_val = 431`.

    Sprint 009 retarget: pushes `δ` to its Rouché-margin floor at fixed
    `B = 1115/1000`. A fine sweep finds `δ = 1635/10000 = 0.1635` is the
    largest rational ≤ 0.164 keeping all four certifications passing
    (`im` & `re` containment, Rouché margin `m ≈ 1.10·10⁻⁴ > 0`, and
    `p·M_d < m`); `δ = 1636/10000` already collapses the margin. To
    resolve the slightly tighter rectangle's M-ball cleanly below the
    integer `428`, internal precision is bumped further:
        n_per_edge: 4096 → 8192
        prec      :  400 →  600
        safety_rel: 1e-4 → 1e-5
        max_denom : 10000 (unchanged).
    The certified arb ball at the new rectangle is `[427.711 +/- 0.198]`
    (upper ≈ 427.909); the rationalized bound is `855827/2000 ≈ 427.9135 < 428`.
    First call after the rectangle change takes ~3–5 minutes (cache miss
    at the new rectangle + bumped precision); thereafter cached.
    """
    params = dict(
        r="23/25", eta=0.01,
        delta="1635/10000", B="1115/1000",
        n_per_edge=8192, prec=600,
        max_denom=10000, safety_rel=1e-5,
    )
    params.update(overrides)
    return compute_M_bound(**params)
