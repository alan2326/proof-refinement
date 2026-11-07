"""Shared loader for the H_eta phi-series used by m_phi/m_phi_prime/m_pp oracles.

The H_eta family at η = 0.01 has its certified b-series cached at
`outputs/b_series_eta0p01_K250_dps100.json`. The phi-series (used for
pointwise evaluation via `eval_H_eta_at_acb`) is derived from the b-series
once and reused across oracle calls.

This loader keeps an in-process cache keyed on `(eta, prec, K_max)` so
repeat calls within one Evaluator run are free.
"""

from __future__ import annotations

from pathlib import Path
from typing import Tuple

from flint import arb_series, ctx as flint_ctx

from grothendieck.proof.certified.h_eta_evaluator import (
    load_b_series_from_json,
)
from grothendieck.proof.certified.phi_taylor import (
    compute_phi_coefficients,
)


# Anchor relative to repository root: <repo>/outputs/b_series_eta0p01_K250_dps100.json.
# This file lives at <repo>/ProofRefinement/Lemma54/Numerical_Library/_phi_loader.py
# so parents[0..3] are: Numerical_Library, Lemma54, ProofRefinement, <repo>.
_REPO_ROOT = Path(__file__).resolve().parents[3]
_DEFAULT_B_SERIES_PATH = _REPO_ROOT / "outputs" / "b_series_eta0p01_K250_dps100.json"

_phi_cache: dict[Tuple[float, int, int], arb_series] = {}


def get_phi_series(
    eta: float = 0.01,
    prec: int = 256,
    K_max: int = 100,
    b_series_path: str | None = None,
) -> arb_series:
    """Return the phi-series for the H_eta family at the given (eta, K_max, prec).

    Loads the cached b-series from disk on first call; subsequent calls within
    the same Python process hit the in-memory cache.

    `eta` is currently locked to 0.01 (the production setting); other values
    raise NotImplementedError because we don't have cached b-series for them.
    """
    if eta != 0.01:
        raise NotImplementedError(
            f"phi-series loader currently only supports eta = 0.01 "
            f"(production); requested eta = {eta}"
        )

    key = (eta, prec, K_max)
    if key in _phi_cache:
        return _phi_cache[key]

    path = b_series_path or str(_DEFAULT_B_SERIES_PATH)
    if not Path(path).exists():
        raise FileNotFoundError(
            f"Expected cached b-series at {path}; "
            f"run the certified pipeline once to populate it."
        )

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        h_eta_series = load_b_series_from_json(path, K_max=K_max, prec=prec)
        phi_series = compute_phi_coefficients(h_eta_series, K_max, prec)
    finally:
        flint_ctx.prec = old_prec

    _phi_cache[key] = phi_series
    return phi_series
