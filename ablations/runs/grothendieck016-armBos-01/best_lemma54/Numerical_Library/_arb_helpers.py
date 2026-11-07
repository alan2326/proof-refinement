"""Shared helpers for the M/R bound oracles.

Two pieces of glue between the certified-arb pipeline and the Lean evaluator:

  * `arb_to_rational_ub(x)` — convert an `arb` (interval) to a `Fraction`
    guaranteed to be ≥ the true value. Adds a small relative+absolute safety
    margin and rounds up to a chosen denominator.

  * `cached_run(key, fn)` — JSON-cache an expensive arb pipeline call so the
    evaluator's per-candidate oracle reverification is cheap.

Both are intentionally conservative: `arb_to_rational_ub` may overestimate by
~0.1% but never underestimate. `cached_run` keys on `key` (any
JSON-serializable dict); first call runs `fn()`, subsequent calls re-load from
disk.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable

from flint import arb

CACHE_DIR = Path(__file__).resolve().parent / ".cache"


def arb_to_rational_ub(
    x: arb,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
    max_denom: int = 10000,
) -> Fraction:
    """Return a Fraction ≥ x (guaranteed sound).

    Strategy: inflate by max(safety_rel * |x|, safety_abs), then ceil to
    a Fraction with denominator at most `max_denom`. The inflation is small
    but defensive — `arb` itself already tracks an interval, but we want a
    guaranteed-upper rational unaffected by float-ish details when ferrying
    through Python.

    The returned Fraction is at most `x * (1 + safety_rel) + safety_abs +
    1/max_denom` above the true value.
    """
    # arb's `.upper()` returns the upper endpoint of the ball as an arb.
    # `float()` converts via the midpoint, with rounding-toward-nearest. To
    # be sound we inflate before float conversion.
    inflated = x * (arb(1) + arb(str(safety_rel))) + arb(str(safety_abs))
    hi_arb = inflated.upper()
    hi_f = float(hi_arb)
    # Re-inflate for any float rounding loss in the conversion above.
    hi_f = hi_f * (1.0 + 1e-12) + 1e-15
    # Ceil to a multiple of 1/max_denom.
    n = math.ceil(hi_f * max_denom)
    f = Fraction(n, max_denom)
    return f


def _cache_path(key_dict: dict[str, Any]) -> Path:
    """Stable filename derived from key_dict (sorted JSON)."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    name = json.dumps(key_dict, sort_keys=True, separators=(",", ":"))
    # Hash to keep filenames short and filesystem-safe.
    import hashlib
    h = hashlib.sha1(name.encode()).hexdigest()[:16]
    return CACHE_DIR / f"{h}.json"


def cached_run(
    key: dict[str, Any],
    fn: Callable[[], dict[str, Any]],
) -> dict[str, Any]:
    """Run fn() once and cache its output keyed on `key`.

    `fn` must return a JSON-serializable dict. To force recomputation, delete
    the cache file (location printed on first run, in `.cache/`).
    """
    p = _cache_path(key)
    if p.exists():
        with p.open() as f:
            return json.load(f)
    result = fn()
    with p.open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    return result
