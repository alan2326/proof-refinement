"""Loader for the high-precision b-series caches in this directory.

Cache schema (version 1, explicit_mid_rad_decimal_strings):
    {
      "version": 1,
      "eta": "0.01",
      "K_max": 300,
      "prec": 400,
      "L": 25, "n_gl": 64, "n_panels": 40,
      "b": {"1": {"mid": "0.6362...", "rad": "1.234e-120"}, ...}
    }

Even-index entries are absent (H_η is odd; b_{2k} = 0 exactly).

Use this loader instead of `h_eta_evaluator.load_b_series_from_json`,
which is for the older `dps`-inflated cache and silently inflates
the radii by 10^{-error_dps}, masking the true geometric decay.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

from flint import arb, ctx as flint_ctx


# ----------------------------------------------------------------------
def load_b_cache(
    path: str | Path,
    K_max: Optional[int] = None,
    prec: Optional[int] = None,
    verbose: bool = False,
) -> tuple[dict[int, arb], dict]:
    """Load b_j arb balls from a high-prec cache.

    Args:
        path: Path to JSON file.
        K_max: Truncate to first K_max indices (default: file's K_max).
        prec: Override flint precision while parsing (default: file's prec).
        verbose: Print summary diagnostics.

    Returns:
        (b_dict, meta) where b_dict[j] is an arb ball with the cached
        midpoint and radius, and meta is the JSON header.
    """
    path = Path(path)
    with path.open() as f:
        data = json.load(f)

    if data.get("version") != 1:
        raise ValueError(f"Unsupported cache version: {data.get('version')}")
    if data.get("schema") != "explicit_mid_rad_decimal_strings":
        raise ValueError(f"Unsupported schema: {data.get('schema')}")

    file_K = data["K_max"]
    file_prec = data["prec"]

    if prec is None:
        prec = file_prec
    if K_max is None:
        K_max = file_K
    K_max = min(K_max, file_K)

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec
    try:
        b_dict: dict[int, arb] = {0: arb(0)}
        for j_str, entry in data["b"].items():
            j = int(j_str)
            if j > K_max:
                continue
            mid = arb(entry["mid"])
            rad = arb(entry["rad"])
            # Reconstruct ball: union of [mid-rad, mid+rad] (matches the
            # pattern used in h_eta_evaluator.load_b_series_from_json).
            b_dict[j] = arb.union(mid - rad, mid + rad)

        # Fill in even indices (= 0 exactly) up to K_max for callers
        # that iterate by index.
        for j in range(K_max + 1):
            if j not in b_dict:
                b_dict[j] = arb(0)
    finally:
        flint_ctx.prec = old_prec

    meta = {k: v for k, v in data.items() if k != "b"}

    if verbose:
        print(f"[b-cache] loaded {path.name}")
        print(f"  K_max in file: {file_K}, requested: {K_max}")
        print(f"  prec in file:  {file_prec}, using: {prec}")
        print(f"  non-zero entries: {sum(1 for j in b_dict if j > 0 and not b_dict[j].is_zero())}")
        for j in [1, 3, 11, 51, 101, 151, 201, K_max - 1 if K_max > 1 else 1]:
            if j in b_dict and not b_dict[j].is_zero():
                bj = b_dict[j]
                print(f"  b_{j:<3} mid={bj.mid().str(8):<22}  rad={bj.rad().str(8):<14}")

    return b_dict, meta


# ----------------------------------------------------------------------
def latest_cache(eta_str: str = "0.01",
                 cache_dir: Optional[Path] = None) -> Path:
    """Return the cache file with the largest K_max·prec for the given eta."""
    if cache_dir is None:
        cache_dir = Path(__file__).resolve().parent
    candidates = list(cache_dir.glob(
        f"b_series_eta{eta_str.replace('.', 'p')}_K*_prec*.json"))
    if not candidates:
        raise FileNotFoundError(
            f"No b-series cache found in {cache_dir} for eta={eta_str}")

    def _score(p: Path) -> int:
        # parse "...K{K}_prec{prec}.json"
        stem = p.stem
        try:
            k_part = stem.split("_K", 1)[1]
            k_str, rest = k_part.split("_prec", 1)
            p_str = rest
            return int(k_str) * int(p_str)
        except Exception:
            return 0

    return max(candidates, key=_score)
