#!/usr/bin/env python3
"""
1D Gauss-Hermite quadrature with arbitrary precision.

Provides nodes and weights for integrating against e^{-x²} or Gaussian measure.
Supports loading precomputed nodes/weights from cache files.

The default cache contains 250 nodes at 200 dps. For n ≤ 250 and dps ≤ 200,
nodes are derived from this master cache. Fresh computation only happens
for n > 250 or dps > 200.
"""

from __future__ import annotations
import pickle
from pathlib import Path
from mpmath import mp


# Directory containing precomputed quadrature data
_DATA_DIR = Path(__file__).parent / "data"

# Master cache parameters
_MASTER_N = 250
_MASTER_DPS = 200
_MASTER_CACHE_PATH = _DATA_DIR / f"gh_quad_{_MASTER_N}_nodes_{_MASTER_DPS}_dps.pkl"

# In-memory cache for the master nodes/weights (loaded once)
_master_cache: tuple[list[str], list[str]] | None = None


def _load_master_cache() -> tuple[list[str], list[str]] | None:
    """Load the master cache file (250 nodes, 200 dps) into memory."""
    global _master_cache

    if _master_cache is not None:
        return _master_cache

    if not _MASTER_CACHE_PATH.exists():
        return None

    try:
        with open(_MASTER_CACHE_PATH, 'rb') as f:
            data = pickle.load(f)

        # Store as strings for precision preservation.
        # CRITICAL: The pickle stores mpf objects, and str(mpf) uses the
        # current mp.dps for formatting. We must set mp.dps = _MASTER_DPS
        # before converting, otherwise nodes are truncated to whatever
        # mp.dps happens to be at first call (often 15 = default).
        old_dps = mp.dps
        mp.dps = _MASTER_DPS
        nodes = [mp.nstr(x, _MASTER_DPS, strip_zeros=False) for x in data['nodes']]
        weights = [mp.nstr(w, _MASTER_DPS, strip_zeros=False) for w in data['weights']]
        mp.dps = old_dps

        _master_cache = (nodes, weights)
        return _master_cache
    except Exception:
        return None


def _get_cache_path(n: int, dps: int) -> Path:
    """Get the path to a cache file for given n and dps."""
    return _DATA_DIR / f"gh_quad_{n}_nodes_{dps}_dps.pkl"


def _load_from_master(dps: int) -> tuple[list, list] | None:
    """
    Load all 250 nodes/weights from master cache at requested precision.

    Returns (nodes, weights) if master cache exists, None otherwise.
    """
    if dps > _MASTER_DPS:
        return None

    master = _load_master_cache()
    if master is None:
        return None

    master_nodes, master_weights = master

    # Convert to mpmath at requested precision
    mp.dps = dps
    nodes = [mp.mpf(x) for x in master_nodes]
    weights = [mp.mpf(w) for w in master_weights]

    return nodes, weights


def _save_to_cache(n: int, dps: int, nodes: list, weights: list) -> None:
    """Save computed nodes/weights to cache file."""
    _DATA_DIR.mkdir(parents=True, exist_ok=True)
    cache_path = _get_cache_path(n, dps)

    # Convert to strings for portable storage
    data = {
        'nodes': [str(x) for x in nodes],
        'weights': [str(w) for w in weights],
    }

    with open(cache_path, 'wb') as f:
        pickle.dump(data, f)


def gh_nodes_weights_1d(n: int = _MASTER_N, dps: int = 80, use_cache: bool = True) -> tuple[list, list]:
    """
    Get Gauss-Hermite nodes and weights for ∫ g(x) e^{-x²} dx.

    By default, uses all 250 precomputed nodes from the master cache.
    The `n` parameter is ignored when loading from cache (always uses 250).

    Returns nodes x_k and weights w_k such that:
        ∫_{-∞}^{∞} g(x) e^{-x²} dx ≈ Σ_k w_k g(x_k)

    Note: To integrate against the standard Gaussian φ(x) = (1/√(2π))e^{-x²/2},
    use the substitution u = √2·x:
        ∫ g(u) φ(u) du = (1/√π) ∫ g(√2·x) e^{-x²} dx
                       ≈ (1/√π) Σ_k w_k g(√2·x_k)

    Args:
        n: Number of quadrature points (ignored when using cache, defaults to 250)
        dps: Decimal precision for mpmath
        use_cache: If True, load from master cache (recommended)

    Returns:
        (nodes, weights): Lists of length 250 (or n if computed fresh)
    """
    mp.dps = dps

    # Try loading from master cache first (always uses 250 nodes)
    if use_cache:
        cached = _load_from_master(dps)
        if cached is not None:
            return cached

    # Fall back to computing (only needed for dps > 200)
    # Build Jacobi matrix: J[i,i] = 0, J[i,i+1] = J[i+1,i] = √((i+1)/2)
    J = mp.zeros(n, n)
    for k in range(n - 1):
        off_diag = mp.sqrt((k + 1) / mp.mpf('2'))
        J[k, k + 1] = off_diag
        J[k + 1, k] = off_diag

    # Eigenvalue decomposition
    evals, evecs = mp.eig(J)

    # Extract real parts and sort
    nodes = [mp.re(ev) for ev in evals]
    indices = sorted(range(n), key=lambda i: nodes[i])
    nodes = [nodes[i] for i in indices]

    # Compute weights: w_k = μ_0 · (v_{0,k})²
    # where μ_0 = ∫ e^{-x²} dx = √π and v_{0,k} is the first component of eigenvector k
    mu0 = mp.sqrt(mp.pi)
    weights = []
    for idx in indices:
        v0 = evecs[0, idx]
        # Weight = μ_0 · |v0|²
        weight = mu0 * (mp.re(v0)**2 + mp.im(v0)**2)
        weights.append(weight)

    # Save to cache for future use (only if dps exceeds master cache)
    if use_cache and dps > _MASTER_DPS:
        _save_to_cache(n, dps, nodes, weights)

    return nodes, weights


class GaussHermite1D:
    """
    1D Gauss-Hermite quadrature with caching and convenient interfaces.

    Uses all 250 precomputed nodes by default for maximum accuracy.

    Example:
        gh = GaussHermite1D(dps=80)
        result = gh.integrate_exp_weight(lambda x: x**2)  # Integrates x² e^{-x²}
        result = gh.integrate_gaussian(lambda u: u**2)    # Integrates x² φ(x)
    """

    def __init__(self, dps: int = 80, use_cache: bool = True):
        """
        Initialize quadrature with given precision.

        Always uses 250 nodes from the master cache for maximum accuracy.

        Args:
            dps: Decimal precision
            use_cache: If True, load from master cache (recommended)
        """
        self.dps = dps
        mp.dps = dps

        # Load nodes/weights (always 250 from cache)
        self.nodes, self.weights = gh_nodes_weights_1d(dps=dps, use_cache=use_cache)
        self.n_points = len(self.nodes)

        # Also cache nodes transformed for Gaussian measure: u_k = √2 · x_k
        self.sqrt2 = mp.sqrt(2)
        self.gaussian_nodes = [self.sqrt2 * x for x in self.nodes]

        # Normalization factor for Gaussian integration: 1/√π
        self.gaussian_factor = mp.mpf('1') / mp.sqrt(mp.pi)

    def integrate_exp_weight(self, func) -> mp.mpf:
        """
        Integrate func(x) against weight e^{-x²}:
            ∫_{-∞}^{∞} func(x) e^{-x²} dx ≈ Σ_k w_k func(x_k)

        Args:
            func: Callable taking a single argument

        Returns:
            Approximation to the integral
        """
        result = mp.mpf('0')
        for k in range(self.n_points):
            result += self.weights[k] * func(self.nodes[k])
        return result

    def integrate_gaussian(self, func) -> mp.mpf:
        """
        Integrate func(u) against standard Gaussian measure φ(u):
            ∫_{-∞}^{∞} func(u) φ(u) du

        where φ(u) = (1/√(2π)) e^{-u²/2}

        Uses the substitution u = √2·x to reduce to exp weight:
            ∫ func(u) φ(u) du = (1/√π) ∫ func(√2·x) e^{-x²} dx

        Args:
            func: Callable taking a single argument

        Returns:
            Approximation to the integral
        """
        result = mp.mpf('0')
        for k in range(self.n_points):
            u_k = self.gaussian_nodes[k]
            result += self.weights[k] * func(u_k)
        return self.gaussian_factor * result

    def get_nodes(self, for_gaussian: bool = False) -> list:
        """
        Get quadrature nodes.

        Args:
            for_gaussian: If True, return nodes scaled for Gaussian (u = √2·x)

        Returns:
            List of nodes
        """
        return self.gaussian_nodes if for_gaussian else self.nodes

    def get_weights(self) -> list:
        """Get quadrature weights (same for both weightings)."""
        return self.weights
