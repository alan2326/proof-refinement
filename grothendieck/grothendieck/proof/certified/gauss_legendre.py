"""
Certified Gauss-Legendre quadrature via flint's arb.legendre_p_root.

Produces rigorously certified GL nodes and weights on [-1, 1] using
flint/arb's built-in Legendre root finder, which returns arb balls
that are guaranteed enclosures at the current flint_ctx.prec.

Precision is controlled by flint_ctx.prec (passed as the `prec` arg):
  prec=128  → radii ~ 10^{-39}
  prec=256  → radii ~ 10^{-78}
  prec=512  → radii ~ 10^{-155}
  prec=1024 → radii ~ 10^{-309}
"""

from __future__ import annotations

from flint import arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import (
    certified_lt,
    certified_gt,
    certified_positive,
)


# ---------------------------------------------------------------------------
# Legendre polynomial evaluation via 3-term recurrence
# ---------------------------------------------------------------------------

def legendre_Pn_Pn1(n: int, x: arb) -> tuple[arb, arb]:
    """Evaluate (P_n(x), P_{n-1}(x)) via the 3-term recurrence.

    Recurrence: (k+1) P_{k+1} = (2k+1) x P_k - k P_{k-1}

    Does NOT use arb.legendre_p() which segfaults in flint 0.8.0.
    """
    if n == 0:
        return (arb(1), arb(0))
    if n == 1:
        return (x, arb(1))

    Pkm1 = arb(1)  # P_0
    Pk = x          # P_1
    for k in range(1, n):
        Pkp1 = ((2 * k + 1) * x * Pk - k * Pkm1) / (k + 1)
        Pkm1, Pk = Pk, Pkp1
    return (Pk, Pkm1)


# ---------------------------------------------------------------------------
# Main certification API
# ---------------------------------------------------------------------------

_certified_cache: dict[tuple[int, int], tuple[list[arb], list[arb]]] = {}


def certify_gl_nodes_weights(
    n: int,
    prec: int = 256,
    verbose: bool = False,
) -> tuple[list[arb], list[arb]]:
    """Certify n-point Gauss-Legendre nodes and weights on [-1, 1].

    Uses flint's arb.legendre_p_root(n, k, weight=True) which returns
    rigorous arb ball enclosures at the requested precision.

    Sanity checks after computation:
      - All nodes in (-1, 1)
      - Consecutive nodes disjoint and strictly increasing
      - P_n(X) contains 0 for each node ball (via 3-term recurrence)
      - All weights positive

    Args:
        n: Number of quadrature points.
        prec: Arb precision in bits. Controls enclosure tightness:
              128 → ~39 digits, 256 → ~78 digits, 512 → ~155 digits.
        verbose: Print progress information.

    Returns:
        (nodes, weights) — lists of certified arb balls, nodes in
        increasing order.

    Raises:
        RuntimeError: If any sanity check fails.
    """
    key = (n, prec)
    if key in _certified_cache:
        return _certified_cache[key]

    old_prec = flint_ctx.prec
    flint_ctx.prec = prec

    # arb.legendre_p_root returns roots in decreasing order (k=0 is largest)
    # We collect in reverse to get increasing order.
    nodes = []
    weights = []
    for k in range(n - 1, -1, -1):
        x, w = arb.legendre_p_root(n, k, weight=True)
        nodes.append(x)
        weights.append(w)
        if verbose:
            print(f"  Node k={k}: x={x}  rad={float(x.rad()):.2e}")

    # -------------------------------------------------------------------
    # Sanity checks
    # -------------------------------------------------------------------

    # All nodes in (-1, 1)
    one = arb(1)
    for i, x in enumerate(nodes):
        if not certified_gt(x, -one):
            flint_ctx.prec = old_prec
            raise RuntimeError(f"Node {i} not certifiably > -1")
        if not certified_lt(x, one):
            flint_ctx.prec = old_prec
            raise RuntimeError(f"Node {i} not certifiably < 1")

    # Consecutive nodes disjoint and strictly increasing
    for i in range(len(nodes) - 1):
        if nodes[i].overlaps(nodes[i + 1]):
            flint_ctx.prec = old_prec
            raise RuntimeError(
                f"Nodes {i} and {i+1} overlap — not disjoint"
            )
        if not certified_lt(nodes[i], nodes[i + 1]):
            flint_ctx.prec = old_prec
            raise RuntimeError(
                f"Node {i} not certifiably < node {i+1}"
            )

    # P_n(X) contains 0 for each certified ball
    for i, x in enumerate(nodes):
        Pn, _ = legendre_Pn_Pn1(n, x)
        if not Pn.contains(arb(0)):
            flint_ctx.prec = old_prec
            raise RuntimeError(
                f"P_{n}(node_{i}) does not contain 0: {Pn}"
            )

    # All weights positive
    for i, w in enumerate(weights):
        if not certified_positive(w):
            flint_ctx.prec = old_prec
            raise RuntimeError(f"Weight {i} not certifiably positive: {w}")

    flint_ctx.prec = old_prec

    _certified_cache[key] = (nodes, weights)
    return nodes, weights


# ---------------------------------------------------------------------------
# Scaling utility
# ---------------------------------------------------------------------------

def certified_scale_gl_to_interval(
    nodes: list[arb], weights: list[arb], a: arb, b: arb,
) -> tuple[list[arb], list[arb]]:
    """Scale GL nodes/weights from [-1,1] to [a,b]."""
    half = (b - a) / arb(2)
    mid = (a + b) / arb(2)
    scaled_nodes = [mid + half * x for x in nodes]
    scaled_weights = [half * w for w in weights]
    return scaled_nodes, scaled_weights
