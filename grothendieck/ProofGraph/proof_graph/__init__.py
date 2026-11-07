"""ProofGraph framework: end-to-end effective proof of `KG < KrivineBound`.

Walks a graph of mathematical steps, each backed by a Lean theorem and/or a
Python certified-arithmetic computation, producing a verifiable certificate at
the sink.

Design: docs/PROOF_GRAPH_DESIGN.md.
"""

from .node import Node, NodeKind
from .graph import Graph, load_graph

__all__ = ["Node", "NodeKind", "Graph", "load_graph"]
