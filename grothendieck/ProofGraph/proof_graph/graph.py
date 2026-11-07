"""Graph: the collection of nodes plus topological order, edge consistency,
and lookup. Loads `_index.toml` plus all `<slug>.toml` files in `nodes/`.
"""

from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterator

try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # pragma: no cover
    import tomli as tomllib  # type: ignore[no-redef]

from .node import Node


@dataclass
class GraphConfig:
    """Loaded from `_index.toml`."""

    sink_node: str
    lean_primitives: list[str]
    trusted_analytic: list[str]
    axiom_inherit: dict[str, list[str]]
    constants: dict[str, str | int]

    @classmethod
    def from_toml(cls, path: Path) -> "GraphConfig":
        with path.open("rb") as f:
            data = tomllib.load(f)
        axioms = data.get("axioms", {}) or {}
        return cls(
            sink_node=data["sink_node"],
            lean_primitives=list(axioms.get("lean_primitives", [])),
            trusted_analytic=list(axioms.get("trusted_analytic", [])),
            axiom_inherit={
                k: list(v) for k, v in (data.get("axiom_inherit", {}) or {}).items()
            },
            constants=dict(data.get("constants", {}) or {}),
        )


class Graph:
    """The proof graph. Nodes keyed by slug; edges via `parents`."""

    def __init__(self, config: GraphConfig, nodes: dict[str, Node]):
        self.config = config
        self.nodes = nodes
        self._validate()

    def _validate(self) -> None:
        # Every parent must exist as a node.
        for node in self.nodes.values():
            for parent in node.parents:
                if parent not in self.nodes:
                    raise ValueError(
                        f"Node {node.slug!r} declares unknown parent {parent!r}"
                    )
        # The sink must exist.
        if self.config.sink_node not in self.nodes:
            raise ValueError(
                f"Sink {self.config.sink_node!r} not found among nodes"
            )

    # --- Iteration / lookup ---

    def __iter__(self) -> Iterator[Node]:
        return iter(self.nodes.values())

    def __getitem__(self, slug: str) -> Node:
        return self.nodes[slug]

    def __contains__(self, slug: str) -> bool:
        return slug in self.nodes

    def __len__(self) -> int:
        return len(self.nodes)

    @property
    def sink(self) -> Node:
        return self.nodes[self.config.sink_node]

    # --- Graph algorithms ---

    def children(self, slug: str) -> list[str]:
        """All nodes that list `slug` as a parent."""
        return [n.slug for n in self.nodes.values() if slug in n.parents]

    def topological_order(self) -> list[Node]:
        """Kahn's algorithm: leaves first, sink last. Stable order (lex) for ties."""
        indegree: dict[str, int] = {slug: len(node.parents) for slug, node in self.nodes.items()}
        children: dict[str, list[str]] = defaultdict(list)
        for slug, node in self.nodes.items():
            for parent in node.parents:
                children[parent].append(slug)

        # Stable: among nodes with indegree 0 we pop in lex order.
        ready = sorted(s for s, d in indegree.items() if d == 0)
        order: list[Node] = []
        ready_dq = deque(ready)
        seen = set(ready)
        while ready_dq:
            s = ready_dq.popleft()
            order.append(self.nodes[s])
            new_ready = []
            for c in children[s]:
                indegree[c] -= 1
                if indegree[c] == 0 and c not in seen:
                    new_ready.append(c)
                    seen.add(c)
            for c in sorted(new_ready):
                ready_dq.append(c)

        if len(order) != len(self.nodes):
            unresolved = [s for s in self.nodes if s not in seen]
            raise ValueError(f"Graph has a cycle; unresolved nodes: {unresolved}")
        return order

    # --- Axiom whitelist resolution ---

    def resolve_allowed_axioms(self, node: Node) -> list[str]:
        """Resolve `audit.allowed_axioms` to a flat list of axiom names.

        Accepts either a literal list or `@inherit:<name>` (or
        `@axioms.<group>`) references against `_index.toml`.
        """
        spec = node.allowed_axioms_spec
        if spec is None:
            spec = self.config.axiom_inherit.get("default", [])
        if isinstance(spec, str):
            spec = [spec]

        flat: list[str] = []
        for entry in spec:
            if entry.startswith("@inherit:"):
                key = entry.removeprefix("@inherit:")
                flat.extend(self.resolve_allowed_axioms_by_inherit_key(key))
            elif entry.startswith("@axioms."):
                group = entry.removeprefix("@axioms.")
                flat.extend(self._axiom_group(group))
            else:
                flat.append(entry)
        # Dedupe, preserving order.
        seen, dedup = set(), []
        for x in flat:
            if x not in seen:
                seen.add(x); dedup.append(x)
        return dedup

    def resolve_allowed_axioms_by_inherit_key(self, key: str) -> list[str]:
        spec = self.config.axiom_inherit.get(key)
        if spec is None:
            raise KeyError(f"Unknown axiom_inherit key: {key!r}")
        flat: list[str] = []
        for entry in spec:
            if entry.startswith("@axioms."):
                flat.extend(self._axiom_group(entry.removeprefix("@axioms.")))
            else:
                flat.append(entry)
        return flat

    def _axiom_group(self, name: str) -> list[str]:
        if name == "lean_primitives":
            return list(self.config.lean_primitives)
        if name == "trusted_analytic":
            return list(self.config.trusted_analytic)
        raise KeyError(f"Unknown axiom group: {name!r}")


def load_graph(nodes_dir: Path | str | None = None) -> Graph:
    """Load the graph from `ProofGraph/nodes/`."""
    if nodes_dir is None:
        # Default: ProofGraph/nodes relative to this file.
        nodes_dir = Path(__file__).resolve().parent.parent / "nodes"
    nodes_dir = Path(nodes_dir)
    if not nodes_dir.is_dir():
        raise FileNotFoundError(f"Nodes directory not found: {nodes_dir}")

    config = GraphConfig.from_toml(nodes_dir / "_index.toml")
    nodes: dict[str, Node] = {}
    for path in sorted(nodes_dir.glob("*.toml")):
        if path.name.startswith("_"):
            continue
        node = Node.from_toml(path)
        if node.slug in nodes:
            raise ValueError(f"Duplicate slug {node.slug!r}")
        nodes[node.slug] = node
    return Graph(config, nodes)
