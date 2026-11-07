"""Node: a single step in the proof graph.

A node is either:
  - `statement`: a Lean theorem (with optional effective companion + Python oracle),
  - `computational`: a pure Python certified-arithmetic step, or
  - `constant`: a fixed rational from `_index.toml`.

Each node loads from a TOML file in `ProofGraph/nodes/`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any

# Python 3.11+ tomllib is in stdlib; fall back to tomli for earlier.
try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # pragma: no cover
    import tomli as tomllib  # type: ignore[no-redef]


class NodeKind(str, Enum):
    STATEMENT = "statement"
    COMPUTATIONAL = "computational"
    CONSTANT = "constant"


@dataclass
class LeanHandle:
    """The Lean side of a statement node."""

    sink: str | None = None              # fully qualified theorem name (e.g., "Braverman.theorem_5_1")
    file: str | None = None              # path relative to project root
    effective: str | None = None         # name of the effective companion theorem
    effective_file: str | None = None    # path to the effective companion file


@dataclass
class PythonHandle:
    """The Python side of a computational (or computational-backed statement) node."""

    module: str | None = None            # e.g., "grothendieck.proof.certified.compute_cr"
    function: str | None = None          # e.g., "compute_Cr_full"
    inputs: list[str] = field(default_factory=list)   # parent slugs / output keys
    outputs: list[str] = field(default_factory=list)  # output keys this node emits


@dataclass
class Node:
    """A single node in the proof graph."""

    name: str
    slug: str
    kind: NodeKind
    paper_ref: str | None
    parents: list[str]

    lean: LeanHandle = field(default_factory=LeanHandle)
    python: PythonHandle = field(default_factory=PythonHandle)

    # Allowed axioms for the Lean theorem. Either a list of strings, or a
    # @inherit:<name> reference resolved against `_index.toml`.
    allowed_axioms_spec: str | list[str] | None = None

    # Result of an audit run (Phase 1+). Maps "actual_axioms" → list of axioms
    # found by `#print axioms`. Populated by audit.py.
    actual_axioms: list[str] | None = None

    # Free-form raw TOML (for forward-compat).
    raw: dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_toml(cls, path: Path) -> "Node":
        with path.open("rb") as f:
            data = tomllib.load(f)
        return cls.from_dict(data)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Node":
        kind = NodeKind(data["kind"])
        lean_data = data.get("lean", {}) or {}
        python_data = data.get("python", {}) or {}
        audit_data = data.get("audit", {}) or {}
        return cls(
            name=data["name"],
            slug=data["slug"],
            kind=kind,
            paper_ref=data.get("paper_ref"),
            parents=list(data.get("parents", [])),
            lean=LeanHandle(
                sink=lean_data.get("sink"),
                file=lean_data.get("file"),
                effective=lean_data.get("effective"),
                effective_file=lean_data.get("effective_file"),
            ),
            python=PythonHandle(
                module=python_data.get("module"),
                function=python_data.get("function"),
                inputs=list(python_data.get("inputs", [])),
                outputs=list(python_data.get("outputs", [])),
            ),
            allowed_axioms_spec=audit_data.get("allowed_axioms"),
            actual_axioms=audit_data.get("actual_axioms"),
            raw=data,
        )

    @property
    def has_lean(self) -> bool:
        return self.lean.sink is not None

    @property
    def has_python(self) -> bool:
        return self.python.module is not None and self.python.function is not None

    def __repr__(self) -> str:
        bits = [self.kind.value]
        if self.has_lean:
            bits.append(f"lean={self.lean.sink}")
        if self.has_python:
            bits.append(f"py={self.python.module}.{self.python.function}")
        return f"Node({self.slug}, {', '.join(bits)})"
