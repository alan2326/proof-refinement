"""Render the proof graph in human-readable formats.

Two outputs:
* `mermaid_diagram(graph)` — a Mermaid `flowchart` source string. Renders
  natively in GitHub Markdown and most Markdown viewers. Best for
  README embeds.
* `dot_diagram(graph)` — Graphviz DOT source. Pipe into
  `dot -Tsvg > graph.svg` for a vector image.

The diagrams differentiate node kinds:
* `statement` (Lean theorem) — rectangular box, blue.
* `computational` (Python oracle) — rounded rectangle, green.
* `constant` — hexagon, gray.

The audit status (if available) tints the border:
* `ok` — solid border.
* `unexpected_axioms` — dashed yellow.
* `fail` — dashed red.

Edges run *from parents to children*, i.e. leaves at the top, sink at the
bottom (Mermaid `BT` direction makes this read top-to-bottom in proof
order — leaves at bottom, sink at top — which matches how mathematicians
draw proof trees).
"""

from __future__ import annotations

import json
from pathlib import Path

from .graph import Graph
from .node import Node, NodeKind


# ---------- Mermaid ----------


_KIND_SHAPES_MMD = {
    NodeKind.STATEMENT: ("[", "]"),       # rectangle
    NodeKind.COMPUTATIONAL: ("([", "])"),  # rounded
    NodeKind.CONSTANT: ("{{", "}}"),       # hexagon
}

_KIND_CLASS_MMD = {
    NodeKind.STATEMENT: "stmt",
    NodeKind.COMPUTATIONAL: "comp",
    NodeKind.CONSTANT: "const",
}


def _mmd_label(node: Node, audit: dict | None) -> str:
    bits = [f"<b>{node.slug}</b>"]
    if node.kind == NodeKind.STATEMENT:
        if node.lean.sink:
            bits.append(f"<i>{node.lean.sink.split('.')[-1]}</i>")
        if node.lean.effective:
            bits.append(f"+ {node.lean.effective.split('.')[-1]}")
    elif node.kind == NodeKind.COMPUTATIONAL:
        if node.python.module and node.python.function:
            modshort = node.python.module.split(".")[-1]
            bits.append(f"<i>{modshort}.{node.python.function}</i>")
    if audit:
        n_ax = len(audit.get("targets", [{}])[-1].get("actual_axioms", []))
        bits.append(f"({n_ax} ax)")
    # Mermaid quote-escape.
    label = "<br/>".join(bits)
    label = label.replace('"', "&quot;")
    return f'"{label}"'


def mermaid_diagram(graph: Graph, audit_results: dict | None = None) -> str:
    """Build a Mermaid `flowchart BT` source string for the proof graph.

    `audit_results` is the parsed JSON from a recent `--audit-snapshot`,
    indexed by node slug. If supplied, axiom counts are shown on each node.
    """
    audit_by_slug: dict[str, dict] = {}
    if audit_results:
        for r in audit_results.get("results", []):
            audit_by_slug[r["slug"]] = r

    lines: list[str] = []
    lines.append("```mermaid")
    lines.append("flowchart BT")
    lines.append("  classDef stmt  fill:#e6f0ff,stroke:#0a4ec0,stroke-width:2px,color:#0a2c5e;")
    lines.append("  classDef comp  fill:#e8f7e8,stroke:#2a7a2a,stroke-width:2px,color:#1b4720;")
    lines.append("  classDef const fill:#f2f2f2,stroke:#666,stroke-width:1px,color:#333;")
    lines.append("  classDef warn  stroke:#cc9900,stroke-dasharray:4 2;")
    lines.append("  classDef fail  stroke:#cc0000,stroke-dasharray:4 2;")
    lines.append("  classDef sink  stroke-width:3px;")
    lines.append("")

    # Nodes (topological order so the diagram is stable).
    sink_slug = graph.config.sink_node
    for node in graph.topological_order():
        l_open, l_close = _KIND_SHAPES_MMD[node.kind]
        label = _mmd_label(node, audit_by_slug.get(node.slug))
        lines.append(f"  {node.slug}{l_open}{label}{l_close}")

    lines.append("")

    # Edges.
    for node in graph.nodes.values():
        for parent in node.parents:
            lines.append(f"  {parent} --> {node.slug}")

    lines.append("")

    # Styling.
    for node in graph.nodes.values():
        cls = _KIND_CLASS_MMD[node.kind]
        lines.append(f"  class {node.slug} {cls};")
    # Audit status tints.
    for slug, r in audit_by_slug.items():
        status = r.get("status", "ok")
        if status == "unexpected_axioms":
            lines.append(f"  class {slug} warn;")
        elif status == "fail":
            lines.append(f"  class {slug} fail;")
    # Sink emphasis.
    lines.append(f"  class {sink_slug} sink;")

    lines.append("```")
    return "\n".join(lines)


# ---------- Graphviz DOT ----------


_KIND_SHAPE_DOT = {
    NodeKind.STATEMENT: "box",
    NodeKind.COMPUTATIONAL: "box, style=\"rounded,filled\"",
    NodeKind.CONSTANT: "hexagon",
}

_KIND_FILL_DOT = {
    NodeKind.STATEMENT: "#e6f0ff",
    NodeKind.COMPUTATIONAL: "#e8f7e8",
    NodeKind.CONSTANT: "#f2f2f2",
}


def _dot_label(node: Node, audit: dict | None) -> str:
    bits = [node.slug]
    if node.kind == NodeKind.STATEMENT and node.lean.sink:
        bits.append(node.lean.sink.split(".")[-1])
    elif node.kind == NodeKind.COMPUTATIONAL and node.python.function:
        modshort = (node.python.module or "").split(".")[-1]
        bits.append(f"{modshort}.{node.python.function}")
    if audit and audit.get("targets"):
        n_ax = len(audit["targets"][-1].get("actual_axioms", []))
        bits.append(f"({n_ax} axioms)")
    return "\\n".join(bits).replace('"', '\\"')


def dot_diagram(graph: Graph, audit_results: dict | None = None) -> str:
    """Build a Graphviz DOT source string."""
    audit_by_slug: dict[str, dict] = {}
    if audit_results:
        for r in audit_results.get("results", []):
            audit_by_slug[r["slug"]] = r

    lines: list[str] = []
    lines.append("digraph ProofGraph {")
    lines.append('  rankdir=BT;')
    lines.append('  node [fontname="Helvetica"];')
    lines.append('  edge [arrowsize=0.7];')
    lines.append("")

    sink_slug = graph.config.sink_node
    for node in graph.topological_order():
        label = _dot_label(node, audit_by_slug.get(node.slug))
        shape = _KIND_SHAPE_DOT[node.kind]
        fill = _KIND_FILL_DOT[node.kind]
        sink_attr = ", penwidth=3" if node.slug == sink_slug else ""
        # Status tint.
        a = audit_by_slug.get(node.slug)
        border = ""
        if a:
            if a.get("status") == "unexpected_axioms":
                border = ', color="#cc9900", style="dashed,filled"'
            elif a.get("status") == "fail":
                border = ', color="#cc0000", style="dashed,filled"'
        if "filled" in shape:
            shape_attr = f'shape={shape}, fillcolor="{fill}"'
        else:
            shape_attr = f'shape={shape}, style=filled, fillcolor="{fill}"'
        lines.append(f'  {node.slug} [label="{label}", {shape_attr}{border}{sink_attr}];')

    lines.append("")

    for node in graph.nodes.values():
        for parent in node.parents:
            lines.append(f"  {parent} -> {node.slug};")

    lines.append("}")
    return "\n".join(lines)


# ---------- Dispatch ----------


def render(graph: Graph, format: str, audit_path: Path | None = None) -> str:
    audit = None
    if audit_path is not None and audit_path.is_file():
        with audit_path.open() as f:
            audit = json.load(f)
    if format == "mermaid":
        return mermaid_diagram(graph, audit)
    if format == "dot":
        return dot_diagram(graph, audit)
    raise ValueError(f"Unknown format: {format}. Use 'mermaid' or 'dot'.")
