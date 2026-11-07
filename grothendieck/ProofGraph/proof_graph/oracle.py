"""Oracle: invoke the Python certified-arithmetic function for a node.

Walks transitive computational ancestors of a target node, runs each in
topological order, and returns a state dict mapping {slug: {output_name: value}}.

Input wiring:
- ``"const:<key>"``  — pull from `_index.toml` `[constants]` (with optional
  ``cast`` to ``float`` / ``int`` / ``str``).
- ``"node:<slug>:<output>"`` — pull from the named output of an already-run node.

Output extraction:
- a dotted path into the function's return value (e.g., ``"C_r"``,
  ``"meta.M_diff"``), or
- ``"tuple_index:<i>"`` for a function returning a tuple.

Nodes without a fully wired ``[python]`` block are skipped with a warning
(Phase 2 ergonomics: only the lemma_5_4 chain is wired).
"""

from __future__ import annotations

import importlib
import sys
from fractions import Fraction
from typing import Any

from .graph import Graph


def _arb_to_rational_upper(value: Any) -> Fraction | None:
    """Best-effort conversion of an Arb / arb_series / float to a rational upper bound.

    Reuses `ProofRefinement.Lemma54.Numerical_Library._arb_helpers.arb_to_rational_ub`
    when available — it provides a sound rational upper bound with a small
    safety margin. Returning None signals "no rational form available".
    """
    try:
        from flint import arb  # type: ignore[import]
    except ModuleNotFoundError:
        return None
    if isinstance(value, arb):
        try:
            from ProofRefinement.Lemma54.Numerical_Library._arb_helpers import (
                arb_to_rational_ub,
            )
            return arb_to_rational_ub(value, max_denom=10**9)
        except Exception:
            try:
                return Fraction(float(value.upper())).limit_denominator(10**12)
            except Exception:
                return None
    if isinstance(value, (int, float)):
        return Fraction(value).limit_denominator(10**15)
    return None


def _cast_value(raw: Any, cast: str | None) -> Any:
    if cast is None:
        return raw
    if isinstance(raw, str) and cast == "float":
        # `_index.toml` constants are strings like "23/25"; parse fraction.
        if "/" in raw:
            num, den = raw.split("/", 1)
            return float(int(num)) / float(int(den))
        return float(raw)
    if cast == "int":
        return int(raw)
    if cast == "str":
        return str(raw)
    if cast == "float":
        return float(raw)
    return raw


def _resolve_input(
    spec: Any,
    *,
    state: dict[str, dict[str, Any]],
    constants: dict[str, str | int],
) -> Any:
    """Resolve a single input spec into a Python value."""
    if isinstance(spec, str):
        # Bare string source, no cast.
        source, cast = spec, None
    elif isinstance(spec, dict):
        source = spec.get("source")
        cast = spec.get("cast")
        if source is None:
            raise ValueError(f"Input spec missing 'source': {spec!r}")
    else:
        raise TypeError(f"Bad input spec: {spec!r}")

    if source.startswith("const:"):
        key = source.removeprefix("const:")
        if key not in constants:
            raise KeyError(f"Constant {key!r} not in _index.toml [constants]")
        return _cast_value(constants[key], cast)
    if source.startswith("node:"):
        rest = source.removeprefix("node:")
        node_slug, output_key = rest.split(":", 1)
        if node_slug not in state:
            raise KeyError(
                f"Source node {node_slug!r} has not been run "
                f"(or has no [python] block)"
            )
        if output_key not in state[node_slug]:
            raise KeyError(
                f"Node {node_slug!r} did not produce output {output_key!r}; "
                f"available: {list(state[node_slug])}"
            )
        return state[node_slug][output_key]
    raise ValueError(f"Unknown source scheme: {source!r}")


def _extract_output(returned: Any, path: str) -> Any:
    """Extract one output value from the function's return value, per `path`."""
    if path.startswith("tuple_index:"):
        idx = int(path.removeprefix("tuple_index:"))
        return returned[idx]
    # Dotted path into a dict (or attribute).
    cur = returned
    for part in path.split("."):
        if isinstance(cur, dict):
            cur = cur[part]
        else:
            cur = getattr(cur, part)
    return cur


def _invoke_node(
    node,
    *,
    state: dict[str, dict[str, Any]],
    constants: dict[str, str | int],
    verbose: bool,
) -> dict[str, Any]:
    py = node.python
    if not (py.module and py.function):
        raise RuntimeError(f"Node {node.slug!r} has no [python] handle")

    raw_inputs = node.raw.get("python", {}).get("inputs", {}) or {}
    raw_kwargs = node.raw.get("python", {}).get("kwargs", {}) or {}
    raw_outputs = node.raw.get("python", {}).get("outputs", {}) or {}

    # Build kwargs dict.
    kwargs: dict[str, Any] = {}
    for arg_name, spec in raw_inputs.items():
        kwargs[arg_name] = _resolve_input(spec, state=state, constants=constants)
    for arg_name, value in raw_kwargs.items():
        kwargs[arg_name] = value

    if verbose:
        print(f"[oracle] {node.slug}: {py.module}.{py.function}", file=sys.stderr)
        for k, v in kwargs.items():
            v_str = repr(v) if len(repr(v)) < 80 else f"<{type(v).__name__}>"
            print(f"           {k} = {v_str}", file=sys.stderr)

    module = importlib.import_module(py.module)
    fn = getattr(module, py.function)
    returned = fn(**kwargs)

    out: dict[str, Any] = {}
    for output_name, path in raw_outputs.items():
        out[output_name] = _extract_output(returned, path)
    return out


def run_oracle_for_node(graph: Graph, slug: str, *, verbose: bool = False) -> dict[str, Any]:
    """Run the oracle for `slug` and all transitive computational ancestors.

    Returns a JSON-serializable dict summarizing each node's outputs (rational
    upper bound + repr of the original value).
    """
    target = graph[slug]
    # Compute transitive parents (closure of the parents relation).
    needed = set()
    queue = [slug]
    while queue:
        s = queue.pop()
        if s in needed:
            continue
        needed.add(s)
        for parent in graph[s].parents:
            queue.append(parent)

    state: dict[str, dict[str, Any]] = {}
    summary: dict[str, Any] = {"target": slug, "ran": [], "skipped": []}

    for node in graph.topological_order():
        if node.slug not in needed:
            continue
        if not (node.has_python and node.python.function):
            summary["skipped"].append({"slug": node.slug, "reason": "no [python] handle"})
            continue
        if verbose:
            print(f"[oracle] running {node.slug}...", file=sys.stderr)
        out = _invoke_node(node, state=state, constants=graph.config.constants, verbose=verbose)
        state[node.slug] = out
        # Build a printable summary entry.
        printable = {}
        for k, v in out.items():
            rat = _arb_to_rational_upper(v)
            printable[k] = {
                "type": type(v).__name__,
                "repr": repr(v) if len(repr(v)) < 200 else repr(v)[:197] + "...",
                "rational_upper": str(rat) if rat is not None else None,
            }
        summary["ran"].append({"slug": node.slug, "outputs": printable})

    return summary
