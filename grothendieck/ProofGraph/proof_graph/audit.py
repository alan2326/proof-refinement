"""Axiom audit: for every Lean-backed node, run `#print axioms <sink>` and
record the actual axioms used. Optionally compare against the allowed list.
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

from .graph import load_graph, Graph
from .lean_bridge import file_to_module, print_axioms, parse_axioms_output
from .node import Node


# We re-load and re-write the TOML preserving comments, but stdlib `tomllib`
# is read-only. For a snapshot, we write a JSON sidecar (audit.json) rather
# than mutating the source TOMLs unless --write is set, in which case we use
# a minimal merge that preserves the existing keys.

def _audit_one_target(
    graph: Graph, node: Node, theorem: str, file_path: str, *, verbose: bool
) -> dict:
    module = file_to_module(file_path)
    if verbose:
        print(f"[audit] {node.slug}: lake env lean print_axioms {theorem} (via {module})", file=sys.stderr)
    res = print_axioms(theorem, import_module=module)
    if not res.ok:
        return {
            "theorem": theorem,
            "status": "fail",
            "stderr": res.stderr.strip(),
            "stdout": res.stdout.strip(),
        }
    actual = parse_axioms_output(res.stdout)
    allowed = graph.resolve_allowed_axioms(node)
    unexpected = [a for a in actual if a not in allowed]
    return {
        "theorem": theorem,
        "file": file_path,
        "status": "ok" if not unexpected else "unexpected_axioms",
        "actual_axioms": actual,
        "allowed_axioms": allowed,
        "unexpected_axioms": unexpected,
    }


def _audit_one(graph: Graph, node: Node, *, verbose: bool) -> dict:
    """Run `#print axioms` on a node's sink and (if present) effective
    companion. Return a dict suitable for JSON serialization."""
    if not node.has_lean:
        return {
            "slug": node.slug,
            "kind": node.kind.value,
            "status": "skipped",
            "reason": "no Lean handle",
        }

    assert node.lean.sink is not None
    assert node.lean.file is not None

    targets: list[dict] = []
    targets.append(_audit_one_target(graph, node, node.lean.sink, node.lean.file, verbose=verbose))
    if node.lean.effective and node.lean.effective_file:
        targets.append(_audit_one_target(graph, node, node.lean.effective,
                                          node.lean.effective_file, verbose=verbose))

    # Aggregate: status is the worst among targets.
    statuses = [t["status"] for t in targets]
    if any(s == "fail" for s in statuses):
        agg = "fail"
    elif any(s == "unexpected_axioms" for s in statuses):
        agg = "unexpected_axioms"
    else:
        agg = "ok"

    return {
        "slug": node.slug,
        "kind": node.kind.value,
        "lean_sink": node.lean.sink,
        "lean_file": node.lean.file,
        "effective": node.lean.effective,
        "status": agg,
        "targets": targets,
    }


def audit_snapshot(nodes_dir: Path | None, *, write: bool = False, verbose: bool = False) -> int:
    """Audit every Lean-backed node. Write to ProofGraph/runs/<ts>/audit.json.

    If `write=True`, also patch each node's TOML with the `audit.actual_axioms`
    list. (Phase 1 keeps `write=False` by default; the snapshot is canonical.)
    """
    graph = load_graph(nodes_dir)
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H-%M-%S")
    out_dir = Path(__file__).resolve().parent.parent / "runs" / ts
    out_dir.mkdir(parents=True, exist_ok=True)
    audit_path = out_dir / "audit.json"

    results: list[dict] = []
    n_lean = 0
    n_ok = 0
    n_unexpected = 0
    n_fail = 0
    for node in graph.topological_order():
        r = _audit_one(graph, node, verbose=verbose)
        results.append(r)
        if r["status"] == "skipped":
            continue
        n_lean += 1
        if r["status"] == "ok":
            n_ok += 1
        elif r["status"] == "unexpected_axioms":
            n_unexpected += 1
        else:
            n_fail += 1
        # Print a one-liner per node, summarizing all its targets.
        for t in r["targets"]:
            label = "sink" if t["theorem"] == node.lean.sink else "eff"
            if t["status"] == "ok":
                ax = t["actual_axioms"]
                print(f"  ok   {node.slug:<22} [{label:>4}] ({len(ax)} ax): {', '.join(ax) if ax else '(none)'}")
            elif t["status"] == "unexpected_axioms":
                print(f"  WARN {node.slug:<22} [{label:>4}] unexpected: {', '.join(t['unexpected_axioms'])}")
            else:
                print(f"  FAIL {node.slug:<22} [{label:>4}]  {t['theorem']}")
                if verbose and t.get("stderr"):
                    for line in t["stderr"].splitlines()[:10]:
                        print(f"       | {line}")

    summary = {
        "timestamp_utc": ts,
        "total_lean_nodes": n_lean,
        "ok": n_ok,
        "unexpected_axioms": n_unexpected,
        "failed": n_fail,
        "results": results,
    }
    audit_path.write_text(json.dumps(summary, indent=2))
    print()
    print(f"# Audit summary: {n_ok}/{n_lean} ok, {n_unexpected} with unexpected axioms, {n_fail} failed")
    print(f"# Snapshot: {audit_path}")

    if write:
        # Forward-compat hook for later phases. Phase 1 keeps the snapshot
        # external to the per-node TOMLs to preserve them as agent-editable.
        print("# (--write not implemented in Phase 1; snapshot is JSON-only)")

    return 0 if n_fail == 0 else 1
