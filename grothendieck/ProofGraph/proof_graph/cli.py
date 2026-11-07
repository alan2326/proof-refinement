"""ProofGraph CLI.

Phase 0: --list-order
Phase 1: --audit-snapshot
Phase 2: --run-python --node <slug>
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .graph import load_graph


def _cmd_list_order(args: argparse.Namespace) -> int:
    graph = load_graph(args.nodes_dir)
    print(f"# {len(graph)} nodes, sink = {graph.sink.slug}")
    print()
    for i, node in enumerate(graph.topological_order(), start=1):
        bits = [node.kind.value]
        if node.has_lean:
            bits.append(f"lean={node.lean.sink}")
        if node.has_python:
            bits.append(f"py={node.python.module}.{node.python.function}")
        if node.parents:
            bits.append(f"parents={','.join(node.parents)}")
        print(f"{i:>3}. {node.slug:<26} [{'  '.join(bits)}]")
    return 0


def _cmd_audit_snapshot(args: argparse.Namespace) -> int:
    from .audit import audit_snapshot
    return audit_snapshot(args.nodes_dir, write=args.write, verbose=args.verbose)


def _cmd_run_python(args: argparse.Namespace) -> int:
    from .oracle import run_oracle_for_node
    graph = load_graph(args.nodes_dir)
    if args.node not in graph:
        print(f"Unknown node: {args.node}", file=sys.stderr)
        return 2
    result = run_oracle_for_node(graph, args.node, verbose=args.verbose)
    print(json.dumps(result, indent=2, default=str))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="proof_graph",
        description="ProofGraph CLI — walk the effective proof graph.",
    )
    parser.add_argument(
        "--nodes-dir",
        type=Path,
        default=None,
        help="Override nodes directory (default: ProofGraph/nodes/).",
    )

    sub = parser.add_subparsers(dest="cmd", required=False)

    # Backwards-compat: also support flag-style for Phase 0/1/2 ergonomics.
    parser.add_argument("--list-order", action="store_true",
                        help="Print nodes in topological order and exit.")
    parser.add_argument("--audit-snapshot", action="store_true",
                        help="Run `#print axioms` for every Lean theorem and write the snapshot.")
    parser.add_argument("--run-python", action="store_true",
                        help="Run the Python oracle for --node.")
    parser.add_argument("--run-all", action="store_true",
                        help="End-to-end: run every wired oracle, parse every Effective "
                             "Lean rational, cross-validate, write certificate.json.")
    parser.add_argument("--no-write", action="store_true",
                        help="With --run-all: print certificate to stdout only, do not write.")
    parser.add_argument("--render", type=str, default=None,
                        choices=["mermaid", "dot"],
                        help="Emit the proof graph in the chosen format.")
    parser.add_argument("--audit-input", type=Path, default=None,
                        help="Path to a previous audit.json (annotates --render output with axiom counts).")
    parser.add_argument("--out", type=Path, default=None,
                        help="Write --render output to this path instead of stdout.")
    parser.add_argument("--node", type=str, default=None,
                        help="Node slug for --run-python.")
    parser.add_argument("--write", action="store_true",
                        help="Write audit results back into nodes/<slug>.toml.")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Verbose output.")

    args = parser.parse_args(argv)

    if args.list_order:
        return _cmd_list_order(args)
    if args.audit_snapshot:
        return _cmd_audit_snapshot(args)
    if args.run_python:
        if args.node is None:
            print("--run-python requires --node <slug>", file=sys.stderr)
            return 2
        return _cmd_run_python(args)
    if args.render is not None:
        return _cmd_render(args)
    if args.run_all:
        return _cmd_run_all(args)

    parser.print_help()
    return 0


def _cmd_run_all(args: argparse.Namespace) -> int:
    from .runner import run_certify, write_certificate
    cert = run_certify(nodes_dir=args.nodes_dir, verbose=args.verbose)

    # Print a human-readable summary.
    cv = cert["cross_validation"]
    print(f"# Cross-validations: {cv['passing']}/{cv['total']} passing")
    for c in cv["checks"]:
        mark = "✓" if c.get("ok") else "✗"
        print(f"  {mark} {c['id']}: {c.get('note', '')}")
    print()
    print(f"# Lean rationals ({len(cert['lean_rationals'])}):")
    for name, v in cert["lean_rationals"].items():
        # Use Fraction(num, den) directly — never float.
        print(f"  {name:<14} = {v['num']}/{v['den']}")
    if cert["lean_derived_arb"]:
        print()
        print(f"# Lean derived (arb intervals):")
        for name, v in cert["lean_derived_arb"].items():
            print(f"  {name:<14} arb = {v.get('str', '?')}")
            if v.get("rational_upper"):
                print(f"  {' ':<14} rat≤ {v['rational_upper']}")
    print()
    print(f"# Oracle outputs ({len(cert['oracle_outputs'])} nodes):")
    for slug, outputs in cert["oracle_outputs"].items():
        for k, v in outputs.items():
            if isinstance(v, dict) and v.get("_kind") == "arb":
                ru = v.get("rational_upper") or "?"
                arb_str = v.get("str", "?")
                print(f"  {slug}.{k:<22} {arb_str[:60]}  rat≤ {ru}")
    if cert.get("oracle_assumptions"):
        print()
        oa = cert["oracle_assumptions"]
        n_certified = sum(1 for v in oa.values() if v.get("certified"))
        print(f"# Oracle assumptions ({n_certified}/{len(oa)} certified):")
        for axiom, info in oa.items():
            mark = "✓" if info.get("certified") else "✗"
            print(f"  {mark} {axiom}")
            print(f"      {info.get('description', '').strip()}")
            ids = info.get("certifying_checks") or []
            if ids:
                print(f"      witnessed by: {', '.join(ids)}")
    print()
    print(f"# Headline:")
    for name, v in cert["headline"].items():
        print(f"  {name:<26} {v}")
    if cert["skipped_nodes"]:
        print()
        print(f"# Skipped ({len(cert['skipped_nodes'])} nodes):")
        for s in cert["skipped_nodes"]:
            print(f"  {s['slug']:<26} ({s['reason']})")
    if not args.no_write:
        path = write_certificate(cert)
        print()
        print(f"# certificate.json: {path}")
    return 0 if cv["passing"] == cv["total"] else 1


def _cmd_render(args: argparse.Namespace) -> int:
    from .render import render
    graph = load_graph(args.nodes_dir)
    audit_path = args.audit_input
    if audit_path is None:
        # Default: pick the most recent audit.json under runs/.
        runs_dir = Path(__file__).resolve().parent.parent / "runs"
        if runs_dir.is_dir():
            candidates = sorted(runs_dir.glob("*/audit.json"))
            if candidates:
                audit_path = candidates[-1]
                if args.verbose:
                    print(f"# using audit input: {audit_path}", file=sys.stderr)
    output = render(graph, args.render, audit_path=audit_path)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(output)
        print(f"# wrote {args.render} diagram to {args.out}")
    else:
        print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
