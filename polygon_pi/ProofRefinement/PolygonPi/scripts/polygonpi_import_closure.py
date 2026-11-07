#!/usr/bin/env python3
"""
polygonpi_import_closure.py — transitive import-closure auditor.

Resolves the full import closure of one or more Lean modules across the project
and the vendored Lean packages under `.lake/packages`, then reports whether any
module matching a blocked pattern appears anywhere in that closure.

Two facts about this Mathlib (Lean v4.28.0, module system) drive the design:

  1. Imports carry modifiers. The tree uses `public import M` 23818 times and
     bare `import M` only 319 times, plus a handful of `meta import M`. A parser
     anchored on `^import` sees almost nothing, and — worse — a candidate could
     evade a naive audit by writing `module` + `public import <blocked>`.
     `IMPORT_RE` therefore accepts any sequence of `public` / `private` / `meta`
     modifiers before `import`.

  2. Several Mathlib docstrings contain a literal `import Mathlib` inside a code
     fence (e.g. Mathlib/Analysis/Normed/Algebra/Exponential.lean). Comments are
     stripped before parsing, or the closure false-positives on the mega-import.

Modules that cannot be resolved to a file (Lean core: `Init.*`, `Std.*`,
`Lean.*`) are treated as leaves and reported separately.

Usage:
    polygonpi_import_closure.py MODULE [MODULE ...]
        [--blocked-exact M] [--blocked-prefix P]
        [--project-root DIR] [--json] [--list]

Exit status: 0 if no blocked module appears in any closure, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.+)$",
    re.MULTILINE,
)


def strip_comments(src: str) -> str:
    """Remove Lean block comments (nestable, incl. `/-!` and `/--`) and line
    comments, preserving newlines so line-anchored regexes still behave."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def parse_imports(src: str) -> list[str]:
    """Module names imported by `src`. Comments are stripped first."""
    imports: list[str] = []
    for m in IMPORT_RE.finditer(strip_comments(src)):
        line = m.group(1).strip()
        # `import A B` is not valid Lean, but tolerate whitespace-separated
        # tokens rather than silently dropping a second name.
        for token in line.split():
            if re.fullmatch(r"[A-Za-z_][\w.'’]*", token):
                imports.append(token)
    return imports


class ModuleResolver:
    """Maps a module name to a source file across the project and packages."""

    def __init__(self, project_root: Path):
        self.project_root = project_root.resolve()
        self.roots: list[Path] = [self.project_root]
        pkgs = self.project_root / ".lake" / "packages"
        if pkgs.is_dir():
            self.roots.extend(sorted(p for p in pkgs.iterdir() if p.is_dir()))
        self._cache: dict[str, Path | None] = {}

    def resolve(self, module: str) -> Path | None:
        if module in self._cache:
            return self._cache[module]
        rel = Path(*module.split(".")).with_suffix(".lean")
        found: Path | None = None
        for root in self.roots:
            cand = root / rel
            if cand.is_file():
                found = cand
                break
        self._cache[module] = found
        return found


def closure(modules: list[str], resolver: ModuleResolver) -> tuple[set[str], set[str]]:
    """Transitive import closure. Returns (resolved, unresolved-leaves)."""
    seen: set[str] = set()
    unresolved: set[str] = set()
    stack = list(modules)
    while stack:
        mod = stack.pop()
        if mod in seen or mod in unresolved:
            continue
        path = resolver.resolve(mod)
        if path is None:
            unresolved.add(mod)
            continue
        seen.add(mod)
        try:
            src = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        stack.extend(parse_imports(src))
    return seen, unresolved


def is_blocked(module: str, blocked_exact: set[str], blocked_prefixes: tuple[str, ...]) -> bool:
    if module in blocked_exact:
        return True
    return any(module == p or module.startswith(p + ".") for p in blocked_prefixes)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("modules", nargs="+")
    ap.add_argument("--blocked-exact", action="append", default=[])
    ap.add_argument("--blocked-prefix", action="append", default=[])
    ap.add_argument("--project-root", default=None)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--list", action="store_true", help="print every module in the closure")
    args = ap.parse_args()

    root = Path(args.project_root) if args.project_root else Path(__file__).resolve().parents[3]
    resolver = ModuleResolver(root)

    blocked_exact = set(args.blocked_exact)
    blocked_prefixes = tuple(args.blocked_prefix)

    results = {}
    any_blocked = False
    for mod in args.modules:
        seen, unresolved = closure([mod], resolver)
        hits = sorted(m for m in seen if is_blocked(m, blocked_exact, blocked_prefixes))
        # A module that is itself blocked but unresolvable (e.g. physically
        # deleted) must still be reported.
        hits += sorted(m for m in unresolved if is_blocked(m, blocked_exact, blocked_prefixes))
        any_blocked = any_blocked or bool(hits)
        results[mod] = {
            "closure_size": len(seen),
            "unresolved": sorted(unresolved),
            "blocked": hits,
            "modules": sorted(seen) if args.list else None,
        }

    if args.json:
        print(json.dumps(results, indent=2, sort_keys=True))
    else:
        for mod, r in results.items():
            status = "BLOCKED" if r["blocked"] else "clean"
            print(f"{mod}: closure={r['closure_size']} unresolved={len(r['unresolved'])} {status}")
            for b in r["blocked"]:
                print(f"    BLOCK {b}")
            if args.list:
                for m in r["modules"]:
                    print(f"    {m}")

    return 1 if any_blocked else 0


if __name__ == "__main__":
    sys.exit(main())
