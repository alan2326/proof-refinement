"""Build a dependency graph of the Lean lemmas/theorems/defs/axioms in the
final Lemma 5.4 candidate (V28) and its supporting library, restricted to
the cone reachable from `lemma_5_4_search`.

Output:
  paper_artifacts/proof_graph/proof_graph.dot
  paper_artifacts/proof_graph/proof_graph.svg
  paper_artifacts/proof_graph/proof_graph.pdf
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LIB  = REPO / "ProofRefinement" / "Lemma54" / "Proof" / "Lib"
CAND = REPO / "ProofRefinement" / "Lemma54" / "Candidates"
OUT  = Path(__file__).resolve().parent

ENTRY = "lemma_5_4_search"

LEAN_FILES = [
    CAND / "V28.lean",
    LIB  / "Lemma54_Paper.lean",
    LIB  / "Lemma54_Paper_Cauchy.lean",
    LIB  / "Lemma54_Paper_Identity.lean",
    LIB  / "Lemma54_Paper_Pderiv.lean",
    LIB  / "Lemma54_Paper_Pderiv_Single.lean",
    LIB  / "Lemma54_Paper_Taylor.lean",
    LIB  / "Lemma54_Paper_Main.lean",
]

DECL_RE = re.compile(
    r"^(theorem|lemma|def|axiom)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
WORD_BOUND = re.compile(r"\b{}\b")


COMMENT_RE = re.compile(r"/-(.*?)-/", re.DOTALL)


def strip_comments(src: str) -> str:
    """Replace `/- ... -/` blocks with whitespace of equal length so byte
    offsets are preserved but the comment text doesn't match decl regex.
    Also blank out `--` line comments."""
    def blank(m: re.Match) -> str:
        return re.sub(r"[^\n]", " ", m.group(0))
    src = COMMENT_RE.sub(blank, src)
    src = re.sub(r"--[^\n]*", lambda m: " " * (m.end() - m.start()), src)
    return src


def extract_decls(lean_path: Path) -> list[tuple[str, str, str, str]]:
    """Return [(kind, name, source_file, body), ...] in source order."""
    raw = lean_path.read_text()
    src = strip_comments(raw)
    matches = list(DECL_RE.finditer(src))
    out = []
    for i, m in enumerate(matches):
        start = m.start()
        end   = matches[i + 1].start() if i + 1 < len(matches) else len(src)
        body  = src[start:end]
        out.append((m.group(1), m.group(2), lean_path.name, body))
    return out


def main():
    OUT.mkdir(parents=True, exist_ok=True)

    decls: dict[str, tuple[str, str, str]] = {}  # name -> (kind, file, body)
    for f in LEAN_FILES:
        for kind, name, fname, body in extract_decls(f):
            if name in decls:
                continue
            decls[name] = (kind, fname, body)

    print(f"parsed {len(decls)} declarations across {len(LEAN_FILES)} files")

    edges: list[tuple[str, str]] = []
    for name, (_, _, body) in decls.items():
        for other in decls:
            if other == name:
                continue
            if re.search(rf"\b{re.escape(other)}\b", body):
                edges.append((name, other))

    if ENTRY not in decls:
        raise SystemExit(f"entry point {ENTRY!r} not found among parsed decls")

    adj: dict[str, set[str]] = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)

    reachable: set[str] = set()
    stack = [ENTRY]
    while stack:
        n = stack.pop()
        if n in reachable:
            continue
        reachable.add(n)
        for v in adj.get(n, ()):
            if v not in reachable:
                stack.append(v)

    print(f"cone reachable from {ENTRY}: {len(reachable)} nodes")

    edges = [(u, v) for u, v in edges if u in reachable and v in reachable]

    file_color = {
        "V28.lean":                          "#e8833a",
        "Lemma54_Paper.lean":                "#9bb7d4",
        "Lemma54_Paper_Cauchy.lean":         "#b9d4a7",
        "Lemma54_Paper_Identity.lean":       "#f3d27a",
        "Lemma54_Paper_Pderiv.lean":         "#d8a8c7",
        "Lemma54_Paper_Pderiv_Single.lean":  "#c79bd6",
        "Lemma54_Paper_Taylor.lean":         "#f5b58a",
        "Lemma54_Paper_Main.lean":           "#a7c7d4",
    }
    kind_shape = {
        "axiom":   "octagon",
        "theorem": "box",
        "lemma":   "box",
        "def":     "ellipse",
    }

    dot_path = OUT / "proof_graph.dot"
    with dot_path.open("w") as f:
        f.write("digraph proof_graph {\n")
        f.write('  rankdir="TB";\n')
        f.write('  graph [bgcolor="white", overlap=false, splines=true,\n')
        f.write('         ranksep=0.7, nodesep=0.25];\n')
        f.write('  node  [style="filled,rounded", fontname="Inter, Helvetica, Arial", fontsize=10];\n')
        f.write('  edge  [color="#888888", arrowsize=0.6];\n\n')

        for n in sorted(reachable):
            kind, fname, _ = decls[n]
            color = file_color.get(fname, "#dddddd")
            shape = kind_shape.get(kind, "box")
            pen = "3" if n == ENTRY else "1"
            tip = f"{kind} ({fname})"
            f.write(
                f'  "{n}" [shape="{shape}", fillcolor="{color}", '
                f'penwidth="{pen}", tooltip="{tip}"];\n'
            )
        f.write("\n")

        for u, v in edges:
            f.write(f'  "{u}" -> "{v}";\n')

        # Legend at the bottom-right.
        f.write("\n  subgraph cluster_legend {\n")
        f.write('    label="legend"; rank=sink; style="rounded"; color="#cccccc"; fontsize=11;\n')
        for fname, color in file_color.items():
            if fname not in {decls[n][1] for n in reachable}:
                continue
            tag = f"legend_{fname.replace('.', '_')}"
            f.write(
                f'    "{tag}" [label="{fname}", shape="box", '
                f'fillcolor="{color}", style="filled,rounded"];\n'
            )
        f.write("  }\n")
        f.write("}\n")

    print(f"wrote {dot_path}")

    # Two layouts: hierarchical (dot, rankdir=TB) and force-directed (fdp).
    # The fdp version is usually nicer for papers because it's more compact /
    # square; the dot version is easier to read top-down for the audit trail.
    for engine, suffix in [("fdp", "_fdp"), ("dot", "_hier")]:
        for ext in ("svg", "pdf", "png"):
            out = OUT / f"proof_graph{suffix}.{ext}"
            cmd = [engine, f"-T{ext}", str(dot_path), "-o", str(out)]
            if engine == "fdp":
                cmd += ["-Goverlap=false", "-Gsplines=true"]
            if ext == "png":
                cmd.insert(1, "-Gdpi=140")
            subprocess.run(cmd, check=True)
            print(f"wrote {out}")

    # Convenience copies named "proof_graph.{svg,pdf,png}" pointing at fdp.
    for ext in ("svg", "pdf", "png"):
        src = OUT / f"proof_graph_fdp.{ext}"
        dst = OUT / f"proof_graph.{ext}"
        dst.write_bytes(src.read_bytes())


if __name__ == "__main__":
    main()
