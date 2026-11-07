"""For every candidate V0..V28 in `ProofRefinement/Lemma54/Candidates/`,
render the Lean dependency graph reachable from `lemma_5_4_search` in that
candidate. Saves one PNG / SVG / PDF per candidate, plus a summary GIF.

Output:
  paper_artifacts/proof_graph/per_candidate/V{k}_proof_graph.{png,svg,pdf}
  paper_artifacts/proof_graph/proof_graph_progression.gif
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LIB  = REPO / "ProofRefinement" / "Lemma54" / "Proof" / "Lib"
CAND = REPO / "ProofRefinement" / "Lemma54" / "Candidates"
OUT  = Path(__file__).resolve().parent / "per_candidate"
GIF  = Path(__file__).resolve().parent / "proof_graph_progression.gif"

ENTRY = "lemma_5_4_search"

LIB_FILES = [
    LIB / "Lemma54_Paper.lean",
    LIB / "Lemma54_Paper_Cauchy.lean",
    LIB / "Lemma54_Paper_Identity.lean",
    LIB / "Lemma54_Paper_Pderiv.lean",
    LIB / "Lemma54_Paper_Pderiv_Single.lean",
    LIB / "Lemma54_Paper_Taylor.lean",
    LIB / "Lemma54_Paper_Main.lean",
]

DECL_RE = re.compile(
    r"^(theorem|lemma|def|axiom)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
COMMENT_RE = re.compile(r"/-(.*?)-/", re.DOTALL)

FILE_COLOR = {
    "Lemma54_Paper.lean":               "#9bb7d4",
    "Lemma54_Paper_Cauchy.lean":        "#b9d4a7",
    "Lemma54_Paper_Identity.lean":      "#f3d27a",
    "Lemma54_Paper_Pderiv.lean":        "#d8a8c7",
    "Lemma54_Paper_Pderiv_Single.lean": "#c79bd6",
    "Lemma54_Paper_Taylor.lean":        "#f5b58a",
    "Lemma54_Paper_Main.lean":          "#a7c7d4",
    "_candidate":                       "#e8833a",
}
KIND_SHAPE = {"axiom": "octagon", "theorem": "box", "lemma": "box", "def": "ellipse"}


def strip_comments(src: str) -> str:
    blank = lambda m: re.sub(r"[^\n]", " ", m.group(0))
    src = COMMENT_RE.sub(blank, src)
    src = re.sub(r"--[^\n]*", lambda m: " " * (m.end() - m.start()), src)
    return src


def extract_decls(path: Path) -> list[tuple[str, str, str]]:
    src = strip_comments(path.read_text())
    matches = list(DECL_RE.finditer(src))
    out = []
    for i, m in enumerate(matches):
        start = m.start()
        end   = matches[i + 1].start() if i + 1 < len(matches) else len(src)
        out.append((m.group(1), m.group(2), src[start:end]))
    return out


def build_one(candidate_path: Path, out_stem: Path) -> int:
    """Build the graph for one candidate. Returns node count in the cone."""
    decls: dict[str, tuple[str, str, str]] = {}  # name -> (kind, file_label, body)

    for f in LIB_FILES:
        for kind, name, body in extract_decls(f):
            decls.setdefault(name, (kind, f.name, body))

    cand_label = "_candidate"
    for kind, name, body in extract_decls(candidate_path):
        decls[name] = (kind, cand_label, body)  # candidate decls override

    if ENTRY not in decls:
        print(f"  skip {candidate_path.name}: no {ENTRY!r}")
        return 0

    edges: list[tuple[str, str]] = []
    for name, (_, _, body) in decls.items():
        for other in decls:
            if other == name:
                continue
            if re.search(rf"\b{re.escape(other)}\b", body):
                edges.append((name, other))

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
            stack.append(v)

    edges = [(u, v) for u, v in edges if u in reachable and v in reachable]

    dot_path = out_stem.with_suffix(".dot")
    with dot_path.open("w") as f:
        f.write("digraph G {\n")
        f.write('  bgcolor="white";\n')
        f.write('  graph [overlap=false, splines=true, ranksep=0.7, nodesep=0.25];\n')
        f.write('  node  [style="filled,rounded", fontname="Inter, Helvetica, Arial", fontsize=10];\n')
        f.write('  edge  [color="#888888", arrowsize=0.6];\n')
        f.write(f'  labelloc="t"; label="{candidate_path.stem}  ({len(reachable)} declarations)"; '
                f'fontsize=18; fontname="Inter, Helvetica, Arial";\n\n')

        for n in sorted(reachable):
            kind, fname, _ = decls[n]
            color = FILE_COLOR.get(fname, "#dddddd")
            shape = KIND_SHAPE.get(kind, "box")
            pen = "3" if n == ENTRY else "1"
            f.write(
                f'  "{n}" [shape="{shape}", fillcolor="{color}", penwidth="{pen}"];\n'
            )

        for u, v in edges:
            f.write(f'  "{u}" -> "{v}";\n')

        f.write("}\n")

    for ext in ("png", "svg", "pdf"):
        cmd = ["fdp", f"-T{ext}", "-Goverlap=false", "-Gsplines=true",
               str(dot_path), "-o", str(out_stem.with_suffix("." + ext))]
        if ext == "png":
            cmd.insert(1, "-Gdpi=120")
        subprocess.run(cmd, check=True)

    return len(reachable)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    candidates = sorted(CAND.glob("V*.lean"),
                        key=lambda p: int(p.stem[1:]))
    print(f"rendering {len(candidates)} candidates → {OUT}")

    pngs: list[Path] = []
    for c in candidates:
        out_stem = OUT / f"{c.stem}_proof_graph"
        n = build_one(c, out_stem)
        if n > 0:
            png = out_stem.with_suffix(".png")
            pngs.append(png)
            print(f"  {c.stem}: {n} nodes → {png.name}")

    if pngs:
        try:
            from PIL import Image
            frames = [Image.open(p).convert("P", palette=Image.ADAPTIVE) for p in pngs]
            # Normalise frame size by padding/letterboxing to the largest dimensions.
            max_w = max(f.width for f in frames)
            max_h = max(f.height for f in frames)
            normed = []
            for f in frames:
                bg = Image.new("RGB", (max_w, max_h), "white")
                bg.paste(f.convert("RGB"), ((max_w - f.width) // 2, (max_h - f.height) // 2))
                normed.append(bg.convert("P", palette=Image.ADAPTIVE))
            normed[0].save(GIF, save_all=True, append_images=normed[1:],
                           duration=900, loop=0, optimize=True)
            print(f"wrote {GIF}")
        except Exception as e:
            print(f"GIF skipped: {e}")


if __name__ == "__main__":
    main()
