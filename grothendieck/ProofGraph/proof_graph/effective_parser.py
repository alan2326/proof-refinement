"""Parse `def NAME : ℝ := <expr>` declarations from Effective Lean files.

Two kinds of right-hand sides are recognized:

1. Literal rationals — ``23 / 25``, ``7219431 / 1000``, ``1/100``. Returned
   as :class:`fractions.Fraction`.

2. Symbolic formulas — anything that isn't a literal rational. Returned
   as the raw string. The runner can evaluate these using helpers in
   :mod:`proof_graph.cert_compute` (e.g., ``Cr_paper r_val ...``).

The parser is tolerant of whitespace and Lean syntax (it doesn't try to
fully tokenize; it uses a simple regex on the structural pattern). It
ignores comments. It returns a flat dict ``{name: value}``.
"""

from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path
from typing import Union

ParsedValue = Union[Fraction, str]


# `def NAME : ℝ := EXPR` or `def NAME : ℚ := EXPR`
# EXPR can span multiple lines; we capture until the next top-level
# declaration (def/theorem/lemma/axiom/end/private/section/namespace) or
# a blank-line boundary.
_DEF_RE = re.compile(
    r"^\s*def\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:\s*[ℝℚ]\s*:=\s*"
    r"(?P<expr>.+?)"
    r"(?=^\s*(?:def|theorem|lemma|axiom|end|private|section|namespace|/--|/-)|\Z)",
    re.MULTILINE | re.DOTALL,
)

# Matches a literal `INT / INT`, `INT / INT ^ INT`, or just `INT`.
_LITERAL_RE = re.compile(
    r"^\s*(?P<num>-?\d+)"
    r"(\s*/\s*(?P<den>\d+)(\s*\^\s*(?P<exp>\d+))?)?\s*$"
)


def _strip_comments(src: str) -> str:
    """Strip Lean line comments (-- …) and block comments (/- … -/)."""
    # Block comments first.
    src = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    # Line comments.
    src = re.sub(r"--[^\n]*", "", src)
    return src


def parse_effective_file(path: Path) -> dict[str, ParsedValue]:
    """Parse an Effective Lean file and return all `def NAME : ℝ := …` decls.

    Literal rationals are returned as :class:`Fraction`; non-literal
    expressions are returned as raw strings (with whitespace normalized).
    """
    if not path.is_file():
        raise FileNotFoundError(f"Effective Lean file not found: {path}")
    src = _strip_comments(path.read_text())
    out: dict[str, ParsedValue] = {}
    for m in _DEF_RE.finditer(src):
        name = m.group("name")
        # Normalize whitespace: collapse multi-line into single line, strip.
        raw = m.group("expr").strip()
        expr = " ".join(raw.split())
        lit = _LITERAL_RE.match(expr)
        if lit:
            num = int(lit.group("num"))
            den_str = lit.group("den")
            den = int(den_str) if den_str else 1
            exp_str = lit.group("exp")
            if exp_str:
                den = den ** int(exp_str)
            out[name] = Fraction(num, den)
        else:
            out[name] = expr
    return out


def parse_effective_dir(directory: Path) -> dict[str, dict[str, ParsedValue]]:
    """Parse every ``*.lean`` file in ``directory`` and return a nested dict
    ``{filename_stem: {name: value}}``."""
    out: dict[str, dict[str, ParsedValue]] = {}
    for path in sorted(directory.glob("*.lean")):
        out[path.stem] = parse_effective_file(path)
    return out
