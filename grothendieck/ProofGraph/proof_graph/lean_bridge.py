"""Lean bridge: thin wrappers around `lake build` and `lake env lean`.

Each call assumes the project root is the current working directory (where
`lakefile.toml` lives). All Lean invocations are run with `lake env lean`
so the Mathlib toolchain is on the path.
"""

from __future__ import annotations

import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


@dataclass
class LakeResult:
    """Outcome of a `lake env lean` or `lake build` invocation."""

    ok: bool
    stdout: str
    stderr: str
    returncode: int


def lake_build_module(module: str, *, project_root: Path | None = None) -> LakeResult:
    """Run `lake build <module>`. The module is the Lean dotted path
    (e.g., `LeanProof.MainTheorem`).
    """
    cwd = project_root or PROJECT_ROOT
    proc = subprocess.run(
        ["lake", "build", module],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    return LakeResult(
        ok=(proc.returncode == 0),
        stdout=proc.stdout,
        stderr=proc.stderr,
        returncode=proc.returncode,
    )


def file_to_module(file_path: str | Path) -> str:
    """Convert a Lean file path (relative to project root) to a module name.

    Example: ``LeanProof/MainTheorem.lean`` → ``LeanProof.MainTheorem``.
    """
    p = Path(file_path)
    if p.suffix != ".lean":
        raise ValueError(f"Not a Lean file: {file_path}")
    parts = list(p.with_suffix("").parts)
    return ".".join(parts)


def print_axioms(theorem: str, *, import_module: str,
                 project_root: Path | None = None) -> LakeResult:
    """Run `#print axioms <theorem>` in a tmp file that imports `<import_module>`,
    via `lake env lean`. Returns the raw output.
    """
    cwd = project_root or PROJECT_ROOT
    src = f"import {import_module}\n\n#print axioms {theorem}\n"
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=cwd, delete=False, encoding="utf-8"
    ) as tf:
        tmp_path = Path(tf.name)
        tf.write(src)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        return LakeResult(
            ok=(proc.returncode == 0),
            stdout=proc.stdout,
            stderr=proc.stderr,
            returncode=proc.returncode,
        )
    finally:
        tmp_path.unlink(missing_ok=True)


def parse_axioms_output(stdout: str) -> list[str]:
    """Parse the output of `#print axioms <name>` into a list of axiom names.

    The output looks like:

        'X.foo' depends on axioms: [propext,
         Classical.choice,
         Quot.sound]

    or, when there are no axioms:

        'X.foo' does not depend on any axioms

    We extract the names between the brackets, ignoring whitespace.
    """
    text = stdout.strip()
    if "does not depend on any axioms" in text:
        return []
    if "depends on axioms" not in text:
        # Could be an error / empty / unexpected form. Return empty;
        # the caller should treat ok=False as the failure signal.
        return []
    # Take everything inside the first matching brackets.
    try:
        lbr = text.index("[")
        rbr = text.rindex("]")
    except ValueError:
        return []
    body = text[lbr + 1 : rbr]
    names = [w.strip().rstrip(",").strip() for w in body.replace("\n", " ").split(",")]
    return [n for n in names if n]
