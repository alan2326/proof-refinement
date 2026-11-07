"""
Adapter between ShinkaEvolve and the Korenblum Lean evaluator.

We import `Evaluator.py` in-process (rather than shelling out) so we can
monkey-patch `theorem_type_check` and `collect_used_axioms` to use
uuid-suffixed wrapper filenames. Without that patch, those two functions
write a fixed path at the Korenblum project root, so 16 concurrent jobs
clobber each other's wrappers. Gate logic is otherwise unchanged — same
lake commands, same audits, same scoring.

Lifecycle for one generation:

1. ShinkaEvolve writes the candidate at `program_path`.
2. We rewrite the placeholder namespace and copy to a unique
   `.../Candidates/Shinka_<staging_id>.lean`.
3. We invoke the patched `Evaluator.main()` against that file, capturing
   stdout/stderr.
4. We delete the staged file.
5. We hand ShinkaEvolve `metrics.json` (`combined_score` + per-stage
   PASS/FAIL detail) and `correct.json`.

`combined_score` is `c_value` if every gate passes, otherwise 0.0.
"""

from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import time
import uuid
from pathlib import Path

# `Evaluator.py` lives here; the Lean project root is its grandparent.
KORENBLUM_LEAN_ROOT = Path(__file__).resolve().parents[1]
KORENBLUM_WORKSPACE = KORENBLUM_LEAN_ROOT / "ProofRefinement" / "Korenblum"
EVALUATOR_PY = KORENBLUM_WORKSPACE / "Evaluator.py"
CANDIDATES_DIR = KORENBLUM_WORKSPACE / "Candidates"

NAMESPACE_PREFIX = "ProofRefinement.Korenblum.Candidates"
PLACEHOLDER_NAMESPACE_RE = re.compile(
    r"^(\s*(?:namespace|end)\s+)ProofRefinement\.Korenblum\.Candidates\.\S+\s*$",
    flags=re.MULTILINE,
)


# ---------------------------------------------------------------------------
# Load Evaluator.py as a module and monkey-patch the two race-prone temp
# wrapper paths to be uuid-unique per process.
# ---------------------------------------------------------------------------
def _load_evaluator_module():
    module_name = "KorenblumEvaluatorBackend"
    spec = importlib.util.spec_from_file_location(module_name, str(EVALUATOR_PY))
    if spec is None or spec.loader is None:
        raise ImportError(f"Cannot load {EVALUATOR_PY}")
    mod = importlib.util.module_from_spec(spec)
    # Register in sys.modules BEFORE exec so @dataclass / typing helpers
    # that look up the class's __module__ in sys.modules don't trip.
    sys.modules[module_name] = mod
    spec.loader.exec_module(mod)
    return mod


EvalMod = _load_evaluator_module()


def _unique_wrapper_path(prefix: str) -> Path:
    """Per-call wrapper at PROJECT_ROOT with a uuid suffix so concurrent
    evaluators don't race on the same path."""
    return EvalMod.PROJECT_ROOT / f".{prefix}_{uuid.uuid4().hex[:8]}.lean"


def _patched_theorem_type_check(path, parsed, config):
    """Identical to Evaluator.theorem_type_check except the wrapper file
    name is uuid-suffixed."""
    t0 = time.monotonic()
    module = EvalMod.module_name_for_path(path)
    theorem_qual = f"{parsed.namespace}.{config.sink_theorem}"
    c_qual = f"{parsed.namespace}.{config.constant_def}"
    wrapper = _unique_wrapper_path("kor_typecheck")
    wrapper.write_text(
        "\n".join([
            f"import {module}",
            "import ProofRefinement.Korenblum.Proof.CandidateContract",
            "",
            f"#check (@{theorem_qual} : ProofRefinement.Korenblum.ValidKorenblumBound {c_qual})",
            "",
        ])
    )
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(wrapper)],
            cwd=EvalMod.PROJECT_ROOT,
            capture_output=True, text=True, timeout=120,
        )
    finally:
        wrapper.unlink(missing_ok=True)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "error:" not in out
    return ok, out, time.monotonic() - t0


def _patched_collect_used_axioms(path, theorem_qual):
    """Identical to Evaluator.collect_used_axioms except the wrapper file
    name is uuid-suffixed."""
    t0 = time.monotonic()
    wrapper = _unique_wrapper_path("kor_axioms")
    module = EvalMod.module_name_for_path(path)
    wrapper.write_text(f"import {module}\n#print axioms {theorem_qual}\n")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(wrapper)],
            cwd=EvalMod.PROJECT_ROOT,
            capture_output=True, text=True, timeout=120,
        )
    finally:
        wrapper.unlink(missing_ok=True)
    elapsed = time.monotonic() - t0
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        return False, [], out, elapsed
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", out, re.DOTALL)
    if not m:
        return False, [], out, elapsed
    raw = m.group(1)
    names = [s.strip() for s in raw.split(",") if s.strip()]
    return True, names, out, elapsed


# Install patches into the loaded Evaluator module. `EvalMod.main()` looks
# up `theorem_type_check` and `collect_used_axioms` via its own __globals__,
# so reassigning the names on EvalMod is sufficient.
EvalMod.theorem_type_check = _patched_theorem_type_check
EvalMod.collect_used_axioms = _patched_collect_used_axioms


# ---------------------------------------------------------------------------
# Staging the candidate file into the Lean project.
# ---------------------------------------------------------------------------
def _staging_id(results_dir: Path) -> str:
    parts = results_dir.resolve().parts
    gen_marker = next((p for p in reversed(parts) if p.startswith("gen_")), "gen_x")
    suffix = uuid.uuid4().hex[:6]
    return f"{gen_marker}_{suffix}"


_LOCAL_AXIOM_RE = re.compile(r"^\s*axiom\s+\w+", flags=re.MULTILINE)


class _CandidateRejected(Exception):
    """Raised when the candidate fails a parse-time gate."""


def _stage_candidate(program_path: Path, staging_id: str) -> Path:
    src = program_path.read_text()

    # Parse-time gate: forbid local `axiom` declarations.
    #
    # Without this gate, the LLM trivially defeats the trust surface by
    # writing `axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value`
    # where `c_value` is a candidate-controlled `def`. The downstream
    # axiom-audit only checks short names, not types, so the redeclared
    # axiom asserts the bound at any `c_value` the candidate chooses.
    # Closing this loophole forces the LLM to use the trusted axiom in
    # `ProofRefinement.Korenblum.Proof.ShinkaTrustedSeed`, which is pinned
    # to the literal `(3554 : ℝ) / 10000`.
    if _LOCAL_AXIOM_RE.search(src):
        raise _CandidateRejected(
            "candidate declares a local `axiom`; ShinkaAblation forbids "
            "local axiom declarations. Use the trusted axiom "
            "`ProofRefinement.Korenblum.Proof.ShinkaTrustedSeed.hEq15_seed_3554` "
            "instead, or prove `Eq15ScalarBound K c_value` from Mathlib."
        )

    new_module_leaf = f"Shinka_{staging_id}"
    new_namespace = f"{NAMESPACE_PREFIX}.{new_module_leaf}"

    def _sub(m: re.Match[str]) -> str:
        return f"{m.group(1)}{new_namespace}"

    src = PLACEHOLDER_NAMESPACE_RE.sub(_sub, src)

    staged_path = CANDIDATES_DIR / f"{new_module_leaf}.lean"
    staged_path.write_text(src)
    return staged_path


# ---------------------------------------------------------------------------
# Run the in-process patched Evaluator and parse its output.
# ---------------------------------------------------------------------------
def _run_evaluator(staged_path: Path) -> tuple[bool, str, dict]:
    saved_argv = sys.argv
    sys.argv = ["Evaluator.py", "--file", str(staged_path), "--no-log"]

    stdout_buf = io.StringIO()
    stderr_buf = io.StringIO()
    t0 = time.monotonic()
    exit_code = 0

    try:
        with contextlib.redirect_stdout(stdout_buf), contextlib.redirect_stderr(stderr_buf):
            try:
                EvalMod.main()
            except SystemExit as e:
                if e.code is None:
                    exit_code = 0
                elif isinstance(e.code, int):
                    exit_code = e.code
                else:
                    exit_code = 1
    finally:
        sys.argv = saved_argv

    elapsed = time.monotonic() - t0
    out = stdout_buf.getvalue() + "\n--- stderr ---\n" + stderr_buf.getvalue()

    summary = {
        "exit_code": exit_code,
        "elapsed_s": round(elapsed, 2),
        "passed": exit_code == 0 and "status: PASS" in stdout_buf.getvalue(),
    }
    score_match = re.search(r"score \(\w+\):\s*(\S+)", stdout_buf.getvalue())
    if score_match:
        summary["score_str"] = score_match.group(1)
    for stage in [
        "workspace imports", "import audit", "compile", "type-check",
        "axiom scan", "axiom audit", "oracle audit",
    ]:
        m = re.search(rf"{re.escape(stage)}:\s*(PASS|FAIL)", stdout_buf.getvalue())
        if m:
            summary[f"stage_{stage.replace(' ', '_')}"] = m.group(1)
    fail_reason = re.search(r"^reason:\s*(.+)$", stdout_buf.getvalue(), flags=re.MULTILINE)
    if fail_reason:
        summary["fail_reason"] = fail_reason.group(1).strip()

    return summary["passed"], out, summary


def _parse_score_to_float(score_str: str) -> float:
    if "/" in score_str:
        n, d = score_str.split("/", 1)
        try:
            return float(int(n)) / float(int(d))
        except ValueError:
            return 0.0
    try:
        return float(score_str)
    except ValueError:
        return 0.0


def main(program_path: str, results_dir: str) -> None:
    program_path = Path(program_path).resolve()
    results_dir = Path(results_dir).resolve()
    results_dir.mkdir(parents=True, exist_ok=True)

    # Make sure UV_CACHE_DIR is set so the lake subprocesses Evaluator
    # spawns inherit a sane uv cache.
    os.environ.setdefault("UV_CACHE_DIR", str(KORENBLUM_LEAN_ROOT / ".uv-cache"))

    staging_id = _staging_id(results_dir)
    staged_path: Path | None = None
    correct = False
    error = ""
    metrics: dict = {"combined_score": 0.0, "public": {}, "private": {}}

    try:
        if not program_path.is_file():
            raise FileNotFoundError(f"program_path {program_path} not found")
        if not EVALUATOR_PY.is_file():
            raise FileNotFoundError(f"Evaluator.py not found at {EVALUATOR_PY}")

        try:
            staged_path = _stage_candidate(program_path, staging_id)
        except _CandidateRejected as e:
            # Synthesise a fail summary so ShinkaEvolve sees a 0 score and
            # records the rejection reason in metrics.json.
            metrics["combined_score"] = 0.0
            correct = False
            error = str(e)
            metrics["public"] = {
                "passed": False,
                "fail_reason": error,
                "stage_parse_gate": "FAIL",
            }
            metrics["private"] = {
                "summary": {"exit_code": 1, "passed": False, "fail_reason": error},
            }
            (results_dir / "evaluator_stdout.txt").write_text(
                f"parse-time gate rejected candidate:\n{error}\n"
            )
            (results_dir / "correct.json").write_text(
                json.dumps({"correct": correct, "error": error}, indent=2)
            )
            (results_dir / "metrics.json").write_text(
                json.dumps(metrics, indent=2)
            )
            print(f"combined_score: {metrics['combined_score']}")
            print(f"correct:        {correct}")
            print(f"error:          {error}")
            return

        passed, raw, summary = _run_evaluator(staged_path)

        (results_dir / "evaluator_stdout.txt").write_text(raw)

        if passed and "score_str" in summary:
            score_f = _parse_score_to_float(summary["score_str"])
            metrics["combined_score"] = score_f
            correct = True
            metrics["public"] = {
                "passed": True,
                "c_value_str": summary["score_str"],
                "c_value_float": score_f,
                "elapsed_s": summary["elapsed_s"],
            }
            metrics["private"] = {"summary": summary}
        else:
            metrics["combined_score"] = 0.0
            correct = False
            error = summary.get("fail_reason", "evaluator failed")
            metrics["public"] = {
                "passed": False,
                "fail_reason": error,
                "elapsed_s": summary.get("elapsed_s"),
                **{k: v for k, v in summary.items() if k.startswith("stage_")},
            }
            metrics["private"] = {"summary": summary}

    except Exception as e:
        correct = False
        error = f"{type(e).__name__}: {e}"
        metrics["combined_score"] = 0.0
        metrics["public"] = {"passed": False, "fail_reason": error}
    finally:
        if staged_path is not None and staged_path.exists():
            try:
                staged_path.unlink()
            except OSError:
                pass

    (results_dir / "correct.json").write_text(
        json.dumps({"correct": correct, "error": error}, indent=2)
    )
    (results_dir / "metrics.json").write_text(
        json.dumps(metrics, indent=2)
    )

    print(f"combined_score: {metrics['combined_score']}")
    print(f"correct:        {correct}")
    if error:
        print(f"error:          {error}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--program_path", type=str, required=True)
    parser.add_argument("--results_dir", type=str, required=True)
    args = parser.parse_args()
    main(args.program_path, args.results_dir)
