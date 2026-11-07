#!/usr/bin/env python3
"""
Evaluator.py — rigorous checker + scorer for Lemma 5.4 proof candidates.

A candidate is a single Lean file at `Candidates/<name>.lean` that proves the
sink theorem named in `lemma.toml` (today: `lemma_5_4_search`). The score is
the rational expression named in `lemma.toml` (today: `Cr_val`). Smaller is
better.

Pipeline:

  1. PARSE   — extract `def *_val : ℝ := <rat>` and `axiom *` declarations.
  2. COMPILE — `lake env lean <file>` must succeed.
  3. AXIOM   — every `#print axioms <sink>` dependency must be either
                  (a) a SEED axiom inherited from V0 (allowed but flagged), or
                  (b) an ORACLE axiom registered in `lemma.toml`.
                Anything else (including `sorryAx`) is a hard fail.
  4. ORACLE  — for each oracle axiom, recompute the bound via the
                registered `Numerical_Library` function and verify the
                candidate's declared `<bound_field>_val` ≥ recomputed bound.
  5. SCORE   — evaluate the configured score expression over the candidate's
                `*_val` rationals.
  6. LOG     — append one JSON record to `Refinement_Log/log.jsonl`.

Per-lemma configuration lives in `lemma.toml` (siblings: seed axioms,
oracles, sink theorem name, score expression, locked search constants).

Usage:
    uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean
    uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean --skip-oracle
    uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean --skip-compile
    uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean --no-log

Optional: a candidate may include a `-- @parent Candidates/Vk.lean` comment
line near the top; the log records this as the edit basis.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
import tomllib
from dataclasses import dataclass, field
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Optional

# --- Layout -----------------------------------------------------------------

ROOT = Path(__file__).resolve().parent
PROJECT_ROOT = ROOT.parent.parent  # grothendieck/
CANDIDATES_DIR = ROOT / "Candidates"
PROOF_DIR = ROOT / "Proof"
NUM_LIB_DIR = ROOT / "Numerical_Library"
LEMMA_TOML = ROOT / "lemma.toml"
LOG_DIR = ROOT / "Refinement_Log"
LOG_FILE = LOG_DIR / "log.jsonl"

# Make Numerical_Library importable (Evaluator.py runs from anywhere).
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

# --- Config -----------------------------------------------------------------


@dataclass
class OracleSpec:
    axiom: str               # short name (namespace-stripped)
    bound_field: str         # `def <bound_field>_val : ℝ` in the candidate
    oracle_fn: str           # attribute name on Numerical_Library
    expected_pattern: str = ""  # optional regex on the Lean axiom type (unused today)


@dataclass
class LemmaConfig:
    name: str
    slug: str
    paper_ref: str
    sink_theorem: str
    score: str
    search_constants: dict[str, str]
    seed_axioms: set[str]
    oracles: dict[str, OracleSpec]   # keyed by short axiom name

    @property
    def search_constants_frac(self) -> dict[str, Fraction]:
        return {k: _parse_fraction(v) for k, v in self.search_constants.items()}


def _parse_fraction(s: str) -> Fraction:
    s = s.strip()
    if "/" in s:
        n, d = s.split("/", 1)
        return Fraction(int(n.strip()), int(d.strip()))
    return Fraction(int(s))


def load_lemma_config(path: Path = LEMMA_TOML) -> LemmaConfig:
    with path.open("rb") as f:
        raw = tomllib.load(f)
    oracles = {
        o["axiom"]: OracleSpec(
            axiom=o["axiom"],
            bound_field=o["bound_field"],
            oracle_fn=o["oracle_fn"],
            expected_pattern=o.get("expected_pattern", ""),
        )
        for o in raw.get("oracles", [])
    }
    return LemmaConfig(
        name=raw.get("name", path.parent.name),
        slug=raw.get("slug", path.parent.name.lower()),
        paper_ref=raw.get("paper_ref", ""),
        sink_theorem=raw["sink_theorem"],
        score=raw["score"],
        search_constants=raw.get("search_constants", {}),
        seed_axioms=set(raw.get("seed_axioms", {}).get("allowed", [])),
        oracles=oracles,
    )


# --- Parsing ----------------------------------------------------------------

DEF_VAL_RE = re.compile(
    r"^\s*def\s+(\w+)\s*:\s*ℝ\s*:=\s*"
    r"(.+?)"
    r"(?=\n\s*(?:def\s+\w+|theorem\b|axiom\b|/-|namespace\b|end\b|private\b|noncomputable\s+def|set_option)|\Z)",
    re.MULTILINE | re.DOTALL,
)
AXIOM_RE = re.compile(r"^\s*axiom\s+(\w+)\b", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$", re.MULTILINE)
PARENT_RE = re.compile(r"^\s*--\s*@parent\s+(\S+)\s*$", re.MULTILINE)


@dataclass
class ParsedCandidate:
    path: Path
    namespace: str
    parent: Optional[str] = None
    def_vals: dict[str, str] = field(default_factory=dict)
    def_vals_eval: dict[str, Fraction] = field(default_factory=dict)
    axioms: list[str] = field(default_factory=list)
    has_theorem: bool = False


def parse_candidate(path: Path, config: LemmaConfig) -> ParsedCandidate:
    src = path.read_text()
    ns_match = NAMESPACE_RE.search(src)
    namespace = ns_match.group(1) if ns_match else "<anonymous>"
    parent_match = PARENT_RE.search(src)
    parent = parent_match.group(1) if parent_match else None
    parsed = ParsedCandidate(path=path, namespace=namespace, parent=parent)
    env = config.search_constants_frac.copy()
    for m in DEF_VAL_RE.finditer(src):
        name, expr = m.group(1), m.group(2).strip().rstrip()
        parsed.def_vals[name] = expr
        try:
            parsed.def_vals_eval[name] = _eval_rational(expr, env)
            env[name] = parsed.def_vals_eval[name]
        except Exception:
            pass  # symbolic; evaluated lazily later
    parsed.axioms = AXIOM_RE.findall(src)
    sink_re = re.compile(rf"theorem\s+{re.escape(config.sink_theorem)}\b")
    parsed.has_theorem = bool(sink_re.search(src))
    return parsed


_RAT_TOKEN = re.compile(r"^\s*(-?\d+)\s*/\s*(\d+)\s*$")


def _eval_rational(expr: str, env: dict[str, Fraction]) -> Fraction:
    """Best-effort eval of a Lean rational expression as a Fraction.

    Handles `<int>`, `<int> / <int>`, references to other defs, and
    arithmetic compositions (`+`, `-`, `*`, `/`, `^`). The `env` dict
    supplies values for symbolic identifiers (search constants and
    previously-evaluated `*_val` defs).
    """
    expr = expr.strip().rstrip()
    m = _RAT_TOKEN.match(expr)
    if m:
        return Fraction(int(m.group(1)), int(m.group(2)))
    if expr in env:
        return env[expr]
    # Substitute env values, normalize Lean syntax to Python.
    py = expr.replace("\n", " ").replace("^", "**")
    # Replace dotted names first (e.g. SearchConfig.r) since `\b` doesn't
    # treat `.` as a word boundary for our purposes.
    for name, val in sorted(env.items(), key=lambda kv: -len(kv[0])):
        if "." in name:
            py = py.replace(name, f"Fraction({val.numerator}, {val.denominator})")
    for name, val in env.items():
        if "." in name:
            continue
        py = re.sub(rf"\b{re.escape(name)}\b", f"Fraction({val.numerator}, {val.denominator})", py)
    py = re.sub(r"\b(\d+)\b", r"Fraction(\1)", py)
    try:
        result = eval(py, {"Fraction": Fraction}, {})
        if isinstance(result, Fraction):
            return result
        return Fraction(result)
    except Exception as e:
        raise ValueError(f"Cannot evaluate {expr!r}: {e}") from e


# --- Compile check ----------------------------------------------------------


def compile_candidate(path: Path) -> tuple[bool, str, float]:
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=600,
        )
    except FileNotFoundError:
        return False, "lake not found on PATH", time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return False, "lake env lean timed out (>10 min)", time.monotonic() - t0
    out = proc.stdout + proc.stderr
    return proc.returncode == 0, out, time.monotonic() - t0


# --- Axiom audit ------------------------------------------------------------


def collect_used_axioms(path: Path, theorem_qual: str) -> tuple[bool, list[str], str, float]:
    """Run `#print axioms <theorem>` in a wrapper file and parse the output."""
    t0 = time.monotonic()
    wrapper = PROJECT_ROOT / ".evaluator_axioms_check.lean"
    rel = path.relative_to(PROJECT_ROOT).with_suffix("")
    module = ".".join(rel.parts)
    wrapper.write_text(f"import {module}\n#print axioms {theorem_qual}\n")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(wrapper)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=120,
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
    names = [s.strip() for s in raw.split(",")]
    return True, names, out, elapsed


def audit_axioms(used: list[str], config: LemmaConfig) -> tuple[bool, list[str], list[dict]]:
    """Categorize each used axiom. Returns (ok, msgs, structured_records)."""
    msgs: list[str] = []
    records: list[dict] = []
    ok = True
    for ax in used:
        if ax == "sorryAx":
            msgs.append(f"  CRIT  {ax} — proof contains `sorry`, hard fail.")
            records.append({"name": ax, "kind": "sorry"})
            ok = False
            continue
        if ax in config.seed_axioms:
            msgs.append(f"  seed  {ax}")
            records.append({"name": ax, "kind": "seed"})
            continue
        short = ax.rsplit(".", 1)[-1]
        if short in config.oracles:
            msgs.append(f"  oracle {ax} (entry: {short})")
            records.append({"name": ax, "kind": "oracle", "short": short})
            continue
        msgs.append(f"  UNREG {ax} — not in seed_axioms.allowed or [[oracles]].")
        records.append({"name": ax, "kind": "unregistered"})
        ok = False
    return ok, msgs, records


# --- Oracle reverification --------------------------------------------------


def _resolve_oracle_fn(fn_name: str) -> Callable[..., Any]:
    import importlib
    mod = importlib.import_module("Numerical_Library")
    return getattr(mod, fn_name)


def verify_oracle_axioms(
    parsed: ParsedCandidate, used: list[str], config: LemmaConfig,
    axiom_records: list[dict],
) -> tuple[bool, list[str], float]:
    t0 = time.monotonic()
    msgs: list[str] = []
    ok = True
    rec_by_name = {r["name"]: r for r in axiom_records}
    for ax in used:
        short = ax.rsplit(".", 1)[-1]
        spec = config.oracles.get(short)
        if not spec:
            continue
        rec = rec_by_name.get(ax, {})
        rec["bound_field"] = spec.bound_field
        rec["oracle_fn"] = spec.oracle_fn
        declared = parsed.def_vals_eval.get(spec.bound_field)
        if declared is None:
            msgs.append(f"  FAIL {ax}: candidate has no `def {spec.bound_field} : ℝ`.")
            rec["status"] = "missing_def"
            ok = False
            continue
        rec["declared"] = f"{declared.numerator}/{declared.denominator}"
        try:
            fn = _resolve_oracle_fn(spec.oracle_fn)
        except Exception as e:
            msgs.append(f"  FAIL {ax}: oracle import failed: {e}")
            rec["status"] = f"import_error: {e}"
            ok = False
            continue
        try:
            result = fn()
        except NotImplementedError as e:
            msgs.append(f"  SKIP {ax}: {e}")
            rec["status"] = "stub"
            continue
        except Exception as e:
            msgs.append(f"  FAIL {ax}: oracle call failed: {e}")
            rec["status"] = f"call_error: {e}"
            ok = False
            continue
        rec["oracle_bound"] = f"{result.bound.numerator}/{result.bound.denominator}"
        if declared >= result.bound:
            msgs.append(f"  pass {ax}: declared {spec.bound_field}={declared} ≥ oracle {result.bound}")
            rec["status"] = "pass"
        else:
            msgs.append(f"  FAIL {ax}: declared {spec.bound_field}={declared} < oracle {result.bound}")
            rec["status"] = "below_oracle"
            ok = False
    return ok, msgs, time.monotonic() - t0


# --- Score ------------------------------------------------------------------


def score_candidate(parsed: ParsedCandidate, config: LemmaConfig) -> Optional[Fraction]:
    """Evaluate the configured score expression as a Fraction.

    Tries (in order):
      1. Direct lookup in `def_vals_eval` (already-evaluated defs).
      2. The simple `_eval_rational` Python expression evaluator
         (handles `+`, `-`, `*`, `/`, `^`, references to other defs).
      3. The production-side symbolic evaluator
         (`proof_graph.cert_compute.evaluate_symbolic`), which
         recognizes `Cr_paper r M (R_val_paper r)` and returns a
         certified arb interval. The arb is converted to a rational
         upper bound via `_arb_to_rational_upper`.

    Step 3 lets a production-faithful candidate (V0) declare
    `def Cr_val : ℝ := Braverman.Paper.Cr_paper SearchConfig.r M_val
    (Braverman.Paper.R_val_paper SearchConfig.r)` and still get a
    rational score for the candidate framework.
    """
    expr = config.score
    if expr in parsed.def_vals_eval:
        return parsed.def_vals_eval[expr]
    raw = parsed.def_vals.get(expr, expr)
    env = config.search_constants_frac.copy()
    env.update(parsed.def_vals_eval)
    try:
        return _eval_rational(raw, env)
    except Exception:
        pass
    # Step 3: fall through to the production symbolic evaluator.
    try:
        import sys as _sys
        from pathlib import Path as _Path
        _proof_graph_dir = _Path(__file__).resolve().parents[2] / "ProofGraph"
        if str(_proof_graph_dir) not in _sys.path:
            _sys.path.insert(0, str(_proof_graph_dir))
        from proof_graph.cert_compute import evaluate_symbolic as _eval_sym
        from proof_graph.oracle import _arb_to_rational_upper as _arb_to_rat
        # Build an env in arb-compatible form (Fraction values, plus the
        # search-constant identifiers that cert_compute expects to see).
        sym_env: dict[str, Fraction] = {}
        sym_env.update(env)
        # cert_compute.evaluate_symbolic expects bare names like `r_val`,
        # `M_val`, etc. without the `Braverman.PaperV0.` namespace prefix
        # and without `Braverman.SearchConfig.` either. Translate the raw
        # expression to remove namespacing.
        raw_clean = (raw
            .replace("Braverman.Paper.", "")
            .replace("Braverman.PaperV0.", "")
            .replace("Braverman.SearchConfig.r", "r_val")
            .replace("Braverman.SearchConfig.eta", "eta_val"))
        # Promote SearchConfig.r → r_val in the env too.
        if "r_val" not in sym_env and Fraction(23, 25) == env.get("SearchConfig.r"):
            sym_env["r_val"] = Fraction(23, 25)
        if "eta_val" not in sym_env and Fraction(1, 100) == env.get("SearchConfig.eta"):
            sym_env["eta_val"] = Fraction(1, 100)
        result = _eval_sym(raw_clean, sym_env, prec=256)
        if result is None:
            return None
        rat_upper = _arb_to_rat(result)
        return rat_upper
    except Exception:
        return None


# --- Log --------------------------------------------------------------------


def _sha256_hex(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def append_log_record(record: dict, path: Path = LOG_FILE) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(record, ensure_ascii=False, separators=(",", ":"))
    with path.open("a", encoding="utf-8") as f:
        f.write(line + "\n")
        f.flush()


def _frac_record(x: Optional[Fraction]) -> Optional[dict]:
    if x is None:
        return None
    return {"numer": x.numerator, "denom": x.denominator, "approx": float(x)}


# --- Main -------------------------------------------------------------------


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--file", required=True, help="Path to Candidates/<name>.lean")
    p.add_argument("--skip-compile", action="store_true")
    p.add_argument("--skip-oracle", action="store_true")
    p.add_argument("--no-log", action="store_true", help="Don't append a refinement-log entry.")
    args = p.parse_args()

    cand_path = Path(args.file).resolve()
    if not cand_path.exists():
        print(f"FAIL: file not found: {cand_path}")
        return 2

    config = load_lemma_config()
    print(f"# {config.name} ({config.paper_ref})")

    timings: dict[str, float] = {}
    record: dict[str, Any] = {
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "lemma": config.slug,
        "candidate": str(cand_path.relative_to(ROOT)) if cand_path.is_relative_to(ROOT) else str(cand_path),
        "candidate_sha256": _sha256_hex(cand_path),
        "parent": None,
        "status": "fail",
        "score_field": config.score,
        "score": None,
        "def_vals": {},
        "axioms_used": [],
        "wall_seconds": timings,
    }

    failure_reason: Optional[str] = None
    failure_tail: Optional[str] = None

    print(f"[1/5] PARSE       {cand_path.name}")
    parsed = parse_candidate(cand_path, config)
    record["parent"] = parsed.parent
    record["def_vals"] = {
        k: f"{v.numerator}/{v.denominator}" for k, v in parsed.def_vals_eval.items()
    }
    print(f"  namespace:    {parsed.namespace}")
    print(f"  parent:       {parsed.parent or '(none)'}")
    print(f"  def *_val:    {len(parsed.def_vals)} ({list(parsed.def_vals)})")
    print(f"  axioms:       {len(parsed.axioms)} ({parsed.axioms})")
    print(f"  sink:         {'found' if parsed.has_theorem else 'MISSING'}")
    if not parsed.has_theorem:
        msg = f"theorem {config.sink_theorem} not found"
        print(f"FAIL: {msg}.")
        failure_reason = msg
        return _finish(record, 2, args.no_log, failure_reason, failure_tail)

    if args.skip_compile:
        print("[2/5] COMPILE     skipped (--skip-compile)")
        used: list[str] = []
        axiom_records: list[dict] = []
    else:
        print("[2/5] COMPILE     lake env lean ...")
        ok, out, elapsed = compile_candidate(cand_path)
        timings["compile"] = round(elapsed, 2)
        if not ok:
            print("FAIL: compilation failed.")
            print(out[-2000:])
            failure_reason = "compile_failed"
            failure_tail = out[-2000:]
            return _finish(record, 2, args.no_log, failure_reason, failure_tail)
        print(f"  pass ({elapsed:.1f}s)")

        theorem_qual = f"{parsed.namespace}.{config.sink_theorem}"
        print(f"[3/5] AXIOM AUDIT #print axioms {theorem_qual}")
        ok, used, out, elapsed = collect_used_axioms(cand_path, theorem_qual)
        timings["axiom_audit"] = round(elapsed, 2)
        if not ok:
            print("FAIL: axiom collection failed.")
            print(out[-2000:])
            failure_reason = "axiom_collection_failed"
            failure_tail = out[-2000:]
            return _finish(record, 2, args.no_log, failure_reason, failure_tail)
        ok2, msgs, axiom_records = audit_axioms(used, config)
        for m in msgs:
            print(m)
        record["axioms_used"] = axiom_records
        if not ok2:
            print("FAIL: unregistered or sorry axioms.")
            failure_reason = "axiom_audit_failed"
            return _finish(record, 2, args.no_log, failure_reason, failure_tail)

    if args.skip_compile or args.skip_oracle:
        print("[4/5] ORACLE     skipped")
    else:
        print("[4/5] ORACLE")
        ok3, msgs2, elapsed = verify_oracle_axioms(parsed, used, config, axiom_records)
        timings["oracle"] = round(elapsed, 2)
        for m in msgs2:
            print(m)
        if not ok3:
            print("FAIL: oracle reverification failed.")
            failure_reason = "oracle_verification_failed"
            return _finish(record, 2, args.no_log, failure_reason, failure_tail)

    print("[5/5] SCORE")
    cr = score_candidate(parsed, config)
    record["score"] = _frac_record(cr)
    if cr is None:
        print(f"  {config.score}: <symbolic, could not evaluate>")
    else:
        print(f"  {config.score}: {cr} ≈ {float(cr):.6f}")

    record["status"] = "ok"
    print("\nPASS")
    return _finish(record, 0, args.no_log, None, None)


def _finish(record: dict, exit_code: int, no_log: bool,
            failure_reason: Optional[str], failure_tail: Optional[str]) -> int:
    if failure_reason is not None:
        record["failure"] = failure_reason
    if failure_tail is not None:
        record["failure_tail"] = failure_tail
    if not no_log:
        append_log_record(record)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
