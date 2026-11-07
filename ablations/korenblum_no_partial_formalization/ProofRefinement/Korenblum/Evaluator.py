#!/usr/bin/env python3
"""
Evaluator.py — rigorous checker + scorer for Korenblum proof candidates.

A candidate is a single Lean file at `Candidates/<name>.lean` that proves the
sink theorem named in `lemma.toml` (today: `korenblum_constant_search`). The
score is the arithmetic expression named in `lemma.toml` (today: `c_value`),
and larger is better.

Pipeline:

  1. PARSE   — extract `def *_val : ℝ := <rat>` and `axiom *` declarations.
  2. COMPILE — `lake env lean <file>` must succeed.
  3. TYPE    — the sink theorem must have the exact contract type
               `ValidKorenblumBound c_value`.
  4. AXIOM   — every `#print axioms <sink>` dependency must be either
               (a) a seed axiom registered in `lemma.toml`, or
               (b) an oracle axiom registered in `lemma.toml`.
               `sorryAx` is a hard fail.
  5. ORACLE  — for each used oracle axiom, recompute the bound via the
               registered `Numerical_Library` function and verify the
               candidate's declared `<bound_field>_val` is at least the
               recomputed bound.
  6. SCORE   — evaluate the configured score expression over the candidate's
               rational `*_val` declarations.
  7. LOG     — append one JSON record to `Refinement_Log/log.jsonl`.

Per-workspace configuration lives in `lemma.toml`.
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
from typing import Any, Optional

ROOT = Path(__file__).resolve().parent
PROJECT_ROOT = ROOT.parent.parent
CANDIDATES_DIR = ROOT / "Candidates"
NUM_LIB_DIR = ROOT / "Numerical_Library"
LEMMA_TOML = ROOT / "lemma.toml"
LOG_DIR = ROOT / "Refinement_Log"
LOG_FILE = LOG_DIR / "log.jsonl"

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


@dataclass
class OracleSpec:
    axiom: str
    bound_field: str
    oracle_fn: str


@dataclass
class WorkspaceConfig:
    name: str
    slug: str
    paper_ref: str
    sink_theorem: str
    score: str
    score_direction: str
    constant_def: str
    search_constants: dict[str, str]
    seed_axioms: set[str]
    oracles: dict[str, OracleSpec]
    allowed_imports_exact: set[str]
    allowed_imports_prefixes: tuple[str, ...]
    workspace_allowed_imports_exact: set[str]
    workspace_allowed_imports_prefixes: tuple[str, ...]

    @property
    def search_constants_frac(self) -> dict[str, Fraction]:
        return {k: _parse_fraction(v) for k, v in self.search_constants.items()}


def _parse_fraction(s: str) -> Fraction:
    s = s.strip()
    if "/" in s:
        n, d = s.split("/", 1)
        return Fraction(int(n.strip()), int(d.strip()))
    return Fraction(int(s))


def load_workspace_config(path: Path = LEMMA_TOML) -> WorkspaceConfig:
    with path.open("rb") as f:
        raw = tomllib.load(f)
    oracles = {
        o["axiom"]: OracleSpec(
            axiom=o["axiom"],
            bound_field=o["bound_field"],
            oracle_fn=o["oracle_fn"],
        )
        for o in raw.get("oracles", [])
    }
    return WorkspaceConfig(
        name=raw.get("name", path.parent.name),
        slug=raw.get("slug", path.parent.name.lower()),
        paper_ref=raw.get("paper_ref", ""),
        sink_theorem=raw["sink_theorem"],
        score=raw["score"],
        score_direction=raw.get("score_direction", "maximize"),
        constant_def=raw.get("constant_def", "c_value"),
        search_constants=raw.get("search_constants", {}),
        seed_axioms=set(raw.get("seed_axioms", {}).get("allowed", [])),
        oracles=oracles,
        allowed_imports_exact=set(raw.get("import_policy", {}).get("allowed_exact", [])),
        allowed_imports_prefixes=tuple(raw.get("import_policy", {}).get("allowed_prefixes", [])),
        workspace_allowed_imports_exact=set(raw.get("workspace_import_policy", {}).get("allowed_exact", [])),
        workspace_allowed_imports_prefixes=tuple(raw.get("workspace_import_policy", {}).get("allowed_prefixes", [])),
    )


DEF_VAL_RE = re.compile(
    r"^\s*def\s+(\w+)\s*:\s*ℝ\s*:=\s*"
    r"(.+?)"
    r"(?=\n\s*(?:def\s+\w+|theorem\b|axiom\b|/-|namespace\b|end\b|private\b|noncomputable\s+def|set_option)|\Z)",
    re.MULTILINE | re.DOTALL,
)
AXIOM_RE = re.compile(r"^\s*axiom\s+(\w+)\b", re.MULTILINE)
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$", re.MULTILINE)
PARENT_RE = re.compile(r"^\s*--\s*@parent\s+(\S+)\s*$", re.MULTILINE)
_RAT_TOKEN = re.compile(r"^\s*(-?\d+)\s*/\s*(\d+)\s*$")


@dataclass
class ParsedCandidate:
    path: Path
    namespace: str
    parent: Optional[str] = None
    def_vals: dict[str, str] = field(default_factory=dict)
    def_vals_eval: dict[str, Fraction] = field(default_factory=dict)
    axioms: list[str] = field(default_factory=list)
    imports: list[str] = field(default_factory=list)
    has_theorem: bool = False


def parse_imports_from_text(src: str) -> list[str]:
    imports: list[str] = []
    for m in IMPORT_RE.finditer(src):
        line = m.group(1).split("--", 1)[0]
        imports.extend(token for token in line.split() if token)
    return imports


def _eval_rational(expr: str, env: dict[str, Fraction]) -> Fraction:
    expr = expr.strip().rstrip()
    m = _RAT_TOKEN.match(expr)
    if m:
        return Fraction(int(m.group(1)), int(m.group(2)))
    if expr in env:
        return env[expr]
    py = expr.replace("\n", " ").replace("^", "**")
    for name, val in sorted(env.items(), key=lambda kv: -len(kv[0])):
        py = re.sub(
            rf"\b{re.escape(name)}\b",
            f"Fraction({val.numerator}, {val.denominator})",
            py,
        )
    py = re.sub(r"\b(\d+)\b", r"Fraction(\1)", py)
    result = eval(py, {"Fraction": Fraction}, {})
    if isinstance(result, Fraction):
        return result
    return Fraction(result)


def parse_candidate(path: Path, config: WorkspaceConfig) -> ParsedCandidate:
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
            pass
    parsed.axioms = AXIOM_RE.findall(src)
    parsed.imports = parse_imports_from_text(src)
    sink_re = re.compile(rf"theorem\s+{re.escape(config.sink_theorem)}\b")
    parsed.has_theorem = bool(sink_re.search(src))
    return parsed


def audit_module_imports(
    imports: list[str],
    *,
    allowed_exact: set[str],
    allowed_prefixes: tuple[str, ...],
) -> tuple[bool, list[str], list[dict[str, str]]]:
    if not allowed_exact and not allowed_prefixes:
        return True, [], []

    msgs: list[str] = []
    records: list[dict[str, str]] = []
    ok = True
    for mod in imports:
        allowed = mod in allowed_exact or any(
            mod == prefix or mod.startswith(prefix + ".")
            for prefix in allowed_prefixes
        )
        if allowed:
            msgs.append(f"  allow {mod}")
            records.append({"module": mod, "kind": "allowed"})
            continue
        msgs.append(f"  BLOCK {mod} — not allowed by import_policy.")
        records.append({"module": mod, "kind": "blocked"})
        ok = False
    return ok, msgs, records


def audit_imports(parsed: ParsedCandidate, config: WorkspaceConfig) -> tuple[bool, list[str], list[dict[str, str]]]:
    return audit_module_imports(
        parsed.imports,
        allowed_exact=config.allowed_imports_exact,
        allowed_prefixes=config.allowed_imports_prefixes,
    )


def audit_workspace_imports(config: WorkspaceConfig) -> tuple[bool, list[str], list[dict[str, str]]]:
    msgs: list[str] = []
    records: list[dict[str, str]] = []
    ok = True
    for lean_file in sorted(ROOT.rglob("*.lean")):
        rel = lean_file.relative_to(ROOT)
        file_ok, file_msgs, file_records = audit_module_imports(
            parse_imports_from_text(lean_file.read_text()),
            allowed_exact=config.workspace_allowed_imports_exact,
            allowed_prefixes=config.workspace_allowed_imports_prefixes,
        )
        for msg in file_msgs:
            msgs.append(f"  {rel}: {msg.strip()}")
        for rec in file_records:
            records.append({"file": str(rel), **rec})
        ok = ok and file_ok
    return ok, msgs, records


def module_name_for_path(path: Path) -> str:
    rel = path.relative_to(PROJECT_ROOT).with_suffix("")
    return ".".join(rel.parts)


def compile_candidate(path: Path) -> tuple[bool, str, float]:
    t0 = time.monotonic()
    module = module_name_for_path(path)
    proc = subprocess.run(
        ["lake", "build", module],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
    )
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "error:" not in out and "declaration uses 'sorry'" not in out
    return ok, out, time.monotonic() - t0


def theorem_type_check(path: Path, parsed: ParsedCandidate, config: WorkspaceConfig) -> tuple[bool, str, float]:
    t0 = time.monotonic()
    module = module_name_for_path(path)
    theorem_qual = f"{parsed.namespace}.{config.sink_theorem}"
    c_qual = f"{parsed.namespace}.{config.constant_def}"
    wrapper = PROJECT_ROOT / ".korenblum_evaluator_typecheck.lean"
    wrapper.write_text(
        "\n".join(
            [
                f"import {module}",
                "import ProofRefinement.Korenblum.Proof.CandidateContract",
                "",
                f"#check (@{theorem_qual} : ProofRefinement.Korenblum.ValidKorenblumBound {c_qual})",
                "",
            ]
        )
    )
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
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "error:" not in out
    return ok, out, time.monotonic() - t0


def collect_used_axioms(path: Path, theorem_qual: str) -> tuple[bool, list[str], str, float]:
    t0 = time.monotonic()
    wrapper = PROJECT_ROOT / ".korenblum_axioms_check.lean"
    module = module_name_for_path(path)
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
    names = [s.strip() for s in raw.split(",") if s.strip()]
    return True, names, out, elapsed


def audit_axioms(used: list[str], config: WorkspaceConfig) -> tuple[bool, list[str], list[dict]]:
    msgs: list[str] = []
    records: list[dict] = []
    ok = True
    for ax in used:
        short = ax.rsplit(".", 1)[-1]
        if ax == "sorryAx":
            msgs.append(f"  CRIT  {ax} — proof contains `sorry`, hard fail.")
            records.append({"name": ax, "kind": "sorry"})
            ok = False
            continue
        if ax in config.seed_axioms or short in config.seed_axioms:
            msgs.append(f"  seed  {ax}")
            records.append({"name": ax, "kind": "seed"})
            continue
        if short in config.oracles or ax in config.oracles:
            msgs.append(f"  oracle {ax}")
            records.append({"name": ax, "kind": "oracle"})
            continue
        msgs.append(f"  UNREG {ax} — not in seed_axioms.allowed or [[oracles]].")
        records.append({"name": ax, "kind": "unregistered"})
        ok = False
    return ok, msgs, records


def _coerce_fraction(value: Any) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if hasattr(value, "bound"):
        value = value.bound
    if isinstance(value, dict):
        if "bound" in value:
            value = value["bound"]
        elif "num" in value and "den" in value:
            return Fraction(int(value["num"]), int(value["den"]))
    if hasattr(value, "to_fraction"):
        value = value.to_fraction()
        if isinstance(value, Fraction):
            return value
    if hasattr(value, "num") and hasattr(value, "den"):
        return Fraction(int(value.num), int(value.den))
    if isinstance(value, (int, str)):
        return _parse_fraction(str(value))
    raise TypeError(f"unsupported oracle return value: {type(value).__name__}")


def _resolve_oracle_fn(fn_name: str):
    import importlib

    if "." not in fn_name:
        numlib = importlib.import_module("Numerical_Library")
        return getattr(numlib, fn_name)

    module_name, attr_name = fn_name.rsplit(".", 1)
    module = importlib.import_module(f"Numerical_Library.{module_name}")
    return getattr(module, attr_name)


def run_oracle_checks(parsed: ParsedCandidate, used_axioms: list[str], config: WorkspaceConfig) -> tuple[bool, list[str], list[dict]]:
    msgs: list[str] = []
    records: list[dict] = []
    needed = {ax.rsplit(".", 1)[-1] for ax in used_axioms if ax.rsplit(".", 1)[-1] in config.oracles}
    if not needed:
        return True, msgs, records
    ok = True
    for short in sorted(needed):
        spec = config.oracles[short]
        if spec.bound_field not in parsed.def_vals_eval:
            msgs.append(f"  FAIL  missing `def {spec.bound_field} : ℝ := ...`")
            records.append({"axiom": short, "result": "missing-bound-field"})
            ok = False
            continue
        try:
            fn = _resolve_oracle_fn(spec.oracle_fn)
        except Exception as e:
            msgs.append(f"  FAIL  oracle function `{spec.oracle_fn}` not found: {e}")
            records.append(
                {
                    "axiom": short,
                    "result": "missing-oracle-fn",
                    "error": f"{type(e).__name__}: {e}",
                }
            )
            ok = False
            continue
        try:
            result = fn()
            bound = _coerce_fraction(result)
        except Exception as e:
            msgs.append(f"  FAIL  oracle `{spec.oracle_fn}` raised {type(e).__name__}: {e}")
            records.append({"axiom": short, "result": "oracle-error", "error": f"{type(e).__name__}: {e}"})
            ok = False
            continue
        declared = parsed.def_vals_eval[spec.bound_field]
        this_ok = bound <= declared
        msgs.append(
            f"  {'PASS' if this_ok else 'FAIL'}  {short}: oracle={bound} declared={declared}"
        )
        records.append(
            {
                "axiom": short,
                "bound_field": spec.bound_field,
                "oracle_bound": str(bound),
                "declared": str(declared),
                "ok": this_ok,
            }
        )
        ok = ok and this_ok
    return ok, msgs, records


def eval_score(parsed: ParsedCandidate, config: WorkspaceConfig) -> Fraction:
    env = config.search_constants_frac.copy()
    env.update(parsed.def_vals_eval)
    return _eval_rational(config.score, env)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def append_log(record: dict[str, Any], path: Path = LOG_FILE) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as f:
        json.dump(record, f, sort_keys=True)
        f.write("\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", required=True)
    parser.add_argument("--skip-compile", action="store_true")
    parser.add_argument("--skip-oracle", action="store_true")
    parser.add_argument("--no-log", action="store_true")
    args = parser.parse_args()

    config = load_workspace_config()
    path = Path(args.file)
    if not path.is_absolute():
        path = (PROJECT_ROOT / path).resolve()
    parsed = parse_candidate(path, config)

    record: dict[str, Any] = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "workspace": config.slug,
        "candidate": str(path.relative_to(ROOT)),
        "namespace": parsed.namespace,
        "parent": parsed.parent,
        "sha256": sha256_file(path),
        "score_direction": config.score_direction,
        "score_expr": config.score,
        "pass": False,
    }

    print(f"candidate:     {path.relative_to(PROJECT_ROOT)}")
    print(f"namespace:     {parsed.namespace}")
    print(f"parent:        {parsed.parent or '(none)'}")

    ok, msgs, records = audit_workspace_imports(config)
    print(f"workspace imports: {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["workspace_imports"] = records
    if not ok:
        record["reason"] = "disallowed workspace import"
        if not args.no_log:
            append_log(record)
        raise SystemExit(1)

    ok, msgs, records = audit_imports(parsed, config)
    print(f"import audit:  {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["imports"] = records
    if not ok:
        record["reason"] = "disallowed import"
        if not args.no_log:
            append_log(record)
        raise SystemExit(1)

    if not parsed.has_theorem:
        msg = f"theorem {config.sink_theorem} not found"
        print(msg)
        record["reason"] = msg
        if not args.no_log:
            append_log(record)
        raise SystemExit(1)

    if config.constant_def not in parsed.def_vals_eval:
        msg = f"`def {config.constant_def} : ℝ := ...` not found or not rational"
        print(msg)
        record["reason"] = msg
        if not args.no_log:
            append_log(record)
        raise SystemExit(1)

    if not args.skip_compile:
        ok, out, elapsed = compile_candidate(path)
        print(f"compile:       {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
        record["compile_elapsed_s"] = round(elapsed, 3)
        if not ok:
            record["reason"] = "compile failed"
            record["compile_output"] = out[-4000:]
            if not args.no_log:
                append_log(record)
            print(out[-4000:])
            raise SystemExit(1)

    ok, out, elapsed = theorem_type_check(path, parsed, config)
    print(f"type-check:    {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
    record["typecheck_elapsed_s"] = round(elapsed, 3)
    if not ok:
        record["reason"] = "contract type check failed"
        record["typecheck_output"] = out[-4000:]
        if not args.no_log:
            append_log(record)
        print(out[-4000:])
        raise SystemExit(1)

    theorem_qual = f"{parsed.namespace}.{config.sink_theorem}"
    ok, used_axioms, out, elapsed = collect_used_axioms(path, theorem_qual)
    print(f"axiom scan:    {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
    record["axiom_scan_elapsed_s"] = round(elapsed, 3)
    if not ok:
        record["reason"] = "axiom scan failed"
        record["axiom_scan_output"] = out[-4000:]
        if not args.no_log:
            append_log(record)
        print(out[-4000:])
        raise SystemExit(1)

    ok, msgs, records = audit_axioms(used_axioms, config)
    print(f"axiom audit:   {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["axioms_used"] = records
    if not ok:
        record["reason"] = "unregistered axiom"
        if not args.no_log:
            append_log(record)
        raise SystemExit(1)

    if not args.skip_oracle:
        ok, msgs, oracle_records = run_oracle_checks(parsed, used_axioms, config)
        print(f"oracle audit:  {'PASS' if ok else 'FAIL'}")
        for msg in msgs:
            print(msg)
        record["oracle_checks"] = oracle_records
        if not ok:
            record["reason"] = "oracle check failed"
            if not args.no_log:
                append_log(record)
            raise SystemExit(1)

    score = eval_score(parsed, config)
    record["score"] = str(score)
    record["def_vals"] = {k: str(v) for k, v in parsed.def_vals_eval.items()}
    record["pass"] = True

    print(f"score ({config.score_direction}): {score}")

    if not args.no_log:
        append_log(record)

    print("status: PASS")


if __name__ == "__main__":
    main()
