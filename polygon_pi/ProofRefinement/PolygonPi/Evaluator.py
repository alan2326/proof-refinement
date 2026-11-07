#!/usr/bin/env python3
"""
Evaluator.py — rigorous checker + scorer for Polygon-π proof candidates.

A candidate is a single Lean file at `Candidates/<name>.lean` declaring two
rational constants and proving the sink theorem named in `lemma.toml`:

    def lambda : ℝ := <rational>
    def kappa  : ℝ := <rational>
    theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa

The score is `kappa - lambda`, the width coefficient of the certified interval,
and **smaller is better**.

Ported from the Korenblum evaluator, keeping its CLI, its rational-parsing and
`-- @parent` conventions, and its append-only `log.jsonl` behaviour. The
substantive differences all follow from decision D3 (pure Lean, no oracles):

  * there is no oracle stage, and it is a hard error for `lemma.toml` to declare
    one;
  * the axiom closure must be a *subset of the three standard Lean axioms*, so
    `native_decide` is banned automatically;
  * imports are audited transitively, not just directly;
  * a static forbidden-pattern scan blocks Mathlib's finished π-bound lemmas.

Stage order (fail-closed — the first failure stops the run and is logged):

   1. workspace import audit          7. exact contract type check
   2. candidate import audit          8. optional secondary contract
   3. transitive import closure       9. axiom closure audit
   4. static pattern + size scan     10. oracle-table assertion
   5. declaration presence + sanity  11. score + incumbent comparison
   6. compile                        12. log append
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import shutil
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
LEMMA_TOML = ROOT / "lemma.toml"
LOG_DIR = ROOT / "Refinement_Log"
LOG_FILE = LOG_DIR / "log.jsonl"
CLOSURE_SCRIPT = ROOT / "scripts" / "polygonpi_import_closure.py"

COMPILE_TIMEOUT_S = 600
LEAN_TIMEOUT_S = 180


# ── shared import parsing (loaded from the closure script, single source of truth)

def _load_closure_module():
    spec = importlib.util.spec_from_file_location("polygonpi_import_closure", CLOSURE_SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CLOSURE_SCRIPT}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_closure = _load_closure_module()
strip_comments = _closure.strip_comments
parse_imports_from_text = _closure.parse_imports
ModuleResolver = _closure.ModuleResolver
import_closure = _closure.closure
is_blocked_module = _closure.is_blocked


# ── configuration ────────────────────────────────────────────────────────────

@dataclass
class ImportPolicy:
    allowed_exact: set[str]
    allowed_prefixes: tuple[str, ...]
    blocked_exact: set[str]
    blocked_prefixes: tuple[str, ...]
    check_transitive: bool

    @classmethod
    def from_raw(cls, raw: dict) -> "ImportPolicy":
        return cls(
            allowed_exact=set(raw.get("allowed_exact", [])),
            allowed_prefixes=tuple(raw.get("allowed_prefixes", [])),
            blocked_exact=set(raw.get("blocked_exact", [])),
            blocked_prefixes=tuple(raw.get("blocked_prefixes", [])),
            check_transitive=bool(raw.get("check_transitive", False)),
        )


@dataclass
class WorkspaceConfig:
    name: str
    slug: str
    paper_ref: str
    sink_theorem: str
    score: str
    score_direction: str
    constant_def: str
    lower_constant_def: str
    contract_def: str
    contract_namespace: str
    contract_module: str
    fixed_depth_theorem: str
    secondary_sink_theorem: str
    secondary_constant_def: str
    secondary_lower_constant_def: str
    secondary_score: str
    secondary_contract_def: str
    secondary_depth: int
    benchmark_depth: int
    seed_axioms: set[str]
    candidate_policy: ImportPolicy
    workspace_policy: ImportPolicy
    forbidden_tokens: tuple[str, ...]
    max_lines_per_file: int
    max_bytes_per_file: int
    max_constant_digits: int
    oracles_declared: int


def load_workspace_config(path: Path = LEMMA_TOML) -> WorkspaceConfig:
    with path.open("rb") as f:
        raw = tomllib.load(f)
    limits = raw.get("limits", {})
    return WorkspaceConfig(
        name=raw.get("name", path.parent.name),
        slug=raw.get("slug", path.parent.name.lower()),
        paper_ref=raw.get("paper_ref", ""),
        sink_theorem=raw["sink_theorem"],
        score=raw["score"],
        score_direction=raw.get("score_direction", "minimize"),
        constant_def=raw.get("constant_def", "kappa"),
        lower_constant_def=raw.get("lower_constant_def", "lambda"),
        contract_def=raw.get("contract_def", "ValidPolygonBound"),
        contract_namespace=raw.get("contract_namespace", "ProofRefinement.PolygonPi"),
        contract_module=raw.get("contract_module", "ProofRefinement.PolygonPi.Proof.Main"),
        fixed_depth_theorem=raw.get("fixed_depth_theorem", "certified_polygon_interval"),
        secondary_sink_theorem=raw.get("secondary_sink_theorem", ""),
        secondary_constant_def=raw.get("secondary_constant_def", ""),
        secondary_lower_constant_def=raw.get("secondary_lower_constant_def", ""),
        secondary_score=raw.get("secondary_score", ""),
        secondary_contract_def=raw.get("secondary_contract_def", "ValidPolygonBoundAt"),
        secondary_depth=int(raw.get("secondary_depth", 10)),
        benchmark_depth=int(raw.get("benchmark_depth", 10)),
        seed_axioms=set(raw.get("seed_axioms", {}).get("allowed", [])),
        candidate_policy=ImportPolicy.from_raw(raw.get("import_policy", {})),
        workspace_policy=ImportPolicy.from_raw(raw.get("workspace_import_policy", {})),
        forbidden_tokens=tuple(raw.get("forbidden_patterns", {}).get("tokens", [])),
        max_lines_per_file=int(limits.get("max_lines_per_file", 2000)),
        max_bytes_per_file=int(limits.get("max_bytes_per_file", 102400)),
        max_constant_digits=int(limits.get("max_constant_digits", 30)),
        oracles_declared=len(raw.get("oracles", [])),
    )


# ── parsing ──────────────────────────────────────────────────────────────────

# A scored constant must be a single-line real-valued `def`, e.g.
# `def kappa : ℝ := 3233 / 10000`. Capturing to end-of-line rather than
# scanning forward for the next declaration keeps this immune to whatever
# follows — the Korenblum-style lookahead silently ran away when the next
# declaration carried a modifier such as `private lemma`.
DEF_VAL_RE = re.compile(
    r"^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*"
    r"def[ \t]+(\w+)[ \t]*:[ \t]*ℝ[ \t]*:=[ \t]*(\S.*?)[ \t]*$",
    re.MULTILINE,
)
AXIOM_RE = re.compile(r"^\s*axiom\s+(\w+)\b", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$", re.MULTILINE)
PARENT_RE = re.compile(r"^\s*--\s*@parent\s+(\S+)\s*$", re.MULTILINE)
_RAT_TOKEN = re.compile(r"^\s*(-?\d+)\s*/\s*(\d+)\s*$")


def _parse_fraction(s: str) -> Fraction:
    s = s.strip()
    if "/" in s:
        n, d = s.split("/", 1)
        return Fraction(int(n.strip()), int(d.strip()))
    return Fraction(int(s))


def _eval_rational(expr: str, env: dict[str, Fraction]) -> Fraction:
    """Evaluate a rational-valued Lean expression exactly.

    Handles bare literals, `p / q`, references to previously-parsed constants,
    and arithmetic combinations of those (so `score = "kappa - lambda"` and a
    candidate writing `def kappa : ℝ := 3 * 7 / 64` both work)."""
    expr = expr.strip().rstrip()
    m = _RAT_TOKEN.match(expr)
    if m:
        return Fraction(int(m.group(1)), int(m.group(2)))
    if expr in env:
        return env[expr]
    py = expr.replace("\n", " ").replace("^", "**")
    if not re.fullmatch(r"[\w\s.+\-*/()**]*", py):
        raise ValueError(f"non-arithmetic characters in {expr!r}")
    for name, val in sorted(env.items(), key=lambda kv: -len(kv[0])):
        py = re.sub(
            rf"\b{re.escape(name)}\b",
            f"Fraction({val.numerator}, {val.denominator})",
            py,
        )
    py = re.sub(r"\b(\d+)\b", r"Fraction(\1)", py)
    result = eval(py, {"__builtins__": {}, "Fraction": Fraction}, {})
    if isinstance(result, Fraction):
        return result
    return Fraction(result)


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
    has_secondary: bool = False
    def_counts: dict[str, int] = field(default_factory=dict)


def parse_candidate(path: Path, config: WorkspaceConfig) -> ParsedCandidate:
    src = path.read_text()
    code = strip_comments(src)
    ns_match = NAMESPACE_RE.search(code)
    namespace = ns_match.group(1) if ns_match else "<anonymous>"
    parent_match = PARENT_RE.search(src)  # `-- @parent` lives in a comment
    parsed = ParsedCandidate(path=path, namespace=namespace, parent=parent_match.group(1) if parent_match else None)
    env: dict[str, Fraction] = {}
    for m in DEF_VAL_RE.finditer(code):
        name, expr = m.group(1), m.group(2).strip().rstrip()
        parsed.def_counts[name] = parsed.def_counts.get(name, 0) + 1
        parsed.def_vals[name] = expr
        try:
            parsed.def_vals_eval[name] = _eval_rational(expr, env)
            env[name] = parsed.def_vals_eval[name]
        except Exception:
            pass
    parsed.axioms = AXIOM_RE.findall(code)
    parsed.imports = parse_imports_from_text(src)
    parsed.has_theorem = bool(re.search(rf"theorem\s+{re.escape(config.sink_theorem)}\b", code))
    if config.secondary_sink_theorem:
        parsed.has_secondary = bool(
            re.search(rf"theorem\s+{re.escape(config.secondary_sink_theorem)}\b", code)
        )
    return parsed


# ── stage 1 & 2: import policy ───────────────────────────────────────────────

def audit_module_imports(imports: list[str], policy: ImportPolicy):
    msgs: list[str] = []
    records: list[dict[str, str]] = []
    ok = True
    for mod in imports:
        if mod in policy.blocked_exact or any(
            mod == p or mod.startswith(p + ".") for p in policy.blocked_prefixes
        ):
            msgs.append(f"  BLOCK {mod} — explicitly blocked by policy.")
            records.append({"module": mod, "kind": "blocked"})
            ok = False
            continue
        allowed = (
            not policy.allowed_exact and not policy.allowed_prefixes
        ) or mod in policy.allowed_exact or any(
            mod == p or mod.startswith(p + ".") for p in policy.allowed_prefixes
        )
        if allowed:
            records.append({"module": mod, "kind": "allowed"})
            continue
        msgs.append(f"  BLOCK {mod} — not allowed by policy.")
        records.append({"module": mod, "kind": "not-allowed"})
        ok = False
    return ok, msgs, records


def audit_workspace_imports(config: WorkspaceConfig):
    msgs: list[str] = []
    records: list[dict[str, str]] = []
    ok = True
    scanned = 0
    for lean_file in sorted(ROOT.rglob("*.lean")):
        scanned += 1
        rel = lean_file.relative_to(ROOT)
        file_ok, file_msgs, file_records = audit_module_imports(
            parse_imports_from_text(lean_file.read_text()), config.workspace_policy
        )
        for msg in file_msgs:
            msgs.append(f"  {rel}: {msg.strip()}")
        for rec in file_records:
            if rec["kind"] != "allowed":
                records.append({"file": str(rel), **rec})
        ok = ok and file_ok
    return ok, msgs, records, scanned


# ── stage 3: transitive closure ──────────────────────────────────────────────

def audit_import_closure(modules: list[str], policy: ImportPolicy):
    resolver = ModuleResolver(PROJECT_ROOT)
    seen, unresolved = import_closure(modules, resolver)
    hits = sorted(
        m for m in (seen | unresolved)
        if is_blocked_module(m, policy.blocked_exact, policy.blocked_prefixes)
    )
    return (not hits), hits, len(seen), sorted(unresolved)


# ── stage 4: static scan ─────────────────────────────────────────────────────

def scan_files_for_candidate(path: Path) -> list[Path]:
    """The candidate plus any per-candidate derived-theorem files."""
    files = [path]
    derived_dir = path.with_suffix("")
    if derived_dir.is_dir():
        files.extend(sorted(derived_dir.rglob("*.lean")))
    return files


def static_scan(path: Path, config: WorkspaceConfig):
    msgs: list[str] = []
    records: list[dict[str, Any]] = []
    ok = True
    for f in scan_files_for_candidate(path):
        rel = f.relative_to(ROOT)
        raw = f.read_text()
        code = strip_comments(raw)
        nbytes = len(raw.encode())
        nlines = raw.count("\n") + 1
        if nlines > config.max_lines_per_file:
            msgs.append(f"  BLOCK {rel}: {nlines} lines > {config.max_lines_per_file}")
            records.append({"file": str(rel), "kind": "too-many-lines", "value": nlines})
            ok = False
        if nbytes > config.max_bytes_per_file:
            msgs.append(f"  BLOCK {rel}: {nbytes} bytes > {config.max_bytes_per_file}")
            records.append({"file": str(rel), "kind": "too-many-bytes", "value": nbytes})
            ok = False
        for token in config.forbidden_tokens:
            if token in code:
                line_no = next(
                    (i + 1 for i, line in enumerate(code.splitlines()) if token in line), 0
                )
                msgs.append(f"  BLOCK {rel}:{line_no}: forbidden token {token!r}")
                records.append({"file": str(rel), "kind": "forbidden-token", "token": token, "line": line_no})
                ok = False
    return ok, msgs, records


def check_constant_digits(value: Fraction, name: str, config: WorkspaceConfig):
    n_digits = len(str(abs(value.numerator)))
    d_digits = len(str(value.denominator))
    if max(n_digits, d_digits) > config.max_constant_digits:
        return False, (
            f"  BLOCK {name} = {value}: {max(n_digits, d_digits)} digits > "
            f"{config.max_constant_digits}"
        )
    return True, ""


# ── stage 6: compile ─────────────────────────────────────────────────────────

def module_name_for_path(path: Path) -> str:
    rel = path.relative_to(PROJECT_ROOT).with_suffix("")
    return ".".join(rel.parts)


_TIME_RE = {
    "max_rss_kb": re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)"),
    "user_cpu_s": re.compile(r"User time \(seconds\):\s*([\d.]+)"),
    "sys_cpu_s": re.compile(r"System time \(seconds\):\s*([\d.]+)"),
}


def compile_candidate(path: Path) -> tuple[bool, str, float, dict[str, float]]:
    t0 = time.monotonic()
    module = module_name_for_path(path)
    cmd = ["lake", "build", module]
    if shutil.which("/usr/bin/time"):
        cmd = ["/usr/bin/time", "-v"] + cmd
    proc = subprocess.run(
        cmd, cwd=PROJECT_ROOT, capture_output=True, text=True, timeout=COMPILE_TIMEOUT_S
    )
    out = proc.stdout + proc.stderr
    metrics: dict[str, float] = {}
    for key, rx in _TIME_RE.items():
        m = rx.search(proc.stderr)
        if m:
            metrics[key] = float(m.group(1))
    ok = (
        proc.returncode == 0
        and "error:" not in out
        and "declaration uses 'sorry'" not in out
    )
    return ok, out, time.monotonic() - t0, metrics


# ── stages 7 & 8: type checks ────────────────────────────────────────────────

def _run_lean_snippet(body: str, tag: str) -> tuple[bool, str, float]:
    t0 = time.monotonic()
    wrapper = PROJECT_ROOT / f".polygonpi_{tag}.lean"
    wrapper.write_text(body)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(wrapper)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=LEAN_TIMEOUT_S,
        )
    finally:
        wrapper.unlink(missing_ok=True)
    out = proc.stdout + proc.stderr
    return (proc.returncode == 0 and "error:" not in out), out, time.monotonic() - t0


def theorem_type_check(path: Path, parsed: ParsedCandidate, config: WorkspaceConfig):
    """Stage 7. Two obligations:

    (a) the sink theorem has *exactly* the contract type at the declared
        constants — not a weaker or differently-shaped statement;
    (b) the trusted fixed-depth corollary applies to it, so the interval the
        artifact reports really does follow from this candidate;
    (c) the constants Lean actually used equal the rationals this script parsed
        and will score.

    (c) is not paranoia. Without it, the textual parse and Lean's own name
    resolution can disagree: `DEF_VAL_RE` matches `def kappa : ℝ := …` anywhere
    in the file with last-match-wins, while Lean resolves `<namespace>.kappa`.
    A candidate could prove the bound at `kappa = 1` and append a shadowing
    `def kappa : ℝ := 1/1000` in a trailing namespace — every other stage passes
    and the score is taken from the decoy. Asking Lean to confirm
    `<ns>.kappa = <parsed value>` by `norm_num` makes text and proof provably the
    same number, which closes that class of divergence outright.
    """
    module = module_name_for_path(path)
    ns = parsed.namespace
    thm = f"{ns}.{config.sink_theorem}"
    kap = f"{ns}.{config.constant_def}"
    lam = f"{ns}.{config.lower_constant_def}"
    contract = f"{config.contract_namespace}.{config.contract_def}"
    fixed = f"{config.contract_namespace}.{config.fixed_depth_theorem}"

    def value_check(qual: str, value: Fraction) -> str:
        return (
            f"example : ({qual} : ℝ) = "
            f"({value.numerator} : ℝ) / ({value.denominator} : ℝ) := by "
            f"norm_num [{qual}]"
        )

    lines = [
        f"import {module}",
        f"import {config.contract_module}",
        "",
        f"#check (@{thm} : {contract} {lam} {kap})",
        f"#check ({fixed} (@{thm}))",
    ]
    for name, qual in ((config.constant_def, kap), (config.lower_constant_def, lam)):
        if name in parsed.def_vals_eval:
            lines.append(value_check(qual, parsed.def_vals_eval[name]))
    lines.append("")
    return _run_lean_snippet("\n".join(lines), "evaluator_typecheck")


def secondary_type_check(path: Path, parsed: ParsedCandidate, config: WorkspaceConfig):
    """Stage 8. Optional; absent declarations are skipped, not failed."""
    module = module_name_for_path(path)
    ns = parsed.namespace
    thm = f"{ns}.{config.secondary_sink_theorem}"
    kap = f"{ns}.{config.secondary_constant_def}"
    lam = f"{ns}.{config.secondary_lower_constant_def}"
    contract = f"{config.contract_namespace}.{config.secondary_contract_def}"
    body = "\n".join(
        [
            f"import {module}",
            f"import {config.contract_module}",
            "",
            f"#check (@{thm} : {contract} {config.secondary_depth} {lam} {kap})",
            "",
        ]
    )
    return _run_lean_snippet(body, "evaluator_secondary")


# ── stage 9: axioms ──────────────────────────────────────────────────────────

def collect_used_axioms(path: Path, theorem_qual: str):
    module = module_name_for_path(path)
    body = f"import {module}\n#print axioms {theorem_qual}\n"
    ok, out, elapsed = _run_lean_snippet(body, "axioms_check")
    if not ok:
        return False, [], out, elapsed
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", out, re.DOTALL)
    if not m:
        # `#print axioms` prints this when the closure is empty.
        if "does not depend on any axioms" in out:
            return True, [], out, elapsed
        return False, [], out, elapsed
    names = [s.strip() for s in m.group(1).replace("\n", " ").split(",") if s.strip()]
    return True, names, out, elapsed


HARD_FAIL_AXIOMS = {"sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"}


def audit_axioms(used: list[str], config: WorkspaceConfig):
    msgs: list[str] = []
    records: list[dict] = []
    ok = True
    for ax in used:
        short = ax.rsplit(".", 1)[-1]
        if ax in HARD_FAIL_AXIOMS or short in HARD_FAIL_AXIOMS:
            why = "proof contains `sorry`" if short == "sorryAx" else "compiler/native trust"
            msgs.append(f"  CRIT  {ax} — {why}, hard fail.")
            records.append({"name": ax, "kind": "hard-fail"})
            ok = False
            continue
        if ax in config.seed_axioms or short in config.seed_axioms:
            msgs.append(f"  std   {ax}")
            records.append({"name": ax, "kind": "standard"})
            continue
        msgs.append(f"  UNREG {ax} — not one of the three standard Lean axioms (D3).")
        records.append({"name": ax, "kind": "unregistered"})
        ok = False
    return ok, msgs, records


# ── stage 11: score ──────────────────────────────────────────────────────────

def eval_score(parsed: ParsedCandidate, expr: str) -> Fraction:
    return _eval_rational(expr, dict(parsed.def_vals_eval))


def best_prior_score(config: WorkspaceConfig, exclude_sha: str) -> Optional[Fraction]:
    if not LOG_FILE.exists():
        return None
    best: Optional[Fraction] = None
    for line in LOG_FILE.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not rec.get("pass") or "score" not in rec:
            continue
        if rec.get("sha256") == exclude_sha:
            continue
        try:
            val = _parse_fraction(str(rec["score"]))
        except Exception:
            continue
        if best is None:
            best = val
        elif config.score_direction == "minimize":
            best = min(best, val)
        else:
            best = max(best, val)
    return best


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def append_log(record: dict[str, Any], path: Path = LOG_FILE) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as f:
        json.dump(record, f, sort_keys=True)
        f.write("\n")


def assert_benchmark_depth(config: WorkspaceConfig) -> None:
    """`lemma.toml`'s reported depth must agree with the trusted Lean source."""
    src = (PROJECT_ROOT / "PolygonCore" / "Polygon.lean").read_text()
    m = re.search(r"def\s+benchmarkDepth\s*:\s*ℕ\s*:=\s*(\d+)", strip_comments(src))
    if not m:
        raise SystemExit("FATAL: cannot read benchmarkDepth from PolygonCore/Polygon.lean")
    if int(m.group(1)) != config.benchmark_depth:
        raise SystemExit(
            f"FATAL: lemma.toml benchmark_depth={config.benchmark_depth} but "
            f"PolygonCore.benchmarkDepth={m.group(1)}"
        )


# ── driver ───────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", required=True)
    parser.add_argument("--skip-compile", action="store_true")
    parser.add_argument("--no-log", action="store_true")
    args = parser.parse_args()

    config = load_workspace_config()

    # Stage 10, hoisted: D3 is structural, so refuse to run at all if the config
    # has grown an oracle table.
    if config.oracles_declared:
        raise SystemExit(
            f"FATAL: lemma.toml declares {config.oracles_declared} oracle(s); "
            "decision D3 forbids oracles in this workspace."
        )
    assert_benchmark_depth(config)

    path = Path(args.file)
    if not path.is_absolute():
        path = (PROJECT_ROOT / path).resolve()
    if not path.is_file():
        raise SystemExit(f"FATAL: no such candidate file: {path}")
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
        "trust_class": "pure_lean",
        "benchmark_depth": config.benchmark_depth,
        "pass": False,
    }

    def die(reason: str, **extra: Any) -> None:
        record["reason"] = reason
        record.update(extra)
        if not args.no_log:
            append_log(record)
        print(f"status: FAIL — {reason}")
        raise SystemExit(1)

    print(f"candidate:     {path.relative_to(PROJECT_ROOT)}")
    print(f"namespace:     {parsed.namespace}")
    print(f"parent:        {parsed.parent or '(none)'}")

    # 1 ── workspace import audit
    ok, msgs, records, scanned = audit_workspace_imports(config)
    print(f"1  workspace imports:  {'PASS' if ok else 'FAIL'} ({scanned} files)")
    for msg in msgs:
        print(msg)
    record["workspace_import_violations"] = records
    if not ok:
        die("disallowed workspace import")

    # 2 ── candidate direct imports
    ok, msgs, records = audit_module_imports(parsed.imports, config.candidate_policy)
    print(f"2  candidate imports:  {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["imports"] = parsed.imports
    if not ok:
        die("disallowed import")

    # 3 ── transitive closure
    if config.candidate_policy.check_transitive:
        module = module_name_for_path(path)
        ok, hits, size, unresolved = audit_import_closure([module], config.candidate_policy)
        print(f"3  import closure:     {'PASS' if ok else 'FAIL'} ({size} modules)")
        for h in hits:
            print(f"  BLOCK {h} — reachable transitively.")
        record["import_closure_size"] = size
        record["import_closure_blocked"] = hits
        if not ok:
            die("blocked module in transitive import closure")
    else:
        record["import_closure_blocked"] = []

    # 4 ── static scan
    ok, msgs, records = static_scan(path, config)
    print(f"4  static scan:        {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["static_scan_violations"] = records
    if not ok:
        die("forbidden pattern or size limit")

    # 5 ── declarations present and sane
    if not parsed.has_theorem:
        die(f"theorem {config.sink_theorem} not found")
    for name in (config.constant_def, config.lower_constant_def):
        if name not in parsed.def_vals_eval:
            die(f"`def {name} : ℝ := <rational>` not found or not rational")
        # A scored constant must be defined exactly once. More than one
        # definition means the textual parse and Lean's name resolution can
        # disagree about which value is being scored — see the note on stage 7.
        if parsed.def_counts.get(name, 0) != 1:
            die(
                f"`{name}` is defined {parsed.def_counts.get(name, 0)} times; "
                "a scored constant must be defined exactly once"
            )
    kappa = parsed.def_vals_eval[config.constant_def]
    lam = parsed.def_vals_eval[config.lower_constant_def]
    record["kappa"] = str(kappa)
    record["lambda"] = str(lam)
    for value, name in ((kappa, config.constant_def), (lam, config.lower_constant_def)):
        digits_ok, msg = check_constant_digits(value, name, config)
        if not digits_ok:
            print(msg)
            die("constant exceeds digit limit")
    if not kappa > 0:
        die(f"contract requires 0 < {config.constant_def}, got {kappa}")
    if not lam >= 0:
        die(f"contract requires 0 ≤ {config.lower_constant_def}, got {lam}")
    if not lam < kappa:
        die(f"empty interval: {config.lower_constant_def}={lam} ≥ {config.constant_def}={kappa}")
    print(f"5  declarations:       PASS ({config.lower_constant_def}={lam}, {config.constant_def}={kappa})")

    # 6 ── compile
    if not args.skip_compile:
        ok, out, elapsed, metrics = compile_candidate(path)
        print(f"6  compile:            {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
        record["compile_elapsed_s"] = round(elapsed, 3)
        record.update({k: v for k, v in metrics.items()})
        if not ok:
            print(out[-4000:])
            die("compile failed", compile_output=out[-4000:])
    else:
        print("6  compile:            SKIP")

    # 7 ── exact contract type check
    ok, out, elapsed = theorem_type_check(path, parsed, config)
    print(f"7  type check:         {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
    record["typecheck_elapsed_s"] = round(elapsed, 3)
    if not ok:
        print(out[-4000:])
        die("contract type check failed", typecheck_output=out[-4000:])

    # 8 ── optional secondary contract
    secondary_score: Optional[Fraction] = None
    if parsed.has_secondary and config.secondary_constant_def in parsed.def_vals_eval \
            and config.secondary_lower_constant_def in parsed.def_vals_eval:
        ok, out, elapsed = secondary_type_check(path, parsed, config)
        print(f"8  secondary contract: {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
        if not ok:
            print(out[-4000:])
            die("secondary contract type check failed", secondary_output=out[-4000:])
        secondary_score = eval_score(parsed, config.secondary_score)
        record["score_secondary"] = str(secondary_score)
        record["kappaDepth10"] = str(parsed.def_vals_eval[config.secondary_constant_def])
        record["lambdaDepth10"] = str(parsed.def_vals_eval[config.secondary_lower_constant_def])
    else:
        print("8  secondary contract: SKIP (not declared)")

    # 9 ── axiom closure
    theorem_qual = f"{parsed.namespace}.{config.sink_theorem}"
    ok, used_axioms, out, elapsed = collect_used_axioms(path, theorem_qual)
    print(f"9  axiom scan:         {'PASS' if ok else 'FAIL'} ({elapsed:.2f}s)")
    if not ok:
        print(out[-4000:])
        die("axiom scan failed", axiom_scan_output=out[-4000:])
    ok, msgs, records = audit_axioms(used_axioms, config)
    print(f"   axiom audit:        {'PASS' if ok else 'FAIL'}")
    for msg in msgs:
        print(msg)
    record["axioms_used"] = sorted(used_axioms)
    if not ok:
        die("axiom closure is not a subset of the three standard axioms")

    # 10 ── oracle-table assertion (already enforced above; recorded for the log)
    record["oracles_declared"] = 0
    print("10 oracle table:       PASS (empty, as D3 requires)")

    # 11 ── score and incumbent
    score = eval_score(parsed, config.score)
    record["score"] = str(score)
    width = score / Fraction(4) ** config.benchmark_depth
    record["interval_width_at_depth10"] = str(width)
    record["def_vals"] = {k: str(v) for k, v in parsed.def_vals_eval.items()}
    incumbent = best_prior_score(config, record["sha256"])
    record["incumbent"] = str(incumbent) if incumbent is not None else None
    if incumbent is None:
        record["strict_improvement"] = None
    elif config.score_direction == "minimize":
        record["strict_improvement"] = score < incumbent
    else:
        record["strict_improvement"] = score > incumbent
    record["pass"] = True

    print(f"11 score ({config.score_direction}):    {score} = {float(score):.12f}")
    print(f"   interval width:     {width} = {float(width):.6e}  (depth {config.benchmark_depth})")
    print(f"   incumbent:          {record['incumbent']}  strict_improvement={record['strict_improvement']}")

    # 12 ── log
    if not args.no_log:
        append_log(record)
    print("status: PASS")


if __name__ == "__main__":
    main()
