"""Shared instrumentation for the ablation arms.

Records every metric M1-M11 from docs/2026-07-27-ablation-design.md sect. 4.1.
"""
from __future__ import annotations

import glob
import hashlib
import json
import os
import platform
import shutil
import subprocess
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
RUNS = ROOT / "runs"
ANCHOR_PARENT_SCORE = Fraction(17823, 50000)      # V64, c = 0.35646
ELAN = str(Path.home() / ".elan" / "bin")


# --------------------------------------------------------------------- utils
def sh(cmd, **kw):
    env = {**os.environ, "PATH": ELAN + os.pathsep + os.environ["PATH"]}
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True,
                          text=True, env=env, **kw)


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def sha256_tree(root: Path, skip=(".lake", ".venv", ".uv-cache", ".git")) -> str:
    """Content hash of a workspace, ignoring build caches."""
    h = hashlib.sha256()
    for p in sorted(root.rglob("*")):
        if any(s in p.relative_to(root).parts for s in skip) or not p.is_file():
            continue
        h.update(str(p.relative_to(root)).encode())
        h.update(p.read_bytes())
    return h.hexdigest()


FATAL_API = (
    "credit balance is too low",
    "authentication_error",
    "invalid x-api-key",
    "permission_error",
    "your account has been disabled",
)


def reap_orphaned_claude() -> int:
    """Kill `claude -p` processes whose parent runner is already dead.

    SIGKILLing a runner leaves its `claude -p` child reparented to init, still
    running and still consuming subscription quota for output nobody will read.
    Two such orphans accumulated across Arm B relaunches. Sweep them at startup.
    """
    out = sh(["ps", "-eo", "pid,ppid,cmd"]).stdout.splitlines()
    killed = 0
    for line in out:
        parts = line.split(None, 2)
        if len(parts) < 3:
            continue
        pid, ppid, cmd = parts
        if ppid == "1" and "claude -p" in cmd:
            try:
                os.kill(int(pid), 15)
                killed += 1
            except (ProcessLookupError, PermissionError, ValueError):
                pass
    return killed


def is_fatal_api_error(msg: str) -> bool:
    """Conditions that will not fix themselves -- abort as D7 rather than spin.

    Arm C burned 996 no-op sprint attempts against an exhausted credit balance
    before hitting its max-sprints guard; without this the token/wall budgets
    look consumed when nothing was actually attempted.
    """
    m = (msg or "").lower()
    return any(f in m for f in FATAL_API)


# ------------------------------------------------------------------ hardware
def hardware_snapshot() -> dict:
    cpu = sh("lscpu").stdout
    def grab(key, default=""):
        for line in cpu.splitlines():
            if line.startswith(key):
                return line.split(":", 1)[1].strip()
        return default
    gpus = sh("nvidia-smi --query-gpu=name,memory.total --format=csv,noheader").stdout
    mem = sh("free -g").stdout.splitlines()
    return {
        "cpu_model": grab("Model name"),
        "cpu_logical": grab("CPU(s)"),
        "cpu_cores_per_socket": grab("Core(s) per socket"),
        "cpu_sockets": grab("Socket(s)"),
        "ram_gb_total": mem[1].split()[1] if len(mem) > 1 else "",
        "gpus": [g.strip() for g in gpus.strip().splitlines() if g.strip()],
        "gpu_used_by_workload": False,   # LLM is remote; Lean/mpmath are CPU-only
        "os": platform.platform(),
        "kernel": platform.release(),
        "python": platform.python_version(),
    }


def toolchain_snapshot(ws: Path) -> dict:
    manifest = {}
    lm = ws / "lake-manifest.json"
    if lm.exists():
        d = json.loads(lm.read_text())
        for p in d.get("packages", []):
            if p.get("name") in ("mathlib", "batteries", "checkdecls"):
                manifest[p["name"]] = p.get("rev", "")
    return {
        "lean_toolchain": (ws / "lean-toolchain").read_text().strip()
        if (ws / "lean-toolchain").exists() else "",
        "deps": manifest,
        "claude_code": sh("claude --version").stdout.strip(),
        "uv": sh("uv --version").stdout.strip(),
    }


# --------------------------------------------------------------------- prompts
PROMPT_FILES = [
    ".claude/agents/korenblum-refinement-planner.md",
    ".claude/agents/korenblum-refinement-generator.md",
    ".claude/agents/korenblum-refinement-evaluator.md",
    ".claude/skills/run-next-korenblum-sprint/SKILL.md",
    "ProofRefinement/Korenblum/AGENT_BRIEF.md",
    "ProofRefinement/Korenblum/START_HERE.md",
    "ProofRefinement/Korenblum/README.md",
    "ProofRefinement/Korenblum/Sprint_Contracts/TEMPLATE.md",
    "CLAUDE.md",
]


def archive_prompts(ws: Path, run_dir: Path) -> dict:
    out, hashes = run_dir / "prompts", {}
    out.mkdir(parents=True, exist_ok=True)
    for rel in PROMPT_FILES:
        src = ws / rel
        if src.exists():
            dst = out / rel.replace("/", "__")
            shutil.copy2(src, dst)
            hashes[rel] = sha256_file(src)
    return hashes


# ------------------------------------------------------------------ run state
class Run:
    def __init__(self, run_id: str, arm: str, ws: Path, meta_extra: dict | None = None):
        self.run_id, self.arm, self.ws = run_id, arm, ws
        self.dir = RUNS / run_id
        self.dir.mkdir(parents=True, exist_ok=True)
        self.events = self.dir / "events.jsonl"
        self.t0 = time.time()
        self.tok_out = self.tok_in = self.tok_cw = self.tok_cr = 0
        self.usd = 0.0
        self.calls = self.builds = self.evals = self.failed = 0
        self.models: dict[str, dict] = {}
        self.manifest = {
            "run_id": run_id, "arm": arm, "constant": "korenblum",
            "workspace": str(ws),
            "anchor": {
                "parent": "Candidates/V64.lean",
                "c_parent": str(ANCHOR_PARENT_SCORE),
                "goal": "evaluator pass with score > 17823/50000",
                "reference_sprints": ["084", "085", "086", "087", "088"],
                "note": "085's DRY refactor is pre-applied in S0 (see design sect. 2.4)",
            },
            "snapshot_sha256": sha256_tree(ws),
            "hardware": hardware_snapshot(),
            "toolchain": toolchain_snapshot(ws),
            "prompt_sha256": archive_prompts(ws, self.dir),
            "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            **(meta_extra or {}),
        }
        (self.dir / "manifest.json").write_text(json.dumps(self.manifest, indent=2))

    # -- logging ----------------------------------------------------------
    def emit(self, kind: str, **kw):
        rec = {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "elapsed_s": round(time.time() - self.t0, 3), "kind": kind, **kw}
        with self.events.open("a") as fh:
            fh.write(json.dumps(rec, sort_keys=True) + "\n")
        return rec

    def account(self, cc_json: dict):
        """Fold one `claude -p --output-format json` result into the totals.

        CRITICAL: the top-level `usage` block reports only the DRIVER's own
        final turn -- it excludes every subagent.  For the Korenblum harness
        that is a ~50x under-count (measured: usage.output_tokens = 4,592 vs
        modelUsage total = 230,815 for the same sprint), because essentially
        all the work happens inside the planner / generator / evaluator
        subagents.  `modelUsage` is the aggregate across all of them and is
        the only correct source.  Always prefer it; fall back to the top-level
        block only if modelUsage is absent.
        """
        mus = cc_json.get("modelUsage") or {}
        self.usd += cc_json.get("total_cost_usd", 0.0) or 0.0
        self.calls += cc_json.get("num_turns", 0) or 0

        if mus:
            for m, mu in mus.items():
                d = self.models.setdefault(
                    m, {"in": 0, "out": 0, "cr": 0, "cw": 0, "usd": 0.0})
                d["in"] += mu.get("inputTokens", 0)
                d["out"] += mu.get("outputTokens", 0)
                d["cr"] += mu.get("cacheReadInputTokens", 0)
                d["cw"] += mu.get("cacheCreationInputTokens", 0)
                d["usd"] += mu.get("costUSD", 0.0)
                self.tok_in += mu.get("inputTokens", 0)
                self.tok_out += mu.get("outputTokens", 0)
                self.tok_cr += mu.get("cacheReadInputTokens", 0)
                self.tok_cw += mu.get("cacheCreationInputTokens", 0)
        else:
            u = cc_json.get("usage", {}) or {}
            self.tok_in += u.get("input_tokens", 0)
            self.tok_out += u.get("output_tokens", 0)
            self.tok_cw += u.get("cache_creation_input_tokens", 0)
            self.tok_cr += u.get("cache_read_input_tokens", 0)

    @property
    def wall(self) -> float:
        return time.time() - self.t0

    def totals(self) -> dict:
        return {
            "wall_clock_s": round(self.wall, 1),
            "output_tokens": self.tok_out,
            "input_tokens": self.tok_in,
            "cache_creation_tokens": self.tok_cw,
            "cache_read_tokens": self.tok_cr,
            "model_calls_turns": self.calls,
            "usd_total": round(self.usd, 4),
            "lake_builds": self.builds,
            "evaluator_runs": self.evals,
            "failed_attempts": self.failed,
            "per_model": self.models,
        }

    def finish(self, label: str, evidence: str = ""):
        self.snapshot_transcripts()
        summary = {"run_id": self.run_id, "arm": self.arm,
                   "terminal_label": label, "evidence": evidence,
                   "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                   "best_score": str(best_score(self.ws)),
                   **self.totals()}
        (self.dir / "summary.json").write_text(json.dumps(summary, indent=2))
        self.emit("terminal", label=label, evidence=evidence, **self.totals())
        return summary

    # -- transcripts ------------------------------------------------------
    def snapshot_transcripts(self):
        """Copy every Claude Code session transcript this run produced.

        The May-2026 originals were lost to Claude Code's default cleanup; this
        is the mitigation (design sect. 6.3).
        """
        out = self.dir / "transcripts"
        out.mkdir(exist_ok=True)
        ids = set()
        if self.events.exists():
            for line in self.events.read_text().splitlines():
                sid = json.loads(line).get("session_id")
                if sid:
                    ids.add(sid)
        n = 0
        for sid in ids:
            for hit in glob.glob(str(Path.home() / ".claude" / "projects" / "*" / f"{sid}.jsonl")):
                shutil.copy2(hit, out / f"{sid}.jsonl")
                n += 1
        return n


# ------------------------------------------------------------------- scoring
def best_score(ws: Path) -> Fraction | None:
    """Highest passing score in the workspace evaluator log."""
    lj = ws / "ProofRefinement" / "Korenblum" / "Refinement_Log" / "log.jsonl"
    if not lj.exists():
        return None
    best = None
    for line in lj.read_text().splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        if r.get("pass") and r.get("score"):
            try:
                v = Fraction(r["score"])
            except (ValueError, ZeroDivisionError):
                continue
            if best is None or v > best:
                best = v
    return best


def goal_reached(ws: Path) -> bool:
    b = best_score(ws)
    return b is not None and b > ANCHOR_PARENT_SCORE


def count_log_rows(ws: Path) -> tuple[int, int]:
    """(total evaluator invocations, failures) in the workspace log."""
    lj = ws / "ProofRefinement" / "Korenblum" / "Refinement_Log" / "log.jsonl"
    if not lj.exists():
        return 0, 0
    rows = [json.loads(l) for l in lj.read_text().splitlines() if l.strip()]
    return len(rows), sum(1 for r in rows if not r.get("pass"))
