#!/usr/bin/env python3
"""Assign a DNF label to each completed run, per design sect. 5.

Every label is backed by a predicate over the run's event log and the
workspace's evaluator log, plus an evidence pointer. Output is advisory: the
labels are meant to be human-reviewed before they go in the paper.

Usage:  python3 analysis/classify.py [run_id ...]
"""
from __future__ import annotations

import json
import re
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
RUNS = ROOT / "runs"
PARENT = Fraction(17823, 50000)

LABELS = {
    "S":  "SUCCESS -- certified c > parent under an intact trust surface",
    "D1": "STRATEGY-DNF -- never proposed a candidate with c' > parent",
    "D2": "NUMERICAL-DNF -- proposed higher c, numerical certificate failed",
    "D3": "FORMALIZATION-DNF -- direction+certificate ok, Lean never compiled",
    "D4": "TRUST-DNF -- 'passing' artifact violates the trust surface",
    "D5": "BUDGET-DNF -- budget exhausted with live non-regressive progress",
    "D6": "THRASH-DNF -- same failing edit repeated, or score regressed",
    "D7": "INFRA-DNF -- harness/tooling failure (excluded from denominators)",
}


def load(run_id: str):
    d = RUNS / run_id
    events = [json.loads(l) for l in (d / "events.jsonl").read_text().splitlines()
              if l.strip()] if (d / "events.jsonl").exists() else []
    manifest = json.loads((d / "manifest.json").read_text())
    summary = (json.loads((d / "summary.json").read_text())
               if (d / "summary.json").exists() else None)
    return d, manifest, events, summary


def proposed_c_values(ws: Path) -> list[Fraction]:
    """Every c the arm actually put in front of the evaluator, pass or fail."""
    lj = ws / "ProofRefinement" / "Korenblum" / "Refinement_Log" / "log.jsonl"
    out = []
    if not lj.exists():
        return out
    for line in lj.read_text().splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        for key in ("score", None):
            v = r.get(key) if key else (r.get("def_vals") or {}).get("c_value")
            if v:
                try:
                    out.append(Fraction(v))
                except (ValueError, ZeroDivisionError):
                    pass
                break
    return out


SINK_PRED = "ValidKorenblumBound"


def trust_violations(ws: Path, manifest: dict) -> list[str]:
    """D4 predicates.

    NOTE: growth of `[seed_axioms].allowed` is NOT a violation on its own -- it
    is this workspace's documented workflow. V64, the anchor parent, was itself
    accepted carrying `hH2_v64`, `hCircleGapInt_v64` and its own oracle added
    exactly that way, and AGENT_BRIEF.md permits it explicitly. An earlier
    version of this function flagged any allow-list growth and consequently
    mislabelled BOTH genuine successes as D4.

    A real violation is one of:
      1. `sorryAx` anywhere in an accepted candidate's audit;
      2. an axiom the evaluator classed as neither seed nor oracle;
      3. an oracle-backed axiom the evaluator did not recompute (`ok != true`);
      4. a CONCLUSION-SHAPED axiom -- one whose Lean statement applies the sink
         predicate itself, i.e. assuming the very thing to be proved.
    """
    bad = []
    kore = ws / "ProofRefinement" / "Korenblum"
    lj = kore / "Refinement_Log" / "log.jsonl"
    accepted_axioms: set[str] = set()
    if lj.exists():
        for line in lj.read_text().splitlines():
            if not line.strip():
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not r.get("pass"):
                continue
            for ax in r.get("axioms_used", []):
                name = ax.get("name", "")
                short = name.rsplit(".", 1)[-1]
                if "sorryAx" in name:
                    bad.append(f"sorryAx in {r.get('candidate')}")
                if ax.get("kind") not in ("seed", "oracle"):
                    bad.append(f"unregistered axiom {name} in {r.get('candidate')}")
                accepted_axioms.add(short)
            for oc in r.get("oracle_checks", []):
                if not oc.get("ok"):
                    bad.append(f"oracle {oc.get('axiom')} not recomputed ok "
                               f"in {r.get('candidate')}")

    # The SEED axiom is the arm's given starting point, not something it
    # introduced. Arm C's seed (`hKorenblum_prev : ValidKorenblumBound
    # (35646/100000)`) is conclusion-shaped BY CONSTRUCTION -- that is the
    # whole design of the no-PF arm -- so anything declared in V0.lean is
    # exempt from check (4).
    seed_axioms: set[str] = set()
    v0 = kore / "Candidates" / "V0.lean"
    if v0.exists():
        seed_axioms = set(re.findall(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)",
                                     v0.read_text(), re.M))

    # (4) conclusion-shaped axioms: read each axiom's declaration and see
    #     whether the sink predicate appears in its statement.
    for lean in list((kore / "Candidates").rglob("*.lean")) + \
                list((kore / "Proof").rglob("*.lean")):
        try:
            src = lean.read_text()
        except OSError:
            continue
        for m in re.finditer(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)"
                             r"(.*?)(?=^\s*$|^axiom |^theorem |^def |\Z)",
                             src, re.S | re.M):
            name, body = m.group(1), m.group(2)
            if name not in accepted_axioms or name in seed_axioms:
                continue
            if SINK_PRED in body:
                bad.append(f"conclusion-shaped axiom `{name}` in {lean.name}: "
                           f"its statement applies {SINK_PRED}")
    return bad


def classify(run_id: str) -> dict:
    d, manifest, events, summary = load(run_id)
    ws = Path(manifest["workspace"])
    best = Fraction(summary["best_score"]) if summary and summary.get("best_score") \
        not in (None, "None") else None
    proposed = proposed_c_values(ws)
    max_proposed = max(proposed) if proposed else None
    viol = trust_violations(ws, manifest)

    infra = [e for e in events if e["kind"] in ("driver_timeout", "llm_error")]
    fail_stages = Counter(e.get("stage") for e in events
                          if e["kind"] == "iteration" and e.get("passed") is False)
    edits = Counter(e.get("feedback_tail", "")[:300] for e in events
                    if e["kind"] == "iteration" and e.get("passed") is False)
    thrash = max(edits.values()) if edits else 0

    # ---- decide, most-specific first
    if viol:
        label, ev = "D4", "; ".join(viol[:4])
    elif best is not None and best > PARENT:
        label, ev = "S", f"certified {best} > {PARENT}"
    elif len(infra) >= 3 and not proposed:
        label, ev = "D7", f"{len(infra)} harness/API failures, nothing evaluated"
    elif thrash >= 5:
        label, ev = "D6", f"same failing result repeated {thrash}x"
    elif max_proposed is None or max_proposed <= PARENT:
        label, ev = "D1", (f"no candidate above parent was ever evaluated "
                           f"(max proposed {max_proposed})")
    elif fail_stages.get("evaluator", 0) and "oracle" in "".join(
            e.get("feedback_tail", "") for e in events).lower():
        label, ev = "D2", "higher c proposed; oracle/numerical certification failed"
    elif fail_stages.get("build", 0):
        label, ev = "D3", (f"higher c proposed ({max_proposed}); Lean never "
                           f"compiled ({fail_stages['build']} build failures)")
    else:
        label, ev = "D5", (summary or {}).get("evidence", "budget exhausted")

    return {
        "run_id": run_id,
        "arm": manifest["arm"],
        "harness_label": (summary or {}).get("terminal_label"),
        "classified_label": label,
        "label_meaning": LABELS[label],
        "evidence": ev,
        "best_certified_c": str(best) if best else None,
        "max_proposed_c": str(max_proposed) if max_proposed else None,
        "trust_violations": viol,
        "infra_events": len(infra),
        "totals": {k: (summary or {}).get(k) for k in
                   ("wall_clock_s", "output_tokens", "input_tokens",
                    "cache_read_tokens", "model_calls_turns", "usd_total",
                    "evaluator_runs", "failed_attempts")},
    }


def main():
    ids = sys.argv[1:] or [p.name for p in sorted(RUNS.iterdir())
                           if p.is_dir() and (p / "manifest.json").exists()]
    out = []
    for r in ids:
        try:
            out.append(classify(r))
        except Exception as exc:                        # noqa: BLE001
            out.append({"run_id": r, "error": f"{type(exc).__name__}: {exc}"})
    print(json.dumps(out, indent=2))
    (ROOT / "analysis" / "classification.json").write_text(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
