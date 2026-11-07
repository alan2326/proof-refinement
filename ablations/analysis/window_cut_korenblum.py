#!/usr/bin/env python3
"""Post-hoc 1x matched-window cut for the korenblum tool-less arms.

The 2026-07-30 writeup framing gives every ablation "the same budget the
full framework used". For korenblum that is Arm A's measured usage:
T = 3285.4 s wall, O = 230,815 output tokens (runs/korenblum-armA-01).
The arms themselves ran under the older, more generous protocols (B: 2x
override; C: 3x floored; Bos: the 8322 s floored window), so the 1x
number is a replay cut: walk the recorded iteration/attempt events in
order and keep exactly those the 1x both-exceeded gate would have run.

Validity rests on the gate convention every runner uses -- checked BEFORE
each iteration/attempt, so an iteration that starts inside the window
completes -- and, for the one-shot arm, on attempts being independent
draws (workspace reset between attempts), which makes any prefix of the
run identical to a run at a smaller budget.

Usage: python3 analysis/window_cut_korenblum.py [T_s O_tok]
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
PARENT = Fraction(17823, 50000)

# Arm A's measured usage (runs/korenblum-armA-01/summary.json), NOT the
# 8322 s original-band floor recorded in reference_budget.json.
T_1X = 3285.4
O_1X = 230_815

ARMS = {
    "B (basic agent)": ["korenblum-armB-01", "korenblum-armB-02"],
    "Bos (no agent)": ["korenblum-armBos-01"],
}


def replay(run_ids: list[str], t_s: float, o_tok: int) -> dict:
    """Replay recorded events under a both-exceeded gate of (t_s, o_tok)."""
    rows = []
    tok = 0
    for rid in run_ids:
        ev = ROOT / "runs" / rid / "events.jsonl"
        if not ev.exists():
            continue
        for line in ev.read_text().splitlines():
            if not line.strip():
                continue
            e = json.loads(line)
            if e.get("kind") not in ("iteration", "attempt"):
                continue
            dur = e.get("wall_s") or 0.0
            end = e["elapsed_s"]              # -02 elapsed includes the carry
            u = e.get("usage") or {}
            out = u.get("output_tokens") or 0
            rows.append({
                "run": rid,
                "n": e.get("iteration") or e.get("attempt"),
                "start_wall": round(end - dur, 1),
                "end_wall": round(end, 1),
                "tok_before": tok,
                "tok_after": tok + out,
                "passed": e.get("passed"),
                "score": e.get("best_score_after") or e.get("attempt_score"),
            })
            tok += out

    included, stopped_at = [], None
    for r in rows:
        if r["start_wall"] > t_s and r["tok_before"] > o_tok:
            stopped_at = r
            break
        included.append(r)

    best = None
    for r in included:
        s = r.get("score")
        if not (r.get("passed") and s and s != "None"):
            continue
        try:
            v = Fraction(s)
        except (ValueError, ZeroDivisionError):
            continue
        if v > PARENT and (best is None or v > best):
            best = v
    last = included[-1] if included else None
    return {
        "gate": {"T_s": t_s, "O_output_tokens": o_tok,
                 "rule": "both-exceeded, checked before each iteration/attempt"},
        "iterations_included": [
            {k: str(v) if isinstance(v, Fraction) else v for k, v in r.items()}
            for r in included],
        "state_at_stop": {"wall_s": last["end_wall"], "output_tokens": last["tok_after"]}
        if last else None,
        "first_excluded": ({"run": stopped_at["run"], "n": stopped_at["n"]}
                           if stopped_at else "none -- recorded run never crossed the gate"),
        "best_in_window": str(best) if best else None,
        "best_in_window_float": float(best) if best else None,
        "gain_over_parent": float(best - PARENT) if best else 0.0,
    }


def main():
    t_s = float(sys.argv[1]) if len(sys.argv) > 2 else T_1X
    o_tok = int(sys.argv[2]) if len(sys.argv) > 2 else O_1X
    out = {"parent": str(PARENT), "parent_float": float(PARENT),
           "reference": {"source": "korenblum-armA-01 measured usage",
                         "T_s": t_s, "O_output_tokens": o_tok},
           "arms": {}}
    for name, ids in ARMS.items():
        out["arms"][name] = replay(ids, t_s, o_tok)
    print(json.dumps(out, indent=2))
    (ROOT / "analysis" / "window_cut_korenblum.json").write_text(
        json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
