"""Shared instrumentation for the sprint-016 Grothendieck ablation arms.

Fork of groth_common.py per design doc sect. 13 -- the sect. 12 harness stays
byte-stable. Differences:

  * anchor parent = V11 at Cr_val = 1 (sprint-016 anchor, sect. 13.1);
  * ORIGINAL_BAND_S = 2360: S0^16 commit 5db00044 (2026-04-30T07:40:56Z) ->
    verdict_017 commit 410a45c1 (08:20:16Z). NOTE this corrects sect. 13.1's
    draft figure of 1,837 s: verdict_016 (08:11:33) was a G3 write-scope FAIL;
    the byte-identical V12 was accepted by the sprint-017 salvage at 08:20:16.
    The honest "original band" for V11 -> accepted V12 includes the salvage.
  * SUCCESS BAR (sect. 13.2): Arms A and B succeed only with an accepted
    candidate at Cr_val <= BAR, where BAR is fixed pre-run from the measured
    no-Lean envelope (runs/groth16_envelope/envelope.json). Plain improvements
    (Cr < 1) are logged as within-envelope progress, not success.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

# Re-export everything structural from the sect. 12 fork; only the constants
# and goal semantics differ.
import sys as _sys
_sys.path.insert(0, str(Path(__file__).parent))
import groth_common as _g12  # noqa: E402

ROOT = _g12.ROOT
RUNS = _g12.RUNS
LEMMA_REL = _g12.LEMMA_REL
ELAN = _g12.ELAN
sh = _g12.sh
sha256_file = _g12.sha256_file
sha256_tree = _g12.sha256_tree
is_fatal_api_error = _g12.is_fatal_api_error
reap_orphaned_claude = _g12.reap_orphaned_claude
hardware_snapshot = _g12.hardware_snapshot
toolchain_snapshot = _g12.toolchain_snapshot
archive_prompts = _g12.archive_prompts
best_score = _g12.best_score
count_log_rows = _g12.count_log_rows
_iter_log = _g12._iter_log
_row_passed = _g12._row_passed
_row_score = _g12._row_score

ANCHOR_PARENT_SCORE = Fraction(1, 1)          # V11, Cr_val
ORIGINAL_BAND_S = 2360

ENVELOPE_FILE = ROOT / "runs" / "groth16_envelope" / "envelope.json"


def load_envelope() -> dict:
    """The P1 measurement (sect. 13.2). Hard requirement before any arm."""
    if not ENVELOPE_FILE.exists():
        raise SystemExit(f"P1 envelope missing: {ENVELOPE_FILE} -- run "
                         "harness/envelope_groth16.py first (sweep+combine)")
    return json.loads(ENVELOPE_FILE.read_text())


def bar() -> Fraction:
    return Fraction(load_envelope()["BAR"][0])


def bar_reached(ws: Path) -> bool:
    b = best_score(ws)
    return b is not None and b <= bar()


def improved(ws: Path) -> bool:
    """Any accepted candidate below the parent (within-envelope progress)."""
    b = best_score(ws)
    return b is not None and b < ANCHOR_PARENT_SCORE


class Run(_g12.Run):
    """sect. 13 run: same instrumentation, sprint-016 anchor block."""

    def __init__(self, run_id: str, arm: str, ws: Path,
                 meta_extra: dict | None = None):
        env = load_envelope()
        # meta_extra spreads AFTER the base manifest fields, so "anchor" and
        # "constant" here REPLACE the sect. 12 (sprint-030) values.
        anchor_extra = {
            "constant": "grothendieck_lemma54 (sprint-016 anchor)",
            "anchor": {
                "parent": "Candidates/V11.lean",
                "score_parent": "1",
                "direction": "minimize",
                "goal": f"evaluator-accepted candidate with Cr_val <= BAR = "
                        f"{env['BAR'][0]}",
                "reference_sprints": ["016", "017 (salvage of 016's G3 "
                                      "write-scope FAIL; V12 byte-identical)"],
                "s0_commit": "5db00044",
                "original_band_s": ORIGINAL_BAND_S,
                "original_band_note": (
                    "07:40:56Z (S0^16, 5db00044) -> 08:20:16Z (verdict_017, "
                    "410a45c1). Corrects the sect. 13.1 draft (1,837 s to "
                    "verdict_016 only, which was a FAIL)."),
                "no_lean_envelope": env["envelope"],
                "envelope_route": env["envelope_route"],
                "BAR": env["BAR"],
                "bar_rationale": ("largest round rational <= envelope/2; "
                                  "unreachable by declared-value/resolution "
                                  "shaving on the frozen Lean surface "
                                  "(sect. 13.2)"),
            },
        }
        super().__init__(run_id, arm, ws,
                         meta_extra={**anchor_extra, **(meta_extra or {})})
