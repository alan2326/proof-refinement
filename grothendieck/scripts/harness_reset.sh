#!/usr/bin/env bash
# scripts/harness_reset.sh — bring the proof refinement harness back to a
# clean V0-only state.
#
# Removes all current candidates (V1+), Sprint Contracts (sprint_002+),
# verdicts, log entries, sprint-state scratch, the bulletin, and the
# experience notebook. Re-seeds `log.jsonl` with V0's most recent PASS,
# restores Bulletin.md and Experience.md to template skeletons, and
# leaves sprint_001.md + TEMPLATE.md intact.
#
# Loss prevention is git-based: the project's PostToolUse auto-checkpoint
# hook commits every Edit/Write, and this script doesn't touch git
# history. If you need to recover anything this script removes, use
# `git log --diff-filter=D --name-only` plus `git show <sha>:<path>`.
#
# Usage:
#   bash scripts/harness_reset.sh             # remove + reset
#   bash scripts/harness_reset.sh --dry-run   # show what would be removed

set -euo pipefail

DRY_RUN=0
if [[ "${1:-}" == "--dry-run" ]]; then
    DRY_RUN=1
fi

ROOT="ProofRefinement/Lemma54"

run() {
    if [[ $DRY_RUN -eq 1 ]]; then
        echo "DRY-RUN: $*"
    else
        eval "$@"
    fi
}

echo "==> harness_reset starting (recovery via git history)"

# 1. Candidates V1+ (V0 stays).
shopt -s nullglob
for f in "$ROOT"/Candidates/V[1-9]*.lean; do
    [[ -f "$f" ]] || continue
    run "rm -f \"$f\""
    echo "  removed: $(basename "$f")"
done

# 2. Sprint Contracts sprint_002+ (sprint_001 + TEMPLATE stay).
for f in "$ROOT"/Sprint_Contracts/sprint_*.md; do
    [[ -f "$f" ]] || continue
    base=$(basename "$f")
    if [[ "$base" == "sprint_001.md" ]]; then continue; fi
    run "rm -f \"$f\""
    echo "  removed: $base"
done

# 3. Verdict files.
for f in "$ROOT"/Refinement_Log/verdict_*.md; do
    [[ -f "$f" ]] || continue
    run "rm -f \"$f\""
    echo "  removed: $(basename "$f")"
done

# 4. Log: re-seed with V0 baseline preserved.
if [[ -f "$ROOT/Refinement_Log/log.jsonl" ]]; then
    BASELINE=$(grep '"candidate":"Candidates/V0.lean"' "$ROOT/Refinement_Log/log.jsonl" | tail -n 1 || true)
    if [[ -n "$BASELINE" && $DRY_RUN -eq 0 ]]; then
        echo "$BASELINE" > "$ROOT/Refinement_Log/log.jsonl"
        echo "  log: reseeded with latest V0 baseline (1 entry)"
    elif [[ -n "$BASELINE" ]]; then
        echo "DRY-RUN: would reseed log with latest V0 baseline"
    else
        run ": > \"$ROOT/Refinement_Log/log.jsonl\""
        echo "  log: emptied (no V0 entry found)"
    fi
fi

# 5. Sprint_State scratch files.
for f in "$ROOT"/Sprint_State/*; do
    [[ -e "$f" ]] || continue
    run "rm -rf \"$f\""
    echo "  removed: Sprint_State/$(basename "$f")"
done

# 6. Bulletin.md — reset to template.
if [[ $DRY_RUN -eq 0 && -f "$ROOT/Bulletin.md" ]]; then
    cat > "$ROOT/Bulletin.md" <<'EOF'
# Bulletin — proof refinement loop

Volatile signaling between sprints. Capped at ~100 lines; the
`/run-next-sprint` skill trims it to the last 50 when it grows past
the cap. The historical record is `Refinement_Log/log.jsonl`.

Format: one line per event.

```
sprint_<NNN> queued: <title> [direction: <axis>]
sprint_<NNN> PASS: <title>
sprint_<NNN> FAIL: <title> (gate: G<id>)
note: <human note>
```

## Current priority

(human-set; the Planner reads this when deciding the next direction)

> No specific priority. The Planner is expected to read the active
> Lean code in `Proof/Lib/Lemma54_Paper*.lean`, run experiments in
> `Scratch/`, and **propose its own refinement direction**. Vary the
> direction across sprints — the "no same-direction-more-than-3-in-
> a-row" rule applies.

## Recent events

(append below; older entries get trimmed)
EOF
    echo "  Bulletin.md: reset to template"
fi

# 7. Experience.md — reset to skeleton.
if [[ $DRY_RUN -eq 0 && -f "$ROOT/Experience.md" ]]; then
    cat > "$ROOT/Experience.md" <<'EOF'
# Experience — proof refinement notebook

Free-form, append-only notes from Generators across sprints. What was
tried, what worked, what didn't, what's worth retrying. The
`Refinement_Log/log.jsonl` is the structured record; this is the
narrative companion.

Conventions:

- Entries dated `### YYYY-MM-DD sprint_<NNN>` for traceability.
- One paragraph per entry. No multi-page narratives.
- No claims about whether checks pass — describe the change, not the
  outcome. The Evaluator's verdict file is the source of truth on
  pass/fail.

## Entries

EOF
    echo "  Experience.md: reset to skeleton"
fi

echo ""
echo "==> harness_reset complete."
if [[ $DRY_RUN -eq 1 ]]; then
    echo "    (dry run — no files removed)"
else
    echo "    Active state:"
    echo "      Candidates/: $(ls $ROOT/Candidates/ | tr '\n' ' ')"
    echo "      Sprint_Contracts/: $(ls $ROOT/Sprint_Contracts/ | tr '\n' ' ')"
    echo "      Refinement_Log/: $(ls $ROOT/Refinement_Log/ | tr '\n' ' ')"
    echo ""
    echo "    To recover anything that was removed, see git history:"
    echo "      git log --diff-filter=D --name-only | head -50"
    echo "      git show <sha>:ProofRefinement/Lemma54/<path>"
    echo ""
    echo "Next: open a fresh Claude Code session and run /run-next-sprint"
fi
