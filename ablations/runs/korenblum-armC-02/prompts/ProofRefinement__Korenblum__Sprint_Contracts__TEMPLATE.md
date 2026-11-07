# Sprint <NNN>: <one-line title>

**Created**: <YYYY-MM-DD HH:MM> by Planner
**Parent candidate**: `Candidates/V<K>.lean`
**Target file**: `Candidates/V<N>.lean`
**Direction**: <raise-c | direct-proof | section2-proof | oracle-support | other>

## Goal

<One sentence describing the exact mathematical move.>

The move may use equation `(15)`, refine Wang Section 2 directly, or bypass the
current seed route entirely. The only fixed target is the final theorem shape.

## Why

<Two or three sentences. Include the concrete reason this sprint is worth
running now.>

## Concrete edits expected

- `<path>`: <edit description>
- `<path>`: <edit description>

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V<N>` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V<N>.lean` succeeds.
3. `<score inequality or other precise success condition>`

## Out of scope

- Edit older candidates.
- Change the final theorem statement.
- Add a free-floating new axiom unless the contract explicitly depends on an
  approved proposal.

## Time budget

≤ <minutes> minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
