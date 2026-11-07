# Sprint <NNN>: <one-line title>

**Created**: <YYYY-MM-DD HH:MM> by Planner
**Parent candidate**: `Candidates/V<K>.lean`
**Target file**: `Candidates/V<N>.lean`
**Direction**: <raise-c | direct-proof | section2-proof | oracle-support | other>

## Goal

<One sentence describing the exact mathematical move.>

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

<Two or three sentences. Include the concrete reason this sprint is worth
running now.>

## Concrete edits expected

- `<path>`: <edit description>
- `<path>`: <edit description>

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V<N>` succeeds.
2. `env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V<N>.lean` succeeds.
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
