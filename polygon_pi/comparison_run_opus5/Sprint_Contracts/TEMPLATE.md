# sprint_<NNN>_<slug>

**Rung type:** `architectural` | `precision` | `infrastructure`
_(required. `architectural` = a new analytic ingredient. `precision` = a better
constant through the existing chain. `infrastructure` = tooling, notes, or
refactoring with no score effect. A `precision` sprint must justify itself
against the last `architectural` one in the Rationale.)_

**Parent candidate:** `Candidates/V<N>.lean` (score `<s>`)
**Target file:** `Candidates/V<N+1>.lean`
**Side:** `upper` | `lower` | `both`
**Strict improvement required:** yes | no

## Goal

One or two sentences. What quantity moves, and why this is the next smallest
useful step.

## Rationale

Why this sprint rather than the alternatives. If the rung type is `precision`,
say explicitly what the last architectural rung was and why a precision push is
the right move now rather than another architectural one.

## Concrete edits expected

- `Candidates/V<N+1>.lean` — …
- `Candidates/V<N+1>/<Name>.lean` — … _(only if a substantial derived theorem is
  needed; theorems only, never axioms)_
- `Experience.md` — append the sprint entry

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, or any older candidate is out of scope for every sprint.

## Acceptance criteria

Concrete and falsifiable. For example:

- [ ] `Candidates/V<N+1>.lean` declares `def kappa : ℝ := <literal>` and
      `def lambda : ℝ := <literal>` on single lines
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V<N+1>` succeeds
- [ ] the evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
- [ ] `score < <parent score>` _(if strict improvement is required)_

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V<N+1>
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V<N+1>.lean --no-log
```

## Notes / expected obstructions

Anything the planner already knows will be hard, and any relevant entry in
`Experience.md` the generator should read first.
