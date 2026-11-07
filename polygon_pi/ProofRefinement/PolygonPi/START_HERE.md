# START HERE — Polygon-π proof refinement workspace

You are working inside a persistent Lean proof-refinement loop. Read this file,
then `AGENT_BRIEF.md`, then whatever your role's agent definition tells you.

## Local-only discipline

**`ProofRefinement/PolygonPi/` plus the trusted modules pinned in `lemma.toml`
is your entire working context.**

- Do not read or search outside this folder unless the human explicitly asks.
- Do not read the Mathlib source tree looking for π bounds. Mathlib's own
  numerical π machinery has been removed from this checkout on purpose; the point
  of the exercise is to rebuild the quantitative part yourself.
- Do not go looking for a directory of reference answers. There is one, it is
  outside your context, and reading it invalidates the run.

If you find yourself wanting a number you did not prove, prove it.

## The task in one line

Minimize `kappa - lambda` subject to proving, **for every** depth `n`,

    polygonLower n + lambda / 4 ^ n  <  π  <  polygonLower n + kappa / 4 ^ n

where `polygonLower n` is half the perimeter of the inscribed regular
`2 ^ (n + 2)`-gon. Smaller score is better. The incumbent is in `Bulletin.md`.

## First reads

1. `AGENT_BRIEF.md` — the contract, the rules, what you may and may not touch
2. `Bulletin.md` — current frontier, incumbent, and the human's standing priorities
3. `Experience.md` — what previous sprints tried, and what failed
4. `Candidates/V0.lean` — the baseline. One worked instance of the whole chain
5. `Proof/CandidateContract.lean` — the exact statement you must prove

## First checks

```bash
# build the current best candidate
lake build ProofRefinement.PolygonPi.Candidates.V0

# run the full evaluator on it
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V0.lean --no-log
```

Both should pass. If they do not, stop and say so — do not start editing.

## The one thing that will get your candidate rejected fastest

Any axiom outside `{propext, Classical.choice, Quot.sound}`. That means no
`sorry`, no `axiom`, and no `native_decide` — the last one pulls in
`Lean.ofReduceBool` and is a hard fail. Every numeric fact must be a proof,
not a computation the kernel is asked to trust.
