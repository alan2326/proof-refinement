# pi_polygon — build commands and policy summary

A persistent Lean 4 proof-refinement loop that minimizes the width of a certified
interval around π derived from the Archimedean inscribed polygon.

Agents working in the refinement loop: your entry point is
[`ProofRefinement/PolygonPi/START_HERE.md`](ProofRefinement/PolygonPi/START_HERE.md),
then [`AGENT_BRIEF.md`](ProofRefinement/PolygonPi/AGENT_BRIEF.md). Read those
rather than inferring the rules from this file.

## Build

```bash
lake build PolygonCore                                  # trusted problem statement
lake build ProofRefinement                              # trusted contract + V0
lake build ProofRefinement.PolygonPi.Candidates.V0      # one candidate
```

Mathlib is vendored, pre-built, and pinned (`v4.28.0`, commit `8f9d9cff`). A build
should take seconds. **If lake starts recompiling Mathlib, stop and investigate** —
something has changed the toolchain or the manifest, and the fix is not to wait it
out.

## Evaluate

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V0            # logs
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V0 --no-log   # does not
./ProofRefinement/PolygonPi/scripts/polygonpi_harness_preflight.sh            # loop health
./ProofRefinement/PolygonPi/scripts/verify_all.sh                            # full replay
python3 results/summarize.py                                                 # human-side report
```

## Import policy — enforced three ways

Allowed prefixes: `Mathlib`, `ProofRefinement.PolygonPi`, `PolygonCore`.

Blocked: bare `import Mathlib`, and anything under `Mathlib.Analysis.Real.Pi`.
The block is **transitive** — some innocent-looking modules reach it, e.g.
`Mathlib.Analysis.SpecialFunctions.Stirling` imports `Pi.Wallis`. Check first:

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py <module> \
  --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi
```

Beyond policy, those five Mathlib modules have been **physically deleted** from
this checkout along with their build artifacts and the root `Mathlib.olean`, so
both the mega-import and any direct `Pi.*` import fail to resolve. Pre-deletion
hashes are in `environment/stripped_modules.txt`. This is deliberate: rebuilding
π's numerical bounds is the exercise.

Note this Mathlib is the Lean 4.28 **module-system** tree — its sources say
`public import M`, not `import M`. Our own files use plain `import`.

## Trust surface

Zero project axioms, zero numerical oracles. Every candidate's axiom closure must
be a subset of `{propext, Classical.choice, Quot.sound}`, which also rules out
`native_decide`. `PolygonCore/` and `ProofRefinement/PolygonPi/Proof/` are the
read-only human-provided surface; they fix the problem statement and contain no
estimate of any kind.

## Do not read

`validation-private/` and `results/` are human-only. They are off-limits to every
agent in the loop, denied in `.claude/settings.local.json`, and
`validation-private/` is gitignored. Reading either invalidates the run — so if
you find yourself curious about what is in them, that is the signal to stop, not
to look.

## Repo

`.lake/` and `validation-private/` are gitignored. The vendored Mathlib is 6.9 GB
and is never committed.
