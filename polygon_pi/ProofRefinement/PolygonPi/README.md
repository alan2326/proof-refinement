# Polygon-π proof refinement workspace

A persistent Lean 4 proof-refinement loop that minimizes the width of a
certified interval around π derived from the Archimedean inscribed polygon.

New here? Read [`START_HERE.md`](START_HERE.md), then
[`AGENT_BRIEF.md`](AGENT_BRIEF.md).

## Layout

```
ProofRefinement/PolygonPi/
├── START_HERE.md          local-only rule, first reads, first checks
├── AGENT_BRIEF.md         the contract, the rules, the capability note
├── Bulletin.md            frontier, incumbent, standing human priorities
├── Experience.md          append-only notebook: what was tried, what failed
├── lemma.toml             contract + policies + score configuration
├── Evaluator.py           the twelve-stage checker and scorer
├── Proof/                 TRUSTED, read-only
│   ├── Surface.lean           re-export of PolygonCore
│   ├── CandidateContract.lean ValidPolygonBound, ValidPolygonBoundAt
│   ├── FixedDepth.lean        certified_polygon_interval (the reported theorem)
│   └── Main.lean              the one module candidates import
├── Candidates/            V0.lean, V1.lean, … and per-candidate V<N>/ dirs
├── Proposals/             policy/contract change requests (narrow scope)
├── Refinement_Log/        log.jsonl + verdict_<sprint>.md
├── Scratch/               sprint_<NNN>/ working space
├── Sprint_Contracts/      TEMPLATE.md + sprint_<NNN>_<slug>.md
├── docs/                  the harness design document
└── scripts/               preflight, build, eval, reset, checkpoint, closure
```

The trusted problem statement lives one level up, in `PolygonCore/`, and is
read-only to every agent.

## The loop

One sprint = one bounded unit of work:

```
preflight → planner writes a contract → generator executes it
         → evaluator runs the gates and writes a verdict → Bulletin line
```

Driven by `/run-next-polygonpi-sprint`, and autonomously by
`/loop /run-next-polygonpi-sprint` with no interval — the next sprint starts when
the previous one finishes. Halt conditions live in preflight, not in a timer.

## Commands

```bash
# build a candidate
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V0

# evaluate a candidate (add --no-log to avoid touching the frontier)
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V0 --no-log

# is the harness healthy enough to run another sprint?
./ProofRefinement/PolygonPi/scripts/polygonpi_harness_preflight.sh

# check an import for transitive leaks before relying on it
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  Mathlib.Analysis.Calculus.MeanValue \
  --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi

# human-side reporting
python3 results/summarize.py
```

## Trust surface

Zero project axioms, zero numerical oracles. Every candidate's axiom closure must
be a subset of `{propext, Classical.choice, Quot.sound}`, which also rules out
`native_decide`. "Partial formalization" here means only that a small read-only
human-provided Lean surface fixes the problem statement; every line of the
refinement is agent-supplied and fully verified.

## Isolation

Mathlib's own numerical π machinery is unavailable three ways: policy (direct and
transitive import blocks), a static forbidden-name scan, and physical deletion of
`Mathlib/Analysis/Real/Pi/` from this checkout — which also makes bare
`import Mathlib` fail to resolve. See `docs/POLYGONPI_PROOF_REFINEMENT_HARNESS.md`
§isolation and `environment/stripped_modules.txt`.

The classical Archimedes argument is famous and certainly present in model
weights. This is a **transfer and formal-certificate recovery** task, not a
held-out discovery benchmark, and the artifact says so plainly.
