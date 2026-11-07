# proposal_<NNN>_<slug>

**Status:** pending | approved | rejected
**Filed by:** sprint_<NNN> planner
**Kind:** import-policy | contract-restatement | hoist-derived-theorem

## Request

Exactly what should change, in one or two sentences. Name the module, the
declaration, or the contract clause precisely.

## Tried hard and failed

Which sprint attempted the blocked route, what it tried (tactic families, search
terms, intermediate lemmas), and the exact goal it stopped on. Link the
`Experience.md` entry and any `Scratch/` artefacts.

## Why this cannot be a Lean sprint instead

The argument that the derivation cost is genuinely large, or that a required
Mathlib API does not exist. Be specific about what is missing.

## Why the mathematics is not in doubt

Numerical witness, derivation sketch, or reduction from a known result. If the
mathematical truth is uncertain, withdraw this and queue a sprint to pin it down.

## Why it moves the score

The specific quantitative gap this closes, and the score you expect it to unlock.

## For import-policy requests only

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  <module> --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi
```

Paste the output. A clean closure is necessary but not sufficient — say also why
the module's *content* does not simply hand over a π bound.

## Immediately runnable sprint queued alongside

`sprint_<NNN>_<slug>.md` — what the loop does while this proposal waits.

## Human decision

_(left blank by the planner)_
