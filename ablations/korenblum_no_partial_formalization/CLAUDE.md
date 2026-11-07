# Korenblum (noPF arm)

Standalone Lean 4 search workspace for the Korenblum constant. **No partial
formalization.** This is the ablation arm of the Korenblum harness experiment.
The sibling arm (with partial formalization) lives at `korenblum/`.

The active search workspace lives in `ProofRefinement/Korenblum/`. See
`ProofRefinement/Korenblum/AGENT_BRIEF.md` for the contract and rules.

## Build

```bash
lake build              # builds ProofRefinement
lake build ProofRefinement.Korenblum.Candidates.V0
```

Lean 4 v4.28.0 with Mathlib v4.28.0.

## Workspace import policy

The candidate-side evaluator enforces `lemma.toml:[workspace_import_policy]`.
In this arm the trusted external surface is **empty** — no `KorenblumPaper.*`
modules exist here. Only `ProofRefinement.Korenblum.*` and `Mathlib.*`
prefixes are admitted. Any expansion must be filed as a `Proposals/` entry
first.
