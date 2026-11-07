# Korenblum

Standalone Lean 4 search workspace for the Korenblum constant.

The trusted paper surface lives in `KorenblumPaper/` (theorem/structure files
formalizing Wang 2025 Section 2; zero free axioms inside the cone).

The active search workspace lives in `ProofRefinement/Korenblum/`. See
`ProofRefinement/Korenblum/AGENT_BRIEF.md` for the contract and rules.

## Build

```bash
lake build              # builds KorenblumPaper + ProofRefinement
lake build ProofRefinement.Korenblum.Candidates.V0
```

Lean 4 v4.28.0 with Mathlib v4.28.0.

## Workspace import policy

The candidate-side evaluator enforces `lemma.toml:[workspace_import_policy]`,
which currently allows imports of:

- `KorenblumPaper.PaperAxioms`
- `KorenblumPaper.PaperEq15`
- `KorenblumPaper.OneModePaperBridge`

Plus anything under the `ProofRefinement.Korenblum.*` and `Mathlib.*` prefixes.
Any expansion must be filed as a `Proposals/` entry first.
