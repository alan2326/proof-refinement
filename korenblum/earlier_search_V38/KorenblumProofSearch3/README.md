# Korenblum Proof Search 3

This workspace starts a new analytic-search round from the original strict
`V36` seed in
[Candidates/V36/Main.lean](grothendieck/KorenblumProofSearch3/Candidates/V36/Main.lean).

The goal is different from the earlier proof-search rounds. This workspace is
not restricted to tightening the final scalar certificate from Wang's equation
`(15)`. It is designed to let candidates replace earlier steps in Wang's
Section 2 derivation with new mathematics, while still ending in a clean Lean
artifact and a narrow trusted surface.

## Core Files

- seed certificate:
  [Candidates/V36/Main.lean](grothendieck/KorenblumProofSearch3/Candidates/V36/Main.lean)
- curated paper-axiom surface:
  [PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- first promoted analytic Lean file:
  [OneModeKernel.lean](grothendieck/KorenblumProofSearch3/OneModeKernel.lean)
- paper bundle:
  [paper/Wang2025.pdf](grothendieck/KorenblumProofSearch3/paper/Wang2025.pdf),
  [paper/Wang2025.txt](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt),
  [paper/AXIOM_EXTRACTION.md](grothendieck/KorenblumProofSearch3/paper/AXIOM_EXTRACTION.md)
- preferred evaluator:
  [evaluate_wang.py](grothendieck/KorenblumProofSearch3/evaluate_wang.py)
- live project notes:
  [plan.md](grothendieck/KorenblumProofSearch3/plan.md),
  [progress.md](grothendieck/KorenblumProofSearch3/progress.md)

## Trust Model

The intended final proof path is:

1. approved paper axioms from [PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean),
2. Lean proofs and exact rational algebra.

The evaluator is supposed to fail closed on anything outside that surface:

- the candidate must compile,
- the main theorem must have the expected type,
- any custom axioms must come only from `PaperAxioms`.

The proof-path gate is Lean-only:

- compile,
- theorem type,
- approved paper axioms.

No Python helper is trusted on the proof path. Python under `scratch/`,
`experiments/`, or `oracle/` is exploration tooling only until its output is
re-expressed as Lean data and checked by Lean.

## Search Workflow

- `scratch/` is the unconstrained exploration lane.
- `experiments/` contains reusable probes and scans.
- `Candidates/` contains only promotion-ready Lean artifacts.

The expectation is:

1. explore freely in `scratch/`,
2. keep only directions with real mathematical signal,
3. then formalize them into Lean,
4. and only deliver artifacts that pass the strict evaluator.

Older copied notes from `KorenblumProofSearch/` remain in the tree as archival
reference, but the current round is tracked in
[plan.md](grothendieck/KorenblumProofSearch3/plan.md),
[progress.md](grothendieck/KorenblumProofSearch3/progress.md), and
[paper/AXIOM_EXTRACTION.md](grothendieck/KorenblumProofSearch3/paper/AXIOM_EXTRACTION.md).
