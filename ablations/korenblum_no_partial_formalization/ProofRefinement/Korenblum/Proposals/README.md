# Proposals — Korenblum human-approval queue

Use this directory only for trust-base expansions that should **not** be done
inline by a sprint generator.

## Use a proposal for

- a new free-floating analytic axiom
- a significant statement reformulation
- a large library/import move that needs human review

## Do not use a proposal for

- ordinary candidate edits
- routine proof refactors
- new oracle registry entries that are already fully specified and directly
  consumed by the current sprint

Those oracle-shaped additions can be done inline as long as the sprint contract
explicitly asks for the new `Numerical_Library` function, the matching
`lemma.toml` entry, and the Lean-facing axiom/use site.

## Status values

- `pending`
- `approved`
- `rejected`
- `superseded`

Keep at most 3 pending proposals at once.

## Naming

`proposal_<NNN>_<slug>.md`
