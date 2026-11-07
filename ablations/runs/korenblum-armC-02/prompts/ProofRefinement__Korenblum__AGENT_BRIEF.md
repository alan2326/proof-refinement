# Agent brief — Korenblum, Arm C (partial formalization ablated)

## The contract

`Proof/CandidateContract.lean` defines, against Mathlib only:

* `UnitDisk : Set ℂ` — the open unit disk;
* `bergmanNormSq f = ∫_𝔻 ‖f z‖² dA` — the squared Bergman A² seminorm;
* `ValidKorenblumBound c` — the function-level Korenblum maximum principle:
  for all analytic, A²-integrable `f, g` on `𝔻`, if `‖f z‖ ≤ ‖g z‖` whenever
  `c < ‖z‖ < 1`, then `bergmanNormSq f ≤ bergmanNormSq g`.

There is **no** coefficient-level intermediate, **no** Wang Section 2
hypothesis bundle, **no** equation chain and **no** numerical oracle.

## The task

`Candidates/V0.lean` asserts the previous state of the art as one axiom:

```lean
axiom hKorenblum_prev : ValidKorenblumBound ((35646 / 100000 : ℝ))
```

Ship a candidate `Candidates/V<N>.lean` whose `korenblum_constant_search`
proves `ValidKorenblumBound c_value` for some rational
`c_value > 35646/100000`, and which the evaluator accepts.

## What you have

* Mathlib, in full.
* Wang (2025), at `Wang2025.pdf` and `Wang2025.txt` in this directory.
* Web search and web fetch.
* The Lean LSP and Lean search MCP tools.
* The standard harness: sprint contracts, `Refinement_Log/`, `Bulletin.md`,
  `Experience.md`, `Evaluator.py`, `scripts/`.

Building whatever Lean apparatus you need — including a partial formalization
of your own design — is **in scope and expected**.

## What counts as progress

The evaluator gate is unchanged. A candidate passes only if it compiles,
type-checks, its audited axiom set is a subset of `[seed_axioms].allowed`
(plus registered oracles), there is no `sorryAx`, and `c_value` strictly
improves on the parent.

**A direct-conclusion axiom at a larger `c` is not progress.** Adding, say,

```lean
axiom h : ValidKorenblumBound (36 / 100)
```

and registering it in `[seed_axioms].allowed` would satisfy the letter of the
gate while asserting exactly the thing to be proved. Do not do this. If you
introduce a new axiom it must be a genuine sub-claim — strictly weaker than
the conclusion — and you must say in the sprint contract why it is weaker.

If you introduce a numerical sub-claim, register it as an `[[oracles]]` row
with a wrapper the evaluator can recompute, exactly as the with-PF workspace
does.

## Halting

If you judge the task infeasible within the sprint budget, say so explicitly
in the sprint contract and in `Bulletin.md`, with the specific obstruction.
A precise, well-evidenced negative result is a legitimate outcome and is more
useful than a shortcut.
