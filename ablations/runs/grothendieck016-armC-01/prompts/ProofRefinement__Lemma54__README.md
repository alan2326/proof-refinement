# Agent brief — Grothendieck K_G, Arm C'' (partial formalization ablated)

## The contract

`Proof/CandidateContract.lean` defines, against Mathlib only:

* `GrothendieckIneq K` — the Grothendieck inequality at constant `K`: for
  every finite real matrix `A` and unit vectors in any real Hilbert space,
  some sign vectors achieve at least `(1/K)` of the SDP value;
* `KrivineBound = π / (2·log(1+√2)) ≈ 1.7822139781` — the previous state
  of the art;
* `GrothendieckIneq.mono` — upward monotonicity in `K` (proven);
* `KrivineBound_le_seed : KrivineBound ≤ 1782214/1000000` — a kernel-checked
  numeric certificate.

There is **no** IFT / analytic-inverse apparatus, **no** Lemma 5.4, **no**
rounding-scheme chain and **no** numerical oracle.

## The task

`Candidates/V0.lean` asserts the previous state of the art as one axiom at
the exact real:

```lean
axiom hKrivine : GrothendieckIneq KrivineBound
```

and evaluates at the rational ceiling `K_val = 1782214/1000000`.

Ship a candidate `Candidates/V<N>.lean` whose `grothendieck_bound_search`
proves `GrothendieckIneq K_val` for some rational
`K_val < 1782214/1000000` (smaller is better), and which the evaluator
accepts.

**What counts as a real advance.** By monotonicity, any rational
`K_val ≥ KrivineBound` is derivable from the seed by tightening the numeric
certificate (better rational endpoints for √2, log, π). Such candidates are
accepted by the gate and logged as progress, but the study scores them as
*re-certifications of the known frontier*, *not* as an improvement of the
Grothendieck constant. **Success for this arm means a certified
`K_val < KrivineBound`** — mathematics strictly beyond the published state
of the art (e.g. via an improved rounding scheme, as Braverman et al. did
for the exact constant). Spend your budget accordingly.

## What you have

* Mathlib, in full.
* Braverman–Makarychev–Makarychev–Naor (2011), at `Braverman2011.pdf` and
  `Braverman2011.txt` in this directory (also `assets/pdf/braverman.pdf`).
* Web search and web fetch.
* The Lean LSP and Lean search MCP tools.
* The standard harness: sprint contracts, `Refinement_Log/`, `Bulletin.md`,
  `Experience.md`, `Proposals/`, `Evaluator.py`, `scripts/`.

Building whatever Lean apparatus you need — including a partial
formalization of your own design — is **in scope and expected**.

## What does not count as progress

The evaluator gate: a candidate passes only if it compiles, its sink theorem
type-checks against `GrothendieckIneq K_val` exactly, its audited axiom set
is a subset of `[seed_axioms].allowed` (plus registered oracles), there is no
`sorryAx`, and `K_val` strictly improves on (is less than) the parent.

**A direct-conclusion axiom at a smaller `K` is not progress.** Adding, say,

```lean
axiom h : GrothendieckIneq (17 / 10)
```

and registering it in `[seed_axioms].allowed` would satisfy the letter of the
gate while asserting exactly the thing to be proved. Do not do this. If you
introduce a new axiom it must be a genuine sub-claim — strictly weaker than
the conclusion — and you must say in the sprint contract why it is weaker.

If you introduce a numerical sub-claim, register it as an `[[oracles]]` row
with a wrapper the evaluator can recompute (a function exported from a
`Numerical_Library/` package you create, returning an object with a rational
`.bound`), exactly as a with-PF workspace does.

## Evaluator

```
uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V<N>.lean
```

Build first: `lake build ProofRefinement.Lemma54.Candidates.V<N>`.
