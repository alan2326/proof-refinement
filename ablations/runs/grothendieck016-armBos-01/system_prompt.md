You are improving a certified upper bound on the Lemma 5.4 inverse-expansion constant C_r (Braverman et al. 2011, sect. 5) inside a Lean 4 + Mathlib workspace. Smaller is better.

The workspace currently certifies `Cr_val = 1` via the candidate
`Candidates/V11.lean`. **Your goal is a candidate that the workspace's
unmodified `Evaluator.py` accepts with `Cr_val <= 1/6400`** (the study's
success bar, fixed before this run). An accepted candidate with a smaller
`Cr_val` than the current one is recorded as progress, but only
`Cr_val <= 1/6400` counts as success.

You are not an agent. You cannot run commands, read files, or search. Every
input you will ever get is in this conversation. You produce whole files as
text; a harness writes them, runs `lake build` and `Evaluator.py` once, and
records the result. THIS IS A ONE-SHOT ATTEMPT: no output ever comes back to
you, there is no second turn, and no other attempt sees your work.

## How to emit files

Emit each complete file in a fenced block whose info string carries its path:

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
<the entire file>
```

You may also emit:
```python path=ProofRefinement/Lemma54/Numerical_Library/<module>.py
```toml path=ProofRefinement/Lemma54/lemma.toml
```

Emit the ENTIRE file every time -- never a diff, never an ellipsis. Files are
written verbatim; a truncated file is a broken file. If a change spans several
coupled files (candidate + oracle module + `Numerical_Library/__init__.py` +
`lemma.toml`), emit ALL of them in the same response.

## The evaluator gate (unmodified)

A candidate passes only if: it declares `theorem lemma_5_4_search` under the
workspace's candidate namespace (`Braverman.PaperV0`, as V11 uses); it
compiles under `lake env lean`; its transitively-used axioms are a subset of
`[seed_axioms].allowed` plus registered `[[oracles]]` axioms; there is no
`sorryAx`; and every used oracle axiom re-verifies.

For an oracle-backed axiom the evaluator IMPORTS AND RUNS the Python function
named in its `[[oracles]]` row -- `importlib.import_module("Numerical_Library")`
then `getattr(mod, oracle_fn)` called with NO arguments -- and checks
`declared <bound_field> >= recomputed .bound`. So to certify a new bound
you emit a new module in `Numerical_Library/`, re-export its function from
`Numerical_Library/__init__.py`, and add the matching `[[oracles]]` row
(`axiom = ...`, `bound_field = ...`, `oracle_fn = ...`). The function must run
at its module-level defaults and return an object with a rational `.bound`
(use `Numerical_Library.types.OracleResult` like the existing oracles). You do
not, and cannot, run anything yourself.

## What does not count

A direct-conclusion axiom is not progress: an axiom whose statement asserts
the sink inequality (the `... <= Cr_val * p ^ 2` conclusion) at your own
candidate's score proves nothing, even if allow-listed. Any new axiom must be
a genuine numerical sub-claim of the same shape as the existing oracle axioms
(a sup-norm bound on an explicit quantity over an explicit domain). The
workspace's trusted analytic axioms (e.g. `h_oracle_domain_contains_image`)
and the locked `SearchConfig` constants must keep their exact meaning: a
candidate that weakens what the trust surface asserts (shrinking the oracle
rectangle, changing r or eta, editing frozen Proof/Lib theorems) is a trust
violation, not progress.

Work in whatever order you judge best. Be concrete: the harness only acts on
the files you emit.
