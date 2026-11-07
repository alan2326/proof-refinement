# Refining the Korenblum Constant — agent brief

You are refining a formal Lean proof search workspace for the Korenblum
constant. The goal is to produce candidates with a **larger valid lower bound**
`c_value`.

## Current state

- The fixed paper-facing surface comes from `KorenblumPaper.PaperAxioms`.
- The currently trusted external Lean modules are pinned by
  `lemma.toml:[workspace_import_policy]`.
- The candidate contract is
  `theorem korenblum_constant_search : ValidKorenblumBound c_value`.
- `ValidKorenblumBound` is defined in
  [Proof/CandidateContract.lean](korenblum/ProofRefinement/Korenblum/Proof/CandidateContract.lean).
- `Section2Assumptions` is available as an ordinary imported structure from the
  paper surface, not as a globally trusted axiom.
- The seed `V0` proves the final Korenblum bound at `c = 0.3554` using one
  seed axiom asserting Wang's equation `(15)` at that value.

## Objective

Unlike the Lemma 5.4 workspace, the score is not a loss constant to minimize.
Here:

- `score = c_value`
- **larger is better**

Any candidate that proves a valid final theorem for a larger rational `c_value`
is an improvement.

The search space is the full space of proofs of
`ValidKorenblumBound c_value`. The current `(15)` reduction is only one seed
path, not a global restriction.

## Local-Only Rule

Treat `ProofRefinement/Korenblum/` as the active workspace.

- Do not read, search, or inspect files outside this directory unless the human
  explicitly tells you to.
- Do not look at prior Korenblum search runs, old candidates, or sibling proof
  search folders.
- Use the import policies in `lemma.toml` as a backstop, not as permission to
  browse the rest of the repository.
- The folder-local harness wiring counts as part of this workspace:
  `.claude/skills/run-next-korenblum-sprint/SKILL.md`,
  `.claude/agents/korenblum-refinement-*.md`,
  `.claude/settings.json`,
  `docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md`,
  and `scripts/korenblum_*.sh`.

## Rules

1. The sink theorem name is fixed: `korenblum_constant_search`.
2. The constant def name is fixed: `c_value`.
3. The theorem type is fixed by `ValidKorenblumBound c_value`.
4. Direct candidate imports are restricted by `lemma.toml:[import_policy]`.
5. All workspace `.lean` imports are restricted by
   `lemma.toml:[workspace_import_policy]`.
6. `sorryAx` is a hard fail.
7. Any new axiom must be either:
   - already allowed in `lemma.toml:[seed_axioms].allowed`, or
   - registered as an oracle in `lemma.toml:[[oracles]]`.

## Seed trust surface

The initial seed allows:

- standard Lean/compiler axioms,
- `hEq15_seed_3554`, the single paper-faithful scalar-check axiom.

The bundled `KorenblumPaper.*` modules are Lean theorems and structures, not
global axiom declarations.

## Numerical tooling

Numerical search code lives under `Numerical_Library/`. The evaluator can call
registered wrapper functions from that package, including submodule functions,
but no `[[oracles]]` entries are registered in `lemma.toml` yet. Future sprints can
add those entries inline when there is a clear Lean-facing oracle statement to
certify and the sprint contract names the required `Numerical_Library`
function, `lemma.toml` entry, and Lean-facing axiom/use site. Use
`ProofRefinement/Korenblum/Proposals/` only for non-oracle trust-base
expansions.

## Workflow

```bash
bash scripts/korenblum_lake_build.sh Candidates/V0.lean
bash scripts/korenblum_eval_candidate.sh Candidates/V0.lean
```

Useful flags:

- `--skip-compile`
- `--skip-oracle`
- `--no-log`

## If you are running inside the harness

If this brief is being read by the driver skill
`run-next-korenblum-sprint` or by a Korenblum sub-agent
(`korenblum-refinement-planner`, `korenblum-refinement-generator`, or
`korenblum-refinement-evaluator`), the Korenblum harness document at
`docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md` applies on top of the rules
above.

Most importantly:

- one end-to-end harness sprint is `/run-next-korenblum-sprint`,
- autonomous repetition is host-driven via `/loop 30m /run-next-korenblum-sprint`,
- `scripts/korenblum_checkpoint_loop.sh` is only a periodic checkpoint loop,
  not an agent-spawn loop.
- `scripts/korenblum_lake_build.sh` and
  `scripts/korenblum_eval_candidate.sh` are the folder-local wrappers for
  candidate build/evaluator runs.

## High-value directions

1. Prove `ValidKorenblumBound c_value` at a larger `c`, by any route.
2. Replace the seed `(15)` axiom with a stronger certified or fully proved
   argument.
3. Prove a stronger direct reduction than the current seed bridge.
4. Introduce oracle-backed numeric subclaims only when they support a real Lean
   theorem that pushes `c_value` upward.

## Generator capability — read this before exiting BLOCKED

The generator is competent at multi-hundred-line Lean proofs over
Mathlib's complex-analysis, ℓ²-summability, boundary-integral, and
measure-theory APIs. Concretely in scope:

- algebraic identities on complex sequences (e.g. Wang's lift
  identity `(1 − a²)(|b_k|² − |a_k|²) = |b_k − a·a_k|² − |a_k − a·b_k|²`),
- termwise applications of Wang Lemma 2 (the boundary-L²
  expansion),
- Cauchy–Schwarz on boundary integrals,
- termwise summability and `tsum`-level rearrangement arguments,
- bridging pointwise modulus inequalities to coefficient-level
  bounds via Lemma 2,
- induction on `ℕ`, case splits on `n1Pred` / `n2Pred`,
- `nlinarith` / `polyrith` / `field_simp` / `ring` chains hundreds
  of lines long.

If a planner cannot enumerate three distinct Lean-derivation
directions for an analytic claim, the obstruction is structural,
not capability — and that fact must be demonstrated by an attempted
generator sprint, not assumed. Default agent dispositions
systematically underestimate analytic-Lean capacity; the correct
prior is "this is provable in Lean, the question is which lemma
family unlocks the shortest proof."

## Creating derived-theorem files under `Candidates/V<N>/`

Wang's published derivations contain un-numbered intermediate
algebraic steps (the lift identity, per-k cross-coupling
positivity, K(c, ρ) extraction, the boundary L² comparison from
`|f| ≤ |g|`, etc.). These are not bundled fields on
`Section2Assumptions` and they should not become bundled fields —
they are derivable from existing fields plus Mathlib, often by a
few lines of `ring` / `nlinarith` / `intervalIntegral.integral_mono`
work.

When a sprint needs such a handle, **prove it in a derived-theorem
file scoped to the candidate version you are shipping**. Concretely:
if the sprint ships `Candidates/V<N>.lean`, create derived-theorem
files under `Candidates/V<N>/`. Examples: `Candidates/V53/Lift.lean`,
`Candidates/V53/BoundaryCompare.lean`, `Candidates/V53/Intermediates.lean`.
Pick a name that reflects what the file contains; group related
intermediates in one file rather than fragmenting.

Rules for per-candidate derived-theorem files:

- the file contains `theorem`s (or `lemma`s), never new `axiom`s
  and never new `Section2Assumptions` fields,
- proofs draw only on existing `Section2Assumptions` fields,
  `KorenblumPaper.*` modules already pinned in
  `lemma.toml:[workspace_import_policy]`, and Mathlib,
- if a new module path is needed, add it to
  `[workspace_import_policy]` in the same sprint (this is not a
  trust expansion — the file is Lean theorems on top of the
  existing trusted surface),
- the file is imported only by `Candidates/V<N>.lean` (or by other
  files under `Candidates/V<N>/`), never by `KorenblumPaper/`,
  `Proof/`, or other candidates,
- the file does not modify the bundle, does not introduce
  alternative paper content, and does not edit anything under
  `KorenblumPaper/` — that directory is the trusted paper surface
  and is read-only for the generator.

If a derived theorem is genuinely useful across multiple future
candidates, propose hoisting it to a shared location in a sprint
contract; do not hoist unilaterally. The default is per-candidate
scope.

Default disposition: when proposal_003-shaped requests come up
(intermediate Wang derivation step needed), the answer is "prove
it in Lean in a per-candidate derived-theorem file," not "file a
proposal." The planner should queue an analytic Lean sprint
targeting the downstream improvement (e.g. a tightened
(15)-shaped inequality); the generator, while attempting that
sprint, creates the per-candidate derived-theorem files as needed
and uses them. One sprint, one derivation chain, no proposal.
