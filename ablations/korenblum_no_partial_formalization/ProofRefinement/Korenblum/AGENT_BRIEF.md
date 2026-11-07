# Refining the Korenblum Constant — agent brief (noPF arm)

You are working in the **no-partial-formalization** ablation arm of the
Korenblum harness. The goal is to produce candidates with a **larger valid
lower bound** `c_value`. Score is `c_value`, larger is better.

## What is different in this arm

This workspace deliberately strips Wang's Section 2 partial formalization.
There is no `KorenblumPaper/`, no Wang Section 2 hypothesis bundle, no
equation chain (no Eq2…Eq15), no oracle infrastructure, and no
`Numerical_Library`. The candidate contract is stated directly at the
function-level Bergman A² Korenblum max principle.

## Current state

- The candidate contract is
  `theorem korenblum_constant_search : ValidKorenblumBound c_value`.
- `ValidKorenblumBound c` is defined in
  [Proof/CandidateContract.lean](ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/CandidateContract.lean)
  as the function-level statement: for every analytic, A²-integrable
  `f, g : ℂ → ℂ` with `‖f‖ ≤ ‖g‖` on the outer annulus `c < ‖z‖ < 1`,
  the integrals satisfy `∫_𝔻 ‖f‖² ≤ ∫_𝔻 ‖g‖²`.
- The seed `V0` proves `ValidKorenblumBound (3554/10000)` using one seed
  axiom, `hKorenblum_published_3554`, asserting the entire Korenblum max
  principle at `c = 0.3554` (Wang 2025).
- The trusted external surface (per `lemma.toml:[workspace_import_policy]`)
  is empty. Only `Mathlib.*` and `ProofRefinement.Korenblum.*` modules may
  be imported.

## Objective

- `score = c_value`, **larger is better**.

A candidate is an improvement if it proves
`ValidKorenblumBound c_value` for a strictly larger rational `c_value`,
through any honest Lean route.

## Local-Only Rule

Treat `ablations/korenblum_no_partial_formalization/` as the active workspace.

- Do not read, search, or inspect files outside this directory unless the
  human explicitly tells you to.
- Do not look at the sibling `korenblum/` workspace — it is
  the *other* arm of the ablation experiment and reading it would corrupt
  the comparison.
- Use the import policies in `lemma.toml` as a backstop, not as permission
  to browse the rest of the host filesystem.
- The folder-local harness wiring counts as part of this workspace:
  `.claude/skills/run-next-korenblum-sprint/SKILL.md`,
  `.claude/agents/korenblum-refinement-*.md`,
  `.claude/settings.local.json`,
  `docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md`,
  `scripts/korenblum_*.sh`.

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

- standard Lean / compiler axioms (`propext`, `Classical.choice`, etc.),
- `hKorenblum_published_3554`, the single paper-faithful axiom asserting
  the full Korenblum max principle at `c = 0.3554`.

Compared to the with-PF arm, this is a structurally bigger trust leaf:
the entire Korenblum theorem at one `c`, rather than a single paper-faithful
sub-claim with the rest of Wang's chain formalized in Lean.

## Numerical tooling

There is no `Numerical_Library/` in this arm. The Bergman-level contract
has no natural numerical sub-claim. If a future sprint introduces a
self-developed partial formalization (and a corresponding numerical
sub-claim), it would create a `Numerical_Library/` directory and register
an `[[oracles]]` entry then. By default, no such tooling exists here.

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
- autonomous repetition is host-driven via
  `/loop 30m /run-next-korenblum-sprint`,
- `scripts/korenblum_checkpoint_loop.sh` is only a periodic checkpoint
  loop, not an agent-spawn loop.
- `scripts/korenblum_lake_build.sh` and
  `scripts/korenblum_eval_candidate.sh` are the folder-local wrappers
  for candidate build / evaluator runs.

## High-value directions

In rough order of preference:

1. **Prove `ValidKorenblumBound c_value` at a larger `c` directly against
   Mathlib.** This requires building enough Bergman A² / annulus
   pseudohyperbolic / boundary-comparison machinery in Lean to push the
   bound. Hard, but the only path that improves the *science* — every
   step you formalize in Lean removes a piece of trust.
2. **Build a per-candidate partial formalization on top of Mathlib.**
   Re-derive a Wang-style or alternative reduction in Lean, attached to
   a candidate `V<N>` and used to prove `ValidKorenblumBound c_value` at
   a higher `c` from a smaller axiomatic leaf. This is allowed (and the
   tools for it exist — derived-theorem files under `Candidates/V<N>/`,
   per-mode reductions, etc.). It rebuilds, in Lean, what was stripped.
3. **Add a new direct-conclusion axiom at higher `c`** (i.e., another
   `hKorenblum_published_X : ValidKorenblumBound c'`). Mechanically
   allowed if listed in `[seed_axioms].allowed`, but does not advance
   the science — it just postulates the answer. Flag this in
   `Bulletin.md` if attempted.

The ablation question this workspace exists to answer: *without
partial formalization, does the agent still find verifiable improvements,
or does it stagnate / shortcut?* Both behaviours are informative; please
record what you do and why.

## Generator capability

The generator is competent at multi-hundred-line Lean proofs over
Mathlib's complex-analysis, ℓ²-summability, boundary-integral, and
measure-theory APIs. In scope:

- Cauchy–Schwarz on boundary integrals,
- Parseval / boundary L² expansions on analytic functions,
- termwise summability and `tsum`-level rearrangements,
- bridging pointwise modulus inequalities to boundary integrals,
- subharmonicity / mean-value arguments for `|f|²`,
- Lebesgue-integral monotonicity on annulus regions,
- `nlinarith` / `polyrith` / `field_simp` / `ring` chains hundreds of
  lines long.

If a planner cannot enumerate three distinct Lean-derivation directions
for an analytic claim, the obstruction is structural, not capability —
and that fact must be demonstrated by an attempted generator sprint, not
assumed. The correct prior is "this is provable in Lean, the question
is which lemma family unlocks the shortest proof."

## Creating per-candidate derived-theorem files

When a sprint needs intermediate algebraic / analytic handles, prove
them in derived-theorem files scoped to the candidate version you are
shipping. If the sprint ships `Candidates/V<N>.lean`, create derived
files under `Candidates/V<N>/`. Pick names that reflect what the file
contains.

Rules for per-candidate derived-theorem files:

- the file contains `theorem`s (or `lemma`s), never new `axiom`s,
- proofs draw only on Mathlib and on already-pinned modules in
  `lemma.toml:[workspace_import_policy]`,
- if a new module path is needed, add it to
  `[workspace_import_policy]` in the same sprint (this is a Lean-side
  derivation, not a trust expansion),
- the file is imported only by `Candidates/V<N>.lean` (or by other
  files under `Candidates/V<N>/`).

If a derived theorem is genuinely useful across multiple future
candidates, propose hoisting it via a sprint contract; do not hoist
unilaterally. The default is per-candidate scope.
