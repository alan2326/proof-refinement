# Proposal <NNN>: <one-line title>

**Created**: <YYYY-MM-DD HH:MM> by Planner (sprint_<NNN> context)
**Status**: pending  <!-- pending | approved | rejected | superseded -->
**Type**: <new-oracle | new-axiom | new-mathlib-import | other>

## What's needed (precise, mechanically actionable)

<Concrete and detailed: the human must be able to act on this
without re-deriving the design.>

- **File:** <e.g. `ProofRefinement/Lemma54/Numerical_Library/m_diff.py`>
  - <function signature, expected return type, decisional inputs>
- **lemma.toml entry** (if new oracle):
  ```toml
  [[oracles]]
  short = "h_M_diff_oracle"
  axiom_fq = "Braverman.PaperV0.h_M_diff_oracle"
  bound_field = "M_diff_val"
  oracle_fn = "compute_M_diff"
  ```
- **Axiom declaration** (if new axiom):
  ```lean
  -- in Proof/Lib/Lemma54_Paper.lean
  axiom h_M_diff_bound : ∀ p : ℂ, …
  ```
- **Supporting Mathlib imports** (if needed):
  - `import Mathlib.Foo.Bar`

## Mathematical content (≤ 6 sentences)

<What does the new infrastructure assert mathematically? For
oracles, write the statement the oracle's bound supports. For
axioms, write the theorem statement and cite a published proof if
one exists.>

## Win unlocked (numerical, must include Scratch/ output)

<Cite the specific Scratch/ run that quantifies the win. Format:
"At the current state (Cr_val = X), if this proposal is approved
and the follow-up sprint queues `<direction>`, then Cr_val drops
to Y, a Z× reduction. Scratch/sprint_<NNN>_planner_<topic>.py
output: <key numbers>."

For axiom-count or other non-Cr_val wins, state the corresponding
metric. For purely-enabling proposals (where the win is "this
unblocks a new axis"), state which axis and what its expected
score impact is.>

## Risk / trust cost

<Honest accounting: what mathematical content is being added on
faith? Is it provable in principle (just expensive)? Is the
oracle's bound certified on demand or claimed once? If it's an
axiom, can a published-paper citation be supplied?>

## Follow-up sprint outline

<If approved, what's the first sprint that uses this? The
Planner doesn't pre-commit a contract here — it just sketches
the next move so the human can sanity-check the cost/benefit.>

## Status log

- <YYYY-MM-DD> created by Planner (sprint_<NNN> context)
<!--
   Append further entries when status changes:
- <YYYY-MM-DD> approved by human; infrastructure landed in <commit/files>
- <YYYY-MM-DD> rejected: <one-line reason>
- <YYYY-MM-DD> superseded by proposal_<NNN_other>
-->
