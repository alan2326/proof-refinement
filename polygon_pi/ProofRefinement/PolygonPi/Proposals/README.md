# Proposals

A proposal is a request for a change the sprint loop is not allowed to make on
its own. It is written by the planner, and only a human approves it.

## Scope — narrower than you might expect

Under decision D3 this workspace has **no axiom-expansion path** and **no oracle
path**. There is nothing to unlock by proposal that would let you assume a
mathematical fact. So the legitimate scope is only:

1. **Import-policy changes** — a specific `Mathlib.*` module you need that the
   policy blocks, with evidence that its transitive closure is clean.
2. **Contract restatements** — a change to `ValidPolygonBound` itself. Expect
   this to be refused: the contract is the benchmark, and changing it makes
   candidates incomparable. Bring a very good reason.
3. **Hoisting a derived theorem into `Proof/`** — when a result proved in
   `Candidates/V<N>/` is genuinely reusable and belongs on the trusted side.
   Note this makes it read-only for all future candidates, so it is a real
   commitment, not a convenience.

Everything else that you might be tempted to propose is instead an **analytic
Lean sprint**. If the missing piece is a mathematical fact, the answer is to
prove it, and you are capable of proving it.

## Before filing

All of the following should hold, and you should be able to state each one in the
proposal. This is a checklist for your own judgment, not a mechanical gate — if
you are stretching to satisfy any of them, the proposal is premature.

- **Tried hard and failed.** A specific goal has been attacked in at least one
  prior generator session, the attempt is recorded in `Experience.md` with the
  tactics and search terms used, and the generator exited `BLOCKED` with a
  precise obstruction note. A claim never attempted in Lean is not a proposal
  target — queue the attempt sprint first.
- **Genuinely large cost.** The blocked route would take thousands of lines, or
  depends on a Mathlib API that does not exist. A few hundred lines of
  `nlinarith` / `field_simp` / `gcongr` work is the generator's job.
- **The mathematics is not in doubt.** You can cite a numerical `Scratch/`
  witness or a derivation tight enough that only the formalization is uncertain.
- **It moves the score.** You can point to the specific quantitative gap it
  closes. "Structurally interesting but unclear if it advances the score" is not
  a proposal target.

## Filing

Copy `TEMPLATE.md` to `proposal_<NNN>_<slug>.md`. The sprint you queue alongside
it must still be runnable immediately — a proposal never blocks the loop.
