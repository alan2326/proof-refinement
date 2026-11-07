# Proposals — asynchronous human-approval queue

A proposal is the Planner's request for the human to expand the
harness's trust base — i.e., to add a new `axiom` declaration, a
new certified-arb oracle, a new Mathlib import that brings extra
classical results, or any other change the Generator is forbidden
from making on its own.

Proposals exist because the Generator cannot add axioms (this is
load-bearing: it keeps the trust boundary in human hands), but
sometimes the next valuable refinement *requires* a new axiom or
oracle. Without a queue, the harness would either stall on the
human or spiral on low-value moves. The proposal mechanism lets
the Planner flag the high-value-but-trust-expanding move
**asynchronously**: file the proposal, queue some other sprint,
keep the loop running. The human reviews the proposal whenever
convenient, decides yes/no, and (if yes) does the
infrastructure work out-of-band; the Planner then sees the new
infrastructure on its next read and queues a sprint that uses it.

## Principles

1. **Trust boundary stays with the human.** The Generator never
   adds axioms or oracles. Only the human does, and only in
   response to an approved proposal. This rule is invariant.
2. **Budget: 3 pending proposals max.** Forces the Planner to be
   selective. If 3 proposals are already pending, the Planner
   cannot file a fourth — it must work within current
   constraints, or return `STATUS=BLOCKED_NEEDS_HUMAN`.
3. **Numerical evidence required.** Every proposal must include
   the *concrete win* it unlocks, computed in `Scratch/`. "Adding
   axiom X would help" is not a proposal; "Adding axiom X drops
   `Cr_val` from `1.13·10⁹` to `9.2·10⁷` per
   `Scratch/sprint_NNN_planner_X.py`" is.
4. **Async.** The Planner files a proposal *and* queues a sprint
   in the same invocation (the sprint must be in some other
   allowed direction that doesn't depend on the pending proposal).
   The agent never stalls waiting for a proposal decision.
5. **Reject with reason.** When the human rejects a proposal,
   they edit `Status:` to `rejected` and add a one-line reason in
   the proposal's status log. The Planner reads rejections and
   doesn't re-propose the same thing.

## File layout

```
Proposals/
  README.md           ← this file
  TEMPLATE.md         ← proposal template
  proposal_001_*.md   ← individual proposals
  proposal_002_*.md
  ...
```

Each proposal file is named `proposal_<NNN>_<slug>.md`, where
`<NNN>` is a zero-padded sequential number (compute with the
same `ls | sed | sort -n | tail -1 + 1` algorithm the Planner
uses for sprints) and `<slug>` is a kebab-case 2-4 word topic.

## Status states

A proposal's `Status:` field is one of:

- `pending` — newly filed, awaiting human decision.
- `approved` — human has approved AND has done (or committed to
  do) the infrastructure work. The next Planner run can queue a
  sprint that depends on this proposal.
- `rejected` — human has declined. Includes a one-line reason in
  the status log. The Planner must not re-propose the same idea
  without addressing the rejection reason.
- `superseded` — proposal was overtaken by another (e.g., a
  better proposal for the same axis was filed later). Status log
  names the superseding proposal.

The Planner counts `pending` toward the 3-proposal budget;
`approved`/`rejected`/`superseded` do not count.

## Approval workflow (for the human)

When you decide to **approve** a proposal:

1. Read the proposal's "What's needed" and "Risk / trust cost"
   sections carefully. The trust base is being expanded; the
   review is the substantive control.
2. Implement the infrastructure exactly as described:
   - For new oracles: add the Python function to
     `Numerical_Library/`, add the corresponding `[[oracles]]`
     entry in `lemma.toml`, and declare the supporting axiom in
     the appropriate Lean file.
   - For new axioms: append to `lemma.toml`'s
     `seed_axioms.allowed`, declare in
     `Proof/Lib/Lemma54_Paper.lean` (or the file the proposal
     names).
   - For new Mathlib imports / library moves: do them.
3. Edit the proposal file: change `Status: pending` → `Status:
   approved`, append a status-log line `- <YYYY-MM-DD> approved
   by human; infrastructure landed in <commit-sha-or-files>`.
4. Optionally: add a `note: proposal_<NNN> approved …` line to
   `Bulletin.md` so the next Planner sees it without scanning
   the directory.

When you decide to **reject** a proposal:

1. Edit `Status: pending` → `Status: rejected`, append a
   status-log line `- <YYYY-MM-DD> rejected: <one-line
   reason>`.
2. Optionally add a Bulletin note.

The proposal file stays in place after approval/rejection — it's
the historical record. Don't delete approved or rejected
proposals.

## What proposals SHOULD ask for

> **Note (2026-04-30 policy update)**: certified-arb oracles are
> now **self-serve by the Generator** — they no longer need to go
> through this proposal queue. Just write the oracle (Python file +
> `[[oracles]]` entry in `lemma.toml` + axiom declaration in the
> candidate) inline as part of a normal sprint. See
> `refinement-generator.md` "Inline oracle creation". The proposal
> queue is now reserved for the non-oracle items below.

Roughly in increasing order of trust cost:

- **A new Mathlib import**: brings classical results into scope.
  Trust cost: zero (Mathlib is already in the trust base).
  Example: `import Mathlib.Analysis.SpecialFunctions.SchwarzPick`
  to use Schwarz-Pick. (Most Mathlib imports are routine and the
  Generator can just add them; file a proposal only for unusually
  large additions or ones bringing in disputed/heavy new infrastructure.)
- **A new axiom asserting an existing-paper theorem**: i.e., the
  Planner has identified a result in a published paper that
  matches the Lean signature, but the Generator can't prove it
  in-loop. Trust cost: medium — the human must verify the citation.
  Example: `axiom hyp_borel_caratheodory: …` citing Conway.
- **A new axiom asserting a Lean-provable result the Generator
  can't prove in 3 hours**: e.g., a substantial geometric fact
  about `Ω(δ, B)`. Trust cost: medium — provable in principle,
  but the harness is amortizing the proof cost to the human's
  later out-of-loop session.

## What proposals SHOULD NOT ask for

- **An axiom-prove conversion** (turning an existing axiom into
  a Lean theorem). The current regime treats axiom-count
  reduction as not-a-victory; don't propose work in this axis.
- **A weakening of the Lemma 5.4 statement.** The signature is
  pinned in `Candidates/V0.lean`; tightening Cr_val is the game.
- **A reorganization that doesn't change the trust base.** Such
  edits don't need a proposal — the Generator can do them
  directly within the contract's write scope.

## Indexing

There's no separate `INDEX.md` — the directory listing is the
index. To see all pending proposals:

```bash
grep -l 'Status: pending' ProofRefinement/Lemma54/Proposals/proposal_*.md
```

To see the budget consumption:

```bash
grep -c 'Status: pending' ProofRefinement/Lemma54/Proposals/proposal_*.md \
  | awk -F: '{n+=$2} END {print n "/3 pending"}'
```
