# Harness Unstuck Plan — break the proposal-filing fixed point

**Created**: 2026-05-03
**Author**: review pass on sprints 048–064 + proposal_003
**Trigger**: the loop has been stuck on `proposal_003`-pending for sprints
061–064. Each sprint emits a halt contract and zero analytical work. The
last `c_value` improvement (V51 → V52, +0.00005) came through the eq15
oracle channel; no analytic Lean theorem has shipped since the channel
opened in sprint 053. The diagnosis: the harness is institutionally
biased toward filing trust-expansion proposals over attempting analytic
Lean derivations.

## Diagnosis (one paragraph)

`Section2Assumptions` exposes Wang's numbered equations (2)–(14) as
opaque bundled hypotheses, but Wang's *un-numbered intermediate
algebraic steps* — the lift identity, the per-k cross-coupling, the
K(c, ρ) extraction inside the derivation of eq.(8) — are not exposed
either as bundled fields or as Lean theorems. An agent that wants to
reclaim the slack Wang drops in eq.(8) therefore has only two routes:
(a) prove the intermediate step in Lean from existing material
(genuine analytic Lean work), or (b) ask Alan to bundle it as a new
field on `Section2Assumptions` (a trust expansion). The current
planner agent definition explicitly directs the planner to choose (b)
when novelty is hard:
`.claude/agents/korenblum-refinement-planner.md:79–82` says *"if no
novel direction, stop and write a proposal instead"*. The bulletin
reinforces this at lines 106–120 ("File proposals when blocked"), and
the generator's stop conditions make `BLOCKED_NEEDS_HUMAN` a peer of
`READY_FOR_EVALUATION` with no extra friction. Combined with a default
agent disposition to underestimate its own analytic-Lean capacity, the
loop converges on proposal-filing as the canonical exit.

## Goal

Retarget the harness so the planner and generator default to attempting
analytic Lean derivations, and reserve proposal-filing for the
narrow case where a claim is genuinely outside Wang 2025's text.

## Action items

The fixes below are ordered by leverage. Items 1, 3, and 7 are the
minimum change set — they retarget the agents' default behaviour and
immediately test the analytic-Lean capability hypothesis. Items 2, 5,
and 6 are structural follow-ups that prevent regression.

### 1. Rewrite the planner's "fail-to-proposal" rule

**File**: `.claude/agents/korenblum-refinement-planner.md`, lines 79–82.

**Current text** (the source of the problem):

> If none of the three candidates is genuinely novel and you are
> tempted to queue a numerical push, **stop and write a proposal
> instead** describing what structural ingredient would be needed to
> unblock a novel derivation, then queue a smaller exploratory sprint.

**Replacement text**:

> If no candidate is novel and you are tempted to queue a numerical
> push, queue an **analytic Lean derivation sprint** instead. The
> generator is competent at multi-hundred-line Lean proofs; assume it
> can prove anything algebraically derivable from `Section2Assumptions`
> plus existing Mathlib.
>
> Proposal-filing is reserved for a narrow case. Use your judgment to
> gauge when it is appropriate; there is no rigid checklist. As a
> guide, all of the following should hold before you file a proposal,
> and you should be able to articulate each in the proposal text:
>
> - **Tried hard and failed.** A specific lemma or result has been
>   attacked in at least one prior generator session, the attempt is
>   recorded in `Experience.md` with the tactical and search
>   directions tried, and the generator exited `BLOCKED` (not
>   `BLOCKED_NEEDS_HUMAN`, not a halt sibling) with a precise
>   obstruction note. A claim that has never been tried in Lean is
>   not a proposal target — queue the attempt sprint first.
> - **Genuinely large derivation cost.** You anticipate the missing
>   result would require thousands of lines of Lean to prove from
>   the current axioms plus Mathlib (e.g. it depends on a
>   substantial Mathlib API that does not exist yet, or on an
>   analytic chain whose intermediate steps each take hundreds of
>   lines). A few hundred lines of `ring` / `nlinarith` /
>   `intervalIntegral.integral_mono` work is not a proposal target —
>   it is the generator's job.
> - **Strong reason to believe the result is mathematically correct.**
>   You can cite specific paper text, a numerical Scratch witness, a
>   reduction from a known-true theorem, or a derivation sketch
>   tight enough that the mathematical content is not in doubt — only
>   the formalization is. A claim whose mathematical truth is
>   uncertain (the proposal_003 pattern, where `θ(c) < 1` was
>   conjectured but not pinned) is not a proposal target — pin the
>   math first via Scratch / paper read.
> - **Strong evidence the result improves `c_value`.** You can cite a
>   numerical Scratch experiment, a slope estimate against the
>   current ceiling, or a paper passage showing the result closes a
>   specific quantitative gap in the existing reduction chain. A
>   claim that is "structurally interesting but unclear if it
>   advances `c_value`" is not a proposal target — there is no
>   project budget for proposals that don't translate to score
>   improvements.
>
> Use these as a checklist for your own judgment, not a mechanical
> gate. If you find yourself stretching to satisfy any of the four,
> the proposal is probably premature — queue an attempt sprint and
> re-evaluate after it returns.

### 2. Rewrite the bulletin's blocked-trigger list

**File**: `Bulletin.md`, the `### File proposals to Proposals/ when blocked`
block (currently lines ~106–120).

Add an explicit *attempt-first* precondition at the top of the block:

> **Before filing any proposal**, the planner must first queue a
> generator sprint whose contract reads "attempt the Lean derivation;
> on failure, document the obstruction at
> `Scratch/sprint_<N>_obstruction.md` precisely enough to file a
> proposal." Only after that sprint returns `BLOCKED` with a concrete
> obstruction note (not `BLOCKED_NEEDS_HUMAN`, and not a halt sibling)
> is proposal-filing permitted on the next sprint.

This converts proposal-filing from a one-step exit into a two-step
sequence whose first step always tries the Lean route. Even if the
generator fails, the failure produces a Scratch artefact that the
proposal can cite as evidence — closing the "axiom shape with deferred
θ(c)" hole that proposal_003 exhibits.

### 3. Add a generator capability statement to AGENT_BRIEF.md

**File**: `AGENT_BRIEF.md`, new section after `## High-value directions`.

Insert verbatim:

> ## Generator capability — read this before exiting BLOCKED
>
> The generator is competent at multi-hundred-line Lean proofs over
> Mathlib's complex-analysis, ℓ²-summability, boundary-integral, and
> measure-theory APIs. Concretely in scope:
>
> - algebraic identities on complex sequences (e.g. Wang's lift
>   identity `(1 − a²)(|b_k|² − |a_k|²) = |b_k − a·a_k|² − |a_k − a·b_k|²`),
> - termwise applications of Wang Lemma 2 (the boundary-L²
>   expansion),
> - Cauchy–Schwarz on boundary integrals,
> - termwise summability and `tsum`-level rearrangement arguments,
> - bridging pointwise modulus inequalities to coefficient-level
>   bounds via Lemma 2,
> - induction on `ℕ`, case splits on `n1Pred` / `n2Pred`,
> - `nlinarith` / `polyrith` / `field_simp` / `ring` chains hundreds
>   of lines long.
>
> If a planner cannot enumerate three distinct Lean-derivation
> directions for an analytic claim, the obstruction is structural,
> not capability — and that fact must be demonstrated by an attempted
> generator sprint, not assumed. Default agent dispositions
> systematically underestimate analytic-Lean capacity; the correct
> prior is "this is provable in Lean, the question is which lemma
> family unlocks the shortest proof."

### 4. Update the generator agent with explicit anti-laziness framing

**File**: `.claude/agents/korenblum-refinement-generator.md`.

**Do not** add rigid stop conditions or counted-attempt requirements
(per Alan's preference). Instead, replace the current *"Think
carefully when the proof resists"* and *"Stop conditions"* sections
with the framing below, which orients the generator toward genuine
exhaustion before exit rather than mechanical retry counts.

**Replacement text for `## Think carefully when the proof resists` and
the `## Stop conditions` block**:

> ## You are capable. Act like it.
>
> Default agent dispositions toward Lean are systematically lazy and
> systematically underestimate what you can do. Counter both.
>
> Concretely: you can write multi-hundred-line Lean 4 proofs. You can
> prove algebraic identities on `ℂ`-valued sequences from first
> principles. You can manipulate `tsum`s, swap summation order under
> summability hypotheses, apply termwise inequalities, bridge pointwise
> bounds to L² bounds via Wang Lemma 2, and chain `nlinarith` /
> `polyrith` / `field_simp` / `linear_combination` over long
> derivations. You can search Mathlib effectively via `lean_leansearch`,
> `lean_loogle`, `lean_local_search`, `lean_state_search`,
> `lean_hammer_premise` — use them aggressively, not once.
>
> When a proof resists, your job is to keep finding angles, not to
> exit. You should only stop when you have **genuinely exhausted**
> the directions you can think of — and "genuinely exhausted" means
> something specific:
>
> - You have stated the exact current goal via `lean_goal` (not from
>   recollection).
> - You have searched Mathlib via at least two of the search tools
>   above for the missing lemma family, and you can name what you
>   were looking for.
> - You have tried multiple distinct tactical approaches, not
>   variations of the same one. If your three "directions" were all
>   `simp` with different lemma sets, that's one direction tried
>   three times.
> - You have considered whether the obstruction is at a different
>   level than where you're attacking it: maybe the goal needs to be
>   restated, maybe an intermediate lemma needs to be proved first,
>   maybe the right move is to invoke Wang Lemma 2 termwise rather
>   than reaching for an unrelated Mathlib API.
> - You have checked whether the obstruction is a missing
>   `Section2Assumptions` field (legitimate trust expansion) versus a
>   gap in your own attack (capability — keep going).
>
> Do not exit on the first sign of difficulty. Do not exit because a
> single tactic block has gotten long — long proofs are normal in
> analytic Mathlib. Do not exit because you've been working for "a
> while" — there is no time pressure on a single sprint. Do not exit
> with `BLOCKED_NEEDS_HUMAN` when `BLOCKED` with a precise obstruction
> note would let the next planner attack the same goal from a
> different angle.
>
> The cost of stopping early is high: the harness has spent four
> sprints (061–064) producing zero analytical artefacts because
> earlier generators exited too cheaply on `proposal_003`-shaped
> obstructions. The cost of trying hard and failing honestly is low:
> the failure note in `Experience.md` and `Scratch/` directly informs
> the next planner.
>
> ## Stop conditions
>
> - Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.
> - You have genuinely exhausted the analytical directions and the
>   obstruction is precisely characterised (which goal, which missing
>   Mathlib lemma, which `Section2Assumptions` field would close it):
>   `STATUS=BLOCKED` with the obstruction written into
>   `Experience.md` and any tried artefacts saved under `Scratch/`.
> - The obstruction is a genuine trust-base expansion (a paper
>   hypothesis Wang 2025 does not state, an oracle whose verification
>   is outside Lean's reach): `STATUS=BLOCKED_NEEDS_HUMAN` with the
>   same obstruction note plus an explicit citation of why it cannot
>   be a Lean theorem from existing material.
>
> "I tried two tactics and the goal is hard" is not exhaustion. "I
> searched Mathlib and didn't find anything in 30 seconds" is not
> exhaustion. "The proof would be long" is not a reason to stop. If
> you find yourself drafting a `STATUS=BLOCKED_NEEDS_HUMAN` line,
> reread this section and ask whether you have actually done the
> work, or whether you are taking the cheap exit.

(No counted-retry rule, no minimum-evidence checklist — the framing
is dispositional, not procedural, per Alan's instruction.)

### 5. Grant the generator architectural permission to create per-candidate derived-theorem files

**Goal**: make explicit that when an agent needs a reusable handle on
one of Wang's *un-numbered intermediate algebraic steps* (the lift
identity, per-k cross-coupling positivity, K(c, ρ) extraction, the
boundary L² comparison, etc.), the agent's first move is to **prove
it as a `theorem` in a per-candidate file scoped to the version it is
shipping**, derived from existing `Section2Assumptions` fields plus
Mathlib. No human pre-curation, no scaffolded sorry list, no separate
"lay down the layer first" sprint. The agent does this on demand
inside the sprint that needs the handle.

`KorenblumPaper/` is the trusted paper surface and is **off-limits**
for new agent-authored files — that directory holds the bundled
axioms and the Wang-paper-side definitions, and changes there carry
trust cost regardless of whether they're `axiom`s or `theorem`s. All
new derived-theorem files live under each candidate's own scope. This
keeps the trust surface frozen and pins each derived theorem to the
version that introduced it, so a candidate's full provenance is
co-located with its `V<N>.lean`.

This is **additive** to the existing axiomatization design and
preserves it intact. `Section2Assumptions` remains the source of
trusted paper content — Wang's numbered equations stay axiomatized
and selectable. The per-candidate intermediate-theorem files live
under `Candidates/` as ordinary derived Lean theorems; agents consume
them the same way they consume Mathlib lemmas, with no trust cost.

**File**: `AGENT_BRIEF.md`, new section after the generator capability
statement from item 3.

Insert verbatim:

> ## Creating derived-theorem files under `Candidates/V<N>/`
>
> Wang's published derivations contain un-numbered intermediate
> algebraic steps (the lift identity, per-k cross-coupling
> positivity, K(c, ρ) extraction, the boundary L² comparison from
> `|f| ≤ |g|`, etc.). These are not bundled fields on
> `Section2Assumptions` and they should not become bundled fields —
> they are derivable from existing fields plus Mathlib, often by a
> few lines of `ring` / `nlinarith` / `intervalIntegral.integral_mono`
> work.
>
> When a sprint needs such a handle, **prove it in a derived-theorem
> file scoped to the candidate version you are shipping**. Concretely:
> if the sprint ships `Candidates/V<N>.lean`, create derived-theorem
> files under `Candidates/V<N>/`. Examples: `Candidates/V53/Lift.lean`,
> `Candidates/V53/BoundaryCompare.lean`, `Candidates/V53/Intermediates.lean`.
> Pick a name that reflects what the file contains; group related
> intermediates in one file rather than fragmenting.
>
> Rules for per-candidate derived-theorem files:
>
> - the file contains `theorem`s (or `lemma`s), never new `axiom`s
>   and never new `Section2Assumptions` fields,
> - proofs draw only on existing `Section2Assumptions` fields,
>   `KorenblumPaper.*` modules already pinned in
>   `lemma.toml:[workspace_import_policy]`, and Mathlib,
> - if a new module path is needed, add it to
>   `[workspace_import_policy]` in the same sprint (this is not a
>   trust expansion — the file is Lean theorems on top of the
>   existing trusted surface),
> - the file is imported only by `Candidates/V<N>.lean` (or by other
>   files under `Candidates/V<N>/`), never by `KorenblumPaper/`,
>   `Proof/`, or other candidates,
> - the file does not modify the bundle, does not introduce
>   alternative paper content, and does not edit anything under
>   `KorenblumPaper/` — that directory is the trusted paper surface
>   and is read-only for the generator.
>
> If a derived theorem is genuinely useful across multiple future
> candidates, propose hoisting it to a shared location in a sprint
> contract; do not hoist unilaterally. The default is per-candidate
> scope.
>
> Default disposition: when proposal_003-shaped requests come up
> (intermediate Wang derivation step needed), the answer is "prove
> it in Lean in a per-candidate derived-theorem file," not "file a
> proposal." The planner should queue an analytic Lean sprint
> targeting the downstream improvement (e.g. a tightened
> (15)-shaped inequality); the generator, while attempting that
> sprint, creates the per-candidate derived-theorem files as needed
> and uses them. One sprint, one derivation chain, no proposal.

**Generator write-scope update**: also update
`.claude/agents/korenblum-refinement-generator.md`'s `## Write scope`
section to add `Candidates/V<N>/**` (where `<N>` matches the candidate
the sprint is shipping) to the writeable list, and to explicitly call
out `KorenblumPaper/**` as not-writeable except when a sprint contract
explicitly authorises a paper-surface change (which it generally
should not).

### 6. Cancel the cron until items 1–5 land

**File**: harness cron registration (per `CronList`).

The cron is currently firing into a no-op (sprint 064's halt
declaration ensures subsequent firings exit without writing
contracts), but each firing still consumes Bash, Read, and
diagnostic calls. Until items 1–5 are deployed, the cron does net
work that is strictly negative. Cancel it via `CronDelete` (or
`! crontab -e` and remove the entry). Re-enable after item 7's first
sprint has shipped successfully — at that point the loop has a
demonstrated forward direction.

### 7. Retract proposal_003 and leave the harness ready for the next /loop fire

**Do not** queue a specific test sprint. After items 1–6 land, Alan
will run `/loop /run-next-korenblum-sprint` from a separate coding
agent in `ProofRefinement/Korenblum/`, and the planner will pick the
next sprint shape itself under the new rules. The role of this item
is only to clear the proposal_003 blocker and make sure the harness
is in a runnable state.

**Files**:

1. `Proposals/proposal_003_paper_eq4_per_k_cross_coupling_for_c_push.md`:
   add a `## Status log` entry dated 2026-05-03 marking
   `Status: superseded` with reason "supplanted by the new harness
   policy (per `docs/HARNESS_UNSTUCK_PLAN.md`): the per-k drop
   should be attacked by proving the needed intermediate algebraic
   lemmas as `theorem`s in per-candidate derived-theorem files
   under `Candidates/V<N>/`, derived from existing
   `Section2Assumptions` fields plus Mathlib, rather than by
   bundling a new `Section2Assumptions` field. If a future generator
   session attempts this and surfaces a structural Lean obstruction
   meeting the four conditions in the rewritten planner rule
   (item 1), a successor proposal may be filed citing the
   obstruction note."

2. **Pre-run sanity checks** (no new files written; just confirm
   the harness is good to go):
   - `bash scripts/korenblum_harness_preflight.sh` exits 0;
   - `lake build ProofRefinement.Korenblum.Candidates.V52`
     succeeds (the current high-water mark still compiles under
     any `lemma.toml` edits made by item 5);
   - the canonical-halt sprint 064 is the most recent sprint
     contract — when the next planner fires, it reads the new
     rules, sees proposal_003 is `superseded` (no longer
     `pending`), and is no longer constrained to halt;
   - `Bulletin.md` `## Current priority` block reflects the new
     attempt-first rule from item 2 (planner sessions read this
     first);
   - the harness cron from item 6 is cancelled (verify via
     `CronList`).

   If any check fails, fix it before handing back to Alan.

After these checks pass, the harness is ready. Alan runs
`/loop /run-next-korenblum-sprint` in a separate coding agent and
the loop picks up under the new policy.

## Acceptance criteria for this plan

- Items 1–5 are file edits to existing files (`AGENT_BRIEF.md`,
  `Bulletin.md`, the two agent definitions); check via `git diff`
  that the replacement text matches §1, §2, §3, §4, §5 verbatim. No
  Lean files are pre-written by this plan and no sprint contracts
  are pre-queued — the derived-theorem layer is created on demand
  by the generator inside whichever sprint the planner picks first
  under the new rules.
- Item 6 produces no positive deliverable; verify via `CronList`
  that the harness cron is absent.
- Item 7 produces only the proposal_003 status update and the
  pre-run sanity-check confirmations; verify by reading the
  proposal_003 file and the listed check outputs. No new sprint
  contract is written by this plan.

## Non-goals

- This plan does not change `Section2Assumptions` or remove any
  bundled field. The axiomatize-the-numbered-equations design is
  preserved.
- This plan does not let agents create or edit files under
  `KorenblumPaper/`. That directory is the trusted paper surface
  and is read-only for the generator (per item 5). All new
  derived-theorem files live under `Candidates/V<N>/`, scoped to
  the candidate that introduced them.
- This plan does not add wall-clock or counted-attempt limits to
  the generator, and does not impose a rigid checklist on
  proposal-filing. The framing is dispositional throughout (items 1
  and 4) — the planner uses judgment against the four guiding
  conditions in item 1; the generator keeps trying until genuinely
  exhausted per item 4.
- This plan does not pre-queue a test sprint. After items 1–6
  land and item 7's sanity checks pass, Alan runs
  `/loop /run-next-korenblum-sprint` in a separate coding agent
  and the planner picks the next sprint shape itself.
- This plan does not touch the oracle channel. `lemma.toml` and the
  `hEq15_oracle_certified_*` axioms remain as-is. The plan is
  orthogonal to the oracle route; both can coexist.
- This plan does not relitigate sprints 048–064. The historical
  trace is the diagnostic evidence that motivated the plan; it
  stays in `Refinement_Log/` unchanged.
