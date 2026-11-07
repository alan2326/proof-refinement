# Proof Refinement Harness — design guide

A guide for setting up a long-running Claude Code agent loop that refines
the Lean 4 proof of Lemma 5.4 (and the broader Grothendieck-bound proof
graph) without drifting, getting "context anxiety", or silently dropping
rigor.

This guide is grounded in Anthropic's [harness design article][1] and the
specifics of *this* project: a Lean 4 + Mathlib proof bridged to a
certified-arb Python pipeline, with an existing scoring framework
(`Cr_val`), an audit pipeline (`#print axioms`), and a runner pipeline
(`--run-all` + `oracle_assumptions`).

[1]: https://www.anthropic.com/engineering/harness-design-long-running-apps

The article identifies two failure modes for naive long-running agents —
**context deterioration** and **self-evaluation blindness** — and
prescribes four core remedies:

1. **Context resets** instead of in-place compaction.
2. **Generator–Evaluator separation** instead of self-grading.
3. **Sprint contracts** with explicit, testable success criteria.
4. **File-based handoff** between agents.

This guide adapts those remedies to proof refinement.

---

## 1. What the harness is for

**Goal**: produce a sequence of well-validated **candidate** Lean files
under `ProofRefinement/Lemma54/Candidates/V<N>.lean`, each strictly
better than its parent (lower `Cr_val`, fewer axioms, fewer `sorry`s).

**Non-goal**: modify the production proof. The harness is **strictly
candidates-only**. It creates new files in `Candidates/`; it never
edits production code under `ProofGraph/`, `LeanProof/`, or
`Proof/Lib/`. Promoting a winning candidate's improvement into
production is a separate, out-of-loop step the human does after
reviewing the log.

**Win condition**: a sequence of candidates whose
`Refinement_Log/log.jsonl` shows monotone improvement on
`Cr_val` (or whatever metric the Bulletin's current priority names),
with the per-candidate `Evaluator.py` returning `pass: true` on every
accepted iteration.

### Write-scope (contract-driven)

The Generator may write to:

- **Newly-created files**: `Candidates/V<N>.lean` (the typical
  primary deliverable).
- **Pre-existing Lemma 5.4 ecosystem files** named in the
  contract's `Concrete edits expected:` list: `Proof/Lib/`,
  `Numerical_Library/`, `ProofGraph/Effective/Lemma54*.lean`,
  `LeanProof/Lemma54.lean`, `LeanProof/Defs/Strip.lean`.
- **Always-allowed notebook paths**: `Experience.md`, `Bulletin.md`,
  anything under `Scratch/`. These need no contract entry.

The Generator may NOT write to:

- Older candidates (`Candidates/V<K>.lean` for `K < N`) — history
  is sacrosanct.
- Sprint Contracts, `Evaluator.py`, runner code under
  `ProofGraph/proof_graph/`, TOML node configs
  (`lemma.toml`, `_index.toml`), helper scripts.
- Files outside the Lemma 5.4 ecosystem (Theorem44, Theorem51, etc.).

The Evaluator's `G3: write scope` gate enforces this by inspecting
`git diff --name-only HEAD`; any out-of-scope edit is
`WRITE_SCOPE_VIOLATION`. Loss prevention is handled by the project's
git auto-checkpoint hook (every Edit/Write commits), so any
pre-existing file the Generator modifies is always recoverable from
git history.

---

## 2. Anatomy — three roles, one repo

Adopt the article's three-role decomposition. Each role is a separate
Claude Code session (sub-agent or independent loop), so each runs with a
*fresh* context window and reads its inputs from files.

```
                ┌──────────────┐
                │   PLANNER    │
                │ (long-lived) │
                └──────┬───────┘
                       │ writes Sprint Contract
                       ▼
            ┌──────────────────────┐
            │      GENERATOR       │ writes Candidate file
            │ (per-sprint, fresh)  │──────────────┐
            └──────────────────────┘              │
                                                   ▼
                                       ┌──────────────────────┐
                                       │      EVALUATOR       │
                                       │ (per-sprint, fresh)  │
                                       └──────────┬───────────┘
                                                  │ writes Verdict file
                                                  ▼
                                  Planner reads Verdict, queues next sprint
```

### 2.1 Planner

- **Lifetime**: long. The same Planner session can drive many sprints.
- **Inputs**: `ProofGraph/STATUS_AND_PLAN.md`, latest
  `ProofRefinement/Lemma54/Refinement_Log/log.jsonl`,
  `ProofRefinement/Lemma54/Experience.md`, prior Sprint Contracts and
  Verdicts.
- **Outputs**: a new Sprint Contract file (see §4) that names a single,
  bounded refinement target.
- **Discipline**: never opens Lean, never edits Lean files. It only
  picks the next direction and writes the contract. This keeps its
  context lean.

### 2.2 Generator

- **Lifetime**: per-sprint, fresh context. Started by the Planner with
  *only* the Sprint Contract path as input.
- **Inputs**: the Sprint Contract; whatever files the contract names.
- **Outputs**: a new candidate Lean file (`Candidates/V<N>.lean`) and a
  brief change-log entry it appends to `Experience.md`.
- **Discipline**: terminates the moment its contract is satisfied.
  Doesn't grade its own work.

### 2.3 Evaluator

- **Lifetime**: per-sprint, fresh context. Started after Generator
  reports complete.
- **Inputs**: the Sprint Contract + the Generator's candidate file.
- **Outputs**: a Verdict file (PASS/FAIL + diagnostics) appended to
  `Refinement_Log/`.
- **Discipline**: runs the validation gates literally; doesn't argue
  with them; doesn't accept "looks fine" as a passing reason.

This separation directly addresses the article's "self-evaluation
blindness" finding: agents praise their own work even when it's
mediocre. The Evaluator is a different session with no investment in
the Generator's output.

---

## 3. Context discipline

### 3.1 File-based handoff is the rule

No agent state lives in conversation context. Everything that a future
session needs must be in a file. The trio of canonical artifact files:

| File | Owner | Purpose |
|---|---|---|
| `Sprint_Contracts/sprint_<N>.md` | Planner writes, Generator + Evaluator read | The contract for this iteration. |
| `Candidates/V<N>.lean` | Generator writes, Evaluator reads | The actual proof attempt. |
| `Refinement_Log/log.jsonl` | Evaluator appends | Append-only verdict + score record. |
| `Experience.md` | Generator + Planner append | Free-form knowledge. |

Add a fifth, the **bulletin board**: `Bulletin.md` — a short, frequently
overwritten file the Planner uses to communicate priorities, blocks, and
"what to try next" hints to subsequent Generators. Capped at ~100 lines
so it can always be read in full.

### 3.2 Context reset, not compaction

Per the article: when a session approaches its window, prefer killing
the session and starting a fresh one (with file-based handoff) over
compacting the conversation. In Claude Code:

- The Planner explicitly **starts a new sub-agent for each sprint** via
  the `Agent` tool. Each sub-agent has its own conversation; it inherits
  no Planner context except the Sprint Contract path.
- Long-lived loops (e.g. via `/loop`) should produce a single artifact
  per fire and then terminate. The next fire reads the artifact.
- If a session needs to compact mid-work, treat that as a signal to
  *split the sprint*, not to compact. Append a follow-up sprint to the
  Planner's queue.

### 3.3 Ground each session in current state

Every Generator and Evaluator session starts by reading, in this order:

1. The Sprint Contract.
2. `ProofGraph/STATUS_AND_PLAN.md` (production trust boundary).
3. `ProofRefinement/Lemma54/AGENT_BRIEF.md` (workspace conventions).
4. The candidate file referenced in the contract (Evaluator only).

Three short reads, total < 1k lines. After this, the session has the
entire picture without a 50-message scrollback.

---

## 4. The Sprint Contract

Adapt the article's Sprint Contract idea to proof work. A Sprint
Contract is a single Markdown file with a fixed schema:

```markdown
# Sprint <N>: <one-line title>

**Created**: 2026-04-30 by Planner
**Parent candidate**: Candidates/V<K>.lean    # often V<N-1>, but V0 for fresh starts / wildcard sprints
**Target file**: Candidates/V<N>.lean

## Goal (one sentence)
Tighten `M_val` from 4000 to 3600, reproving `lemma_5_4_search` with the
new value and a justifying numerical oracle.

## Why (two sentences max)
The certified `compute_M_rigorous` returns ~3531 on the current rectangle.
We have headroom; smaller M cuts Cr_val quadratically.

## Concrete edits expected
- Change `def M_val : ℝ := 4000` to `def M_val : ℝ := 3600` in the new
  candidate.
- No other Lean changes.
- (No oracle changes — `compute_M_bound_*` already certifies tighter.)

## Acceptance criteria (Evaluator runs literally)
1. `uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V<N>.lean`
   exits 0.
2. The new log line shows `score < <previous-score>`.
3. Axiom count in the log line is unchanged from V<N-1> (no new
   trusted axioms introduced).
4. `Refinement_Log/log.jsonl` reports `pass: true`.

## Out of scope (Generator must NOT do)
- Modify `Proof/Lib/`.
- Modify `ProofGraph/`.
- Add new oracles or rename existing axioms.

## Time budget
≤ 30 minutes of agent runtime; ≤ 200k input tokens.
```

The contract pins **what changes, why, what counts as success, and what's
off-limits**. Three properties matter:

- **Bounded**: one acceptance criterion list, < 200 lines of context.
- **Falsifiable**: every criterion is mechanically checkable.
- **Out-of-scope explicit**: protects against scope creep, the most
  common failure of long-running agents.

Sprint Contracts should be small. If a target needs > 5 acceptance
criteria, split it into multiple sprints.

---

## 5. Validation gates

The Evaluator runs gates in order, **terminating on the first failure**.
Because the harness is candidates-only, all gates are cheap
(no production audit/runner). Total cost per sprint: ~30 seconds.

| Gate | Command | Pass condition |
|---|---|---|
| **G1: Compile** | `lake env lean Candidates/V<N>.lean` | Exit 0, no `error:` lines |
| **G2: No sorry** | `grep -n 'sorry' Candidates/V<N>.lean` | No matches |
| **G3: Write scope** | `git diff --name-only HEAD` | Only `Candidates/V<N>.lean` (new) + optional appends to `Experience.md` / `Bulletin.md`. Anything else is `WRITE_SCOPE_VIOLATION`. |
| **G4: No new non-oracle axioms** | parent's non-oracle `axioms_used` ⊇ new candidate's non-oracle `axioms_used` | Oracle-kind additions (registered in `lemma.toml`'s `[[oracles]]`) are exempt — already human-approved via the proposal mechanism, and re-verified by G5 |
| **G5: Per-candidate evaluator** | `uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V<N>.lean` | exit 0 and `pass: true` in JSON |
| **G6: Score** | parse new log entry | inequality from contract holds (`Cr_val < prev`, etc.) |

If any gate fails, the verdict is FAIL with the failing gate quoted
verbatim. The Generator's narrative or self-assessment is **not**
considered.

### Production verification is post-port, not in-loop

When a candidate's improvement is worth landing in production, the
human (or a one-off, supervised agent invocation) ports the change
into `ProofGraph/Effective/*.lean` and runs the production gates
manually:

```bash
PYTHONPATH=ProofGraph uv run python -m ProofGraph.proof_graph --audit-snapshot
PYTHONPATH=ProofGraph uv run python -m ProofGraph.proof_graph --run-all
```

The harness does not run these. The runner's `inputs_sha256` cache
(`scripts/runner_cache_check.sh`) is available for the human's
post-port verification, not for the loop.

---

## 6. Anti-drift mechanisms

Drift = the agent gradually expanding scope, accepting partial fixes,
or deciding mid-task that "actually a different change is better".
Three counters:

### 6.1 The contract is read-only mid-sprint

The Generator may not edit the Sprint Contract. If it discovers the
contract was wrong, it terminates with a `BLOCKED` outcome and the
Planner writes a new contract. (This protects against scope creep.)

### 6.2 The "what changed" diff is small by construction

After the Generator finishes, the Evaluator runs `git diff` (or the
equivalent file diff) and checks that the changeset matches the
contract's "Concrete edits expected" section. If the Generator changed
files outside scope, the Evaluator returns FAIL with reason
`SCOPE_VIOLATION` even if all other gates pass.

### 6.3 Append-only logs

`Refinement_Log/log.jsonl`, `Experience.md`, and Sprint Contracts are
**append-only**. No editing of historical records. This makes drift
visible: a future reader can see "we tried X three sprints ago and it
failed for reason Y" without an agent retroactively re-summarizing.

### 6.4 Diversity: parent selection + wildcard sprints

By default the Planner queues sprints in a linear chain — each new
candidate has `Parent: V<N-1>.lean`. That's efficient when the
trajectory is making genuine progress, but it has a failure mode:
**trajectory lock-in**. If V3 introduces a misstep, V4 inherits it,
and so on. Refinements compound, but mistakes also compound, and the
search can wander into a local optimum without ever stepping back.

Two mechanisms in the Planner's prompt counter this:

- **Free parent selection.** The contract's `Parent candidate:` field
  is *not* fixed at `V<N-1>`. The Planner is told it can pick any
  earlier candidate as parent — most usefully `V0.lean` (the
  production-mirror baseline) — when the recent trajectory has
  plateaued, accumulated small mistakes, or wandered away from a
  property that an earlier candidate had.

- **Wildcard sprints (1-in-4).** At least every 4th sprint, the
  parent MUST be `V0.lean` (or another non-immediate ancestor) AND
  the direction MUST be one not used in the prior 3 sprints. This
  forces the search out of any local trajectory and gives radically
  different ideas a chance to be tried — without competing against
  the cumulative refinements of the chain.

Practical effect: if sprints 005-007 are M-tightening on the same
rectangle and the gains are tapering, sprint 008 (a wildcard) might
branch from V0 and try axiom-elimination, formula change, or a
different rectangle entirely. If the wildcard wins on score or
trust-base reduction, the trajectory pivots; if not, sprint 009 can
return to the linear chain from wherever's best.

This is the harness's analog of "evolutionary search with periodic
restarts" — the linear chain exploits the current ridge, the
wildcard explores.

### 6.5 Ambitious sprints + persistent Scratch/

Two more diversity mechanisms work together:

- **Sprint tier `cheap` vs `ambitious`.** Most sprints are cheap —
  surgical edits, ≤ 30 minutes, ≤ ~75% of context. Some sprints are
  ambitious — substantial new Lean writing, up to 3 hours, full
  context. The Planner picks based on what the direction needs:
  numerical tighten = cheap, prove a previously-axiomatized fact =
  ambitious. Cadence guideline: an ambitious sprint at least every
  ~5-6 sprints, especially when scores plateau or a known
  load-bearing axiom is plausibly Lean-provable. The Generator's
  prompt acknowledges ambitious-tier work: it iterates compile-edit
  cycles many times within its session and doesn't terminate
  prematurely.

- **Persistent Scratch/.** `ProofRefinement/Lemma54/Scratch/`
  accumulates across sprints — files are never wiped by the harness.
  Naming convention: `Scratch/sprint_<NNN>_<topic>.py`. Both Planner
  and Generator are encouraged to read prior `sprint_<K>_*` files
  for context on past numerical findings, treating Scratch/ as the
  harness's research notebook. This means an ambitious sprint that
  works out a non-trivial calculation (e.g. a Cauchy estimate
  derivation, a formula simplification) leaves a record that future
  sprints can build on rather than re-deriving.

The two combine: ambitious sprints produce both a candidate file
(scored) and a Scratch/ trace (institutional memory). Linear-chain
descendants build on the candidate; future ambitious sprints (and
wildcards) build on the Scratch/ trace.

---

## 7. Anti-anxiety mechanisms

The article's "context anxiety" failure: as the model approaches its
context limit, it prematurely wraps up — declares success, stops trying
hard cases, returns a partial answer.

For proof refinement specifically:

### 7.1 Sprint Contracts cap the work *before* context fills

A well-scoped sprint completes well below the model's context limit.
For Opus 4.6/4.7 on 1M context, **target ≤ 75% of context as a soft
cap** — the agent never sees its limit approaching, so the wrap-up
reflex doesn't fire. (Opus 4.5 / Sonnet 4.5 had stronger anxiety; if
you're running on those, drop the cap to 50%.)

If a Generator session hits 75% mid-work, treat it as a *contract was
too big* signal. The Generator terminates with `STATUS=BLOCKED`
("contract exceeds soft context cap"), and the Planner re-scopes into
two smaller sprints.

### 7.2 The Generator is told to stop the moment the contract is satisfied

Add to the Generator's system prompt:

> **Stop conditions**:
> - The acceptance criteria in the Sprint Contract are met → terminate
>   with `STATUS=READY_FOR_EVALUATION`.
> - You hit a blocker the contract didn't anticipate → terminate with
>   `STATUS=BLOCKED` and a one-paragraph blocker description.
> - You realize the contract is wrong → terminate with `STATUS=BLOCKED`
>   and the reason. **Do not improvise**.
>
> **Anti-speculation rule**: finish the contract's acceptance criteria.
> Don't pad with bonus refactors, additional cross-checks, or "while
> I'm here, let me also…" changes. If you spot a follow-up worth
> doing, append it to `Bulletin.md` and stop. There is always another
> sprint.

The phrasing matters. Don't tell the Generator "early termination is
fine" — that reads as "give up if you're tight on context", which is
exactly the context-anxiety failure mode the harness is meant to
prevent. *Anti-speculation* and *anti-anxiety* are not the same thing.
The instruction above prevents the former without inviting the latter.

### 7.3 Validation gates are not the agent's responsibility

The Generator is told **not** to run the audit/runner itself. The
Evaluator does that in a separate session. This removes the temptation
to optimize for "all checks green" by tweaking the audit allow-list.

---

## 8. Maintaining rigor

### 8.1 Two separate audit pipelines, both load-bearing

- `ProofRefinement/Lemma54/Evaluator.py` — per-candidate audit
  (compile, axioms, score, oracles).
- `PYTHONPATH=ProofGraph uv run python -m ProofGraph.proof_graph
  --audit-snapshot` and `--run-all` — production-graph audit.

Every sprint that touches ProofGraph must pass *both*. Every sprint that
only touches `Candidates/` must pass at least the candidate-side audit.
Don't let one substitute for the other.

### 8.2 Append a reproducibility line to every Verdict

```
REPRODUCED-WITH:
  lake commit: 47bb96d7
  prec=256, K_max=250, p_override=1e-30 (ProofGraph/nodes/_index.toml)
  audit snapshot: ProofGraph/runs/2026-04-30T10-12-44/audit.json
  certificate: ProofGraph/runs/2026-04-30T10-12-44/certificate.json
```

If a later sprint can't reproduce a claim, the verdict trail names
exactly which `runs/<ts>/` to compare against.

### 8.3 No new axioms — strict policy

The Generator may **only**:

- **Remove** an axiom by proving it as a Lean theorem (Mathlib- or
  hand-derived).
- **Retarget** an existing oracle: replace e.g. `M_val = 4000` with a
  tighter `M_val = 3600`, leaving the axiom name and signature
  unchanged. This narrows the bound but doesn't add a new claim to
  the trust base.

The Generator may **not**:

- Add a new `axiom` declaration of any flavor (numerical or
  structural).
- Add a new oracle entry to `lemma.toml` or to the production
  `oracle_assumptions` block.
- Add a new `Classical.choose` extraction whose properties aren't
  already a theorem of the existing module.

Why so strict: every axiom is forever. Once a numerical oracle is
landed, removing it later requires re-doing all the proofs that
depended on it. Better to err on the side of refusing to add. If a
sprint *needs* a new axiom, the Generator returns
`STATUS=BLOCKED_NEEDS_HUMAN`, and the human (you) decides out-of-band
whether the new axiom is justified before the Planner re-scopes.

The Evaluator enforces this gate by `diff`-ing the audit-snapshot
axiom set against the previous successful run, with one exemption:
**axioms classified as `kind = oracle` by the per-candidate
Evaluator** (i.e., axioms whose short name appears in `lemma.toml`'s
`[[oracles]]` table) are not counted as "new" for G4 purposes.
Those have been human-approved through the proposal mechanism, and
G5 independently re-verifies their numeric content every run. Any
new axiom of `kind = seed` or `kind = unregistered` is
FAIL-`NEW_AXIOM_INTRODUCED`.

#### Vocabulary: "runner-witness" vs "structural axiom"

For reference and for what's already in the trust base:

- **Runner-witnessed axiom**: a Lean axiom whose claim is
  re-derivable, every `--run-all`, by a Python check in
  `runner.py` against the certified-arb pipeline. Examples:
  - `h_M_oracle` — re-checked by `M_oracle_le_M_val`
    (`compute_M_rigorous` ≤ `M_val`).
  - `h_oracle_domain_contains_image` — re-checked by
    `domain_containment_certified` (Step 1 Rouché).
  - `h_eta_strict_improvement_oracle` — re-checked by
    `h_eta_strict_improvement` ((H_η(I)/I).re > log(1+√2)).
  - `h_gamma_explicit_sandwich` — re-checked by
    `gamma_best_in_lean_sandwich`.
  - `h_p_explicit_lt_pr_paper`, `h_gap_ratio_at_p_explicit_with_B_phi`
    — re-checked numerically.

- **Structural axiom**: justified analytically; the runner can't
  re-derive it. Examples:
  - The 12 trusted `F_inv_paper` axioms (IFT-supplied).
  - `h_F_p_deriv_at_p_explicit` (F_p has nonzero deriv at 0 for tiny p).
  - `h_summability_at_p_explicit` (sign-structure conclusion at
    p_explicit_rat; cross-validated indirectly via
    `KG_upper_val_lt_KrivineBound`).

The strict policy applies to both flavors equally. A sprint can't add
a new structural OR a new numerical axiom.

---

## 9. Concrete Claude Code wiring

The harness can be implemented entirely with built-in Claude Code
primitives. No new MCP server required.

### 9.1 Roles as sub-agents

Define one custom agent per role. Add to your `.claude/agents/`
directory (or use the `Agent` tool's `subagent_type` directly):

- **`refinement-planner`** — uses Read, Write, Bash (git/log inspection
  only). System prompt: §2.1's discipline. Optional model: Opus for
  long-horizon planning.
- **`refinement-generator`** — uses Read, Write, Edit, lean-lsp MCP, Bash
  (lake build of single modules). System prompt: §7.2's stop conditions
  + a literal copy of §6.1's "contract is read-only" rule.
- **`refinement-evaluator`** — uses Read, Bash (everything in §5),
  WebSearch (no). Cannot use Write or Edit. System prompt: §5's gates,
  in order, terminating on first failure; explicit instruction to
  ignore the Generator's narrative.

### 9.2 The driver loop: `/loop` + `Bulletin.md`

```bash
# Start the harness:
/loop 30m /run-next-sprint
```

`/run-next-sprint` is a slash-command (skill) you create that:

1. Reads `Bulletin.md` to see the current priority direction.
2. Spawns `refinement-planner` to write the next Sprint Contract
   (or to mark the current sprint blocked and write a new one).
3. Spawns `refinement-generator` with the new contract.
4. Spawns `refinement-evaluator` after the Generator reports back.
5. Appends the Verdict to `Refinement_Log/log.jsonl`.
6. Updates `Bulletin.md` with one line summarizing the outcome.
7. Returns a one-paragraph status to the human.

Each step is a separate `Agent` invocation, so each step's context is
isolated. The driver loop's own context is short — it just orchestrates.

### 9.3 Hooks for the non-negotiables

In `.claude/settings.json` add hooks:

- **`PreToolUse` on Write/Edit to `Candidates/V*.lean`**: refuse if the
  current Sprint Contract is missing or stale.
- **`PostToolUse` on `Bash` running `lake build`**: capture exit code
  + last 20 lines into a per-sprint scratch file (`Sprint_State/<N>.log`)
  for the Evaluator to inspect.
- **`Stop` (session end)**: refuse if `STATUS` line is missing from the
  agent's last message; force the agent to declare a final state.

These hooks make the "agent must stop cleanly with a labeled state"
rule load-bearing rather than aspirational.

### 9.4 Rate the loop, don't tail it

The article's advice on cost: a full multi-agent harness is 20× the
solo-agent cost but produces dramatically better output. For proof work
the cost ratio matters less (proofs are not interactive) but the
*time* ratio matters: don't sit there watching. Use:

- `/loop 30m /run-next-sprint` and step away.
- Email-style weekly digest of the log instead of mid-loop monitoring.
- A simple `make-status` script that reads the last 10 log entries and
  prints a one-screen summary. Run once a day.

---

## 10. Operational playbook

### 10.1 Starting cold

1. `Sprint_Contracts/sprint_001.md` — write the first contract by hand.
   Keep it tiny ("change `M_val` from 4000 to 3999, audit must pass").
   This is the harness shakedown, not real work.
2. Run the loop manually for the first 2-3 sprints. Watch where each
   role gets stuck. Tighten the contract format until each sprint
   completes without surprises.
3. Only then start `/loop` for autonomous operation.

### 10.2 Stopping

The loop should stop on:

- Three consecutive FAIL verdicts on the *same* sprint goal (the
  Planner is stuck; needs a human).
- Audit failure on production (`--audit-snapshot` is not 5/5 ok).
  Production regressions are not silently accepted.
- Score regression on any accepted sprint (a passed candidate that
  somehow lowered rigor — should be impossible, but explicit halt
  catches harness bugs).

Add these as exit conditions in `/run-next-sprint`.

### 10.3 Periodically simplify the harness

Per the article: "every component encodes an assumption about what the
model can't do on its own." As Claude improves:

- Once the Generator reliably stops cleanly, drop the `Stop`-hook
  guard.
- Once Sprint Contracts are reliably scoped, allow a Generator session
  to complete two consecutive sprints in one context (less spawn
  overhead).
- Once the Evaluator is rarely catching anything the Generator missed,
  collapse the two roles for "trivial" sprint types (≤ 3 acceptance
  criteria, ≤ 50 lines of changes).

Do these one at a time. Watch the score and verdict trail for
regression after each simplification.

---

## 11. What this doesn't do

The harness is good at: incremental refinement, axiom hygiene, score
tracking, preventing scope creep.

The harness is bad at: greenfield design, deciding *which* lemma to
formalize next, picking the right paper to read, anything that requires
synthesizing across the whole proof graph in one head. Those tasks need
a human Planner (or one focused, long Opus session — not a loop).

Use the harness for the steady drumbeat of small refinements. Use the
human (or a one-off agent invocation) for the strategic moves. Don't
try to make the loop replace strategy.

---

## 12. Reading list (for the human operator)

1. [Anthropic harness design article][1] — the source.
2. `ProofRefinement/Lemma54/AGENT_BRIEF.md` — workspace conventions
   the Generator inherits.
3. `ProofGraph/STATUS_AND_PLAN.md` — production trust boundary; the
   Planner reads this to pick the next direction.
4. `ProofRefinement/Lemma54/Refinement_Log/log.jsonl` — the empirical
   record. Re-read whenever the Planner is stuck.

---

## TL;DR

- **Three roles, three contexts**: Planner, Generator, Evaluator.
  No agent grades its own work.
- **Sprint Contracts**: bounded, falsifiable, out-of-scope explicit.
- **File-based handoff**: nothing important lives only in conversation
  context.
- **Validation gates**: literal commands with binary pass/fail.
  Don't argue with them.
- **Anti-anxiety**: scope each sprint to < 50% of context. Tell the
  Generator that early termination is fine.
- **Anti-drift**: Generator can't edit the contract; Evaluator checks
  the diff matches scope; logs are append-only.
- **Periodic simplification**: as models improve, strip out
  components — one at a time, watching for regressions.
