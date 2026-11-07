# Instrumented Single-Iteration Ablations — Design

**Date:** 2026-07-27
**Status:** Draft for approval
**Scope:** Korenblum executes now; Grothendieck designed but not executed (§9).

---

## 1. Objective and reviewer mapping

Rerun the ablation study for *Optimizing Analytic Constants via AI-Guided Lean Proof
Refinement* (NeurIPS 2026 submission 32032) with full instrumentation, anchored on a
single iteration of the framework's trajectory rather than a from-scratch run.

Every reviewer complaint this addresses:

| Reviewer | Complaint | Addressed by |
|---|---|---|
| Ss1D W3 / Q1 | No hardware config, wall-clock, model calls, failed attempts, success rates | §6 instrumentation schema; every field recorded per arm |
| Ss1D Q2 | Baselines' foundation model / budget / literature / tool access / stopping criteria unclear | §3 arm specs (explicit per-arm capability matrix); §4 stopping rule |
| Ss1D Q2 | "Clarify the specific failure modes of each baseline" | §5 DNF taxonomy |
| KcCs | "Failures reported mostly as DNF outcomes without detail about budgets, prompts, stochastic variability, implementation conditions" | §5 + §6; full prompt archival |
| dimn | "Manuscript should include more details on the prompts used for each part of the AI Agent Framework (Sec 3.3)" | §6.4 prompt archival — verbatim agent definitions + skill + contracts shipped as an appendix |
| Uspn W2 / Q2 | "The computational cost is not well evaluated" | §4 metrics; §10 cost table |
| KcCs / Ss1D | "Ablation study is conducted only on the Korenblum constant" | §9 Grothendieck design (executed in a second phase) |

**Explicitly out of scope:** reproducibility across independent runs (N>1 per arm). A
collaborator is handling that concurrently. Every run here is nonetheless recorded so
that additional seeds can be appended to the same schema without rework (§6.5).

---

## 2. The anchor iteration

### 2.1 Selection

The Korenblum trajectory (213 evaluator invocations, `korenblum/ProofRefinement/Korenblum/Refinement_Log/log.jsonl`)
has five certified `c` improvements:

| Band | c | Δc | Sprints | Wall clock |
|---|---|---|---|---|
| V0 → V48 | 0.355400 | — | 48 | 2026-05-01 22:37 → 05-02 23:02 |
| V48 → V49 | 0.356000 | +6.0e-4 | 1 | 05-02 23:30 |
| V49 → V52 | 0.356450 | +4.5e-4 | 3 | 05-03 |
| V52 → V64 | 0.356460 | +1.0e-5 | ~30 | 05-03 → 05-05 03:44 |
| **V64 → V66** | **0.356562** | **+1.02e-4** | **5 (084–088)** | **05-05 04:00:25 → 06:19:07** |
| V66 → V68 | 0.356565 | +3.0e-6 | 4 | 05-05 06:27 → 09:29 |

**Anchor = V64 → V66, sprints 084–088.** Rationale:

1. **Largest single certified push** in the trajectory, and an order of magnitude
   above the V52→V64 push it followed (sprint 088's own contract calls this out).
2. **It realises the paper's headline Korenblum insight** — the per-mode supremum
   kernel `H(c,ρ) = sup_{j≥1} (j/(j+1))·c^(2j+2)/ρ^(2j)` replacing Wang's eqs (5)+(6),
   as a 7-window τ-band partition with √-rational endpoints
   (`τ_j = 1 − 1/(j+1)²` ⟹ breakpoints at `ρ²/c² ∈ {50/49, 36/35, 25/24, 16/15, 9/8, 4/3}`).

   > **Correction, established during P0 — the anchor is execution, not discovery.**
   > The seven-window / per-mode *direction* was already on the roadmap at S₀. The
   > Bulletin's 2026-05-04 "EXPLICIT V38 REFERENCE" directive and sprint 083's own
   > contract both name it — sprint 083 §"Out of scope" says verbatim: *"Re-attempt
   > the seven-window m=7 reducer for V38's `c = 356401/1000000`: bigger c-push but
   > needs new reducer infrastructure (Sprint C of the Bulletin's three-sprint
   > chain). **Deferred to sprint 084+.**"*
   >
   > So all three arms start knowing the intended architecture and a target of
   > `c = 356401/1000000`. What sprints 084–088 actually added, and what the arms
   > must therefore reproduce:
   >   * the general-`m` per-mode τ-partition reducer (084),
   >   * the mixed-kernel reducer admitting Branch.one *and* modeJ windows (086),
   >   * a Phase-0 sweep that found the architecture's true c-ceiling to be
   >     **`356562/1000000`, +1.61e-4 above the roadmap's own 356401 target** (087),
   >   * the certified numerical wrapper for it (087),
   >   * the full Lean witness chain (088).
   >
   * This is a **better-controlled** ablation than a pure-discovery anchor: every arm
   > receives the same roadmap, so the comparison isolates execution capability
   > rather than luck in direction-finding. It must not be described as the arms
   > rediscovering the mode-adaptive kernel from nothing.
3. **Tight and self-contained**: 5 sprints in one contiguous 2h18m42s band, with
   per-sprint boundaries recoverable to the second from contract/verdict mtimes.

### 2.2 Anchor boundary

- **Start state** `S₀`: the workspace exactly as it stood at the end of sprint 083
  (V64 accepted at `c = 35646/100000`; sprints 084–088 not yet performed).
- **Goal** `G`: produce a candidate that the unmodified `Evaluator.py` accepts with
  `pass: true` and `score > 35646/100000`, under the arm's trust surface.
- **Reference cost**: whatever the instrumented Arm A run consumes reaching `G`
  from `S₀` (§4).

Per-sprint reference timings inside the band (from file mtimes):

| Sprint | Contract written | Verdict written | Content |
|---|---|---|---|
| 084 | 04:00:25 | 04:21:35 | per-mode multi-window reducer, general `m` |
| 085 | 04:28:29 | 04:36:46 | branch1 pointwise eq5+eq8+eq9, factored |
| 086 | 04:44:39 | 05:01:04 | mixed-kernel multi-window reducer |
| 087 | 05:08:15 | 05:42:23 | 7-window mass oracle: Phase-0 sweep + Python wrapper |
| 088 | 05:53:09 | 06:19:07 | **V66 ships** at `c = 356562/1000000` |

### 2.3 Snapshot reconstruction — the main technical risk

`korenblum/` **was never committed during the run.** `git log` stops at 2026-05-02
(5 commits, last one `732a5f0`, before V48); the working tree is at the final
post-sprint-102 state. So `S₀` must be reconstructed by hand.

What must be removed to get from HEAD-of-worktree back to `S₀`:

| Path | Action |
|---|---|
| `Candidates/V65.lean` … `V68.lean`, `Candidates/V6{5,6,7,8}/` | delete |
| `Proof/Reduction.lean` | truncate at the sprint-084 boundary (sprints 084/085/086 reducers and 087's `v66CValue` / `v66SevenWindow*` defs + `h_seven_window_mass_certified_at_356562_sqrt` axiom are appended; the mixed reducer is at ~:8934, sprint-087 helpers at ~:9487) |
| `Numerical_Library/rigorous_scalar.py` | remove `certify_seven_window_mass_at_356562_sqrt` and later wrappers |
| `lemma.toml` | remove `[[oracles]]` rows and `[seed_axioms]` entries added at sprint 087+ (`hH2_v66`, `hCircleGapInt_v66`, the 7-window oracle) |
| `Sprint_Contracts/sprint_084…102`, `Refinement_Log/verdict_sprint_084…102` | delete |
| `Refinement_Log/log.jsonl` | truncate to entries with `timestamp_utc < 2026-05-05T04:00:00Z` |
| `Bulletin.md`, `Experience.md` | truncate to the sprint-083 row |
| `Scratch/sprint_087*`, `sprint_089*`+ | delete |
| Sprints 096–098 hoisted V63 derived theorems into `Proof/` | revert (post-anchor) |

**Acceptance gate for `S₀` (hard, blocking):**

1. `lake build ProofRefinement.Korenblum.Candidates.V64` succeeds.
2. `Evaluator.py --file Candidates/V64.lean` returns `pass: true`, `score = 17823/50000`.
3. `grep -c v66CValue Proof/Reduction.lean` → 0; the 7-window oracle axiom is absent.
4. `lake build` of every surviving candidate V0–V64 succeeds (no dangling refs).

### 2.4 P0 outcome — S₀ built, all gates pass

Reconstruction succeeded; the sprint-088-only fallback was not needed.
`Reduction.lean` proved cleanly append-ordered (sprint 084 opens at line 8260).
Reproducible via `harness/make_s0.sh` (rebuilds from `korenblum`,
which is never mutated) + `harness/gate_s0.sh`. Gate output: **ALL PASS** —
V64 builds, evaluator returns `status: PASS` / `score 17823/50000` / oracle
audit PASS / no `sorryAx`, whole workspace builds, log tail and contract tail
are sprint-083-consistent, and no answer term leaks.

Five things P0 surfaced that the original plan did not anticipate:

1. **Sprints 096–098 hoisted the V63 derived files into `Proof/`** and rewrote
   V64's imports *and* its 11 fully-qualified body references. Reverting required
   moving the content back under the `Candidates.V63.*` namespace and re-pointing
   V64. Handled; V64 now builds against `Candidates.V63.*` exactly as the
   sprint-083 `log.jsonl` entry records.

2. **The truncation removed `end ProofRefinement.Korenblum`.** Re-appended.

3. **`Bulletin.md` carried a 264-line post-anchor human directive** (dated
   2026-05-05, "AUDIT + NEW-IDEAS") at the *top* of the file, above the sprint
   rows, so the tail truncation missed it. It audits sprints 086–092 and states
   the architectural ceiling `c ≈ 0.356565` outright — a direct statement of the
   answer, and the single worst leak found. Removed. The 2026-05-04 V38 reference
   directive beneath it is pre-anchor and is **kept**, because sprint 084's
   contract cites it by name.

4. **`lemma.toml`'s `[import_policy].allowed_exact` listed V65–V68 derived
   modules by name** and named `c = 356562/1000000` in a comment — inside the
   kept prefix. Restored to the ten sprint-083 modules.

5. **Two deviations that are not cleanly reversible, both accepted and reported:**

   * *Sprint 085's DRY refactor is pre-applied.* Sprint 085 edited
     `Reduction.lean` **in place at ~line 2497**, extracting
     `pointwise_branch1_on_Ioo_eq5_eq8_eq9` from an inline derivation. Re-inlining
     is risky Lean surgery on the substrate Arms A and B share, and sprint 085 was
     score-neutral (it shipped a V65-*tie*, no c change). Kept. The anchor task as
     reproduced is therefore **"sprints 084–088 minus 085's refactor"** — roughly
     4 of 5 sprints of work. Affects Arms A and B identically; Arm C not at all.
   * *The numerical library is the Arb version, not sprint 083's mp.quad version.*
     `certify_two_window_mass_at_35646_sqrt` was migrated in place to rigorous
     interval arithmetic at sprints 099/101/102; the pre-migration body has no VCS
     coverage and is unrecoverable. Kept, because Arb is strictly **more** rigorous
     than what the anchor run used — it steelmans every arm rather than weakening
     any.

   Post-anchor sprint *labels* in surviving comments were relabelled (prose only;
   no executable code or proof term touched) so the workspace does not tell the
   agent it is at sprint 099+.

---

## 3. The three arms

All three start from the same anchor and share the same goal `G` and the same
unmodified `Evaluator.py` gate. What differs is exactly one factor per ablation arm.

### 3.1 Arm A — full framework (reference)

The unmodified harness at `S₀`: `/run-next-korenblum-sprint` driving
planner → generator → evaluator in sequence, looped until `G` or halt.

- Planner (`model: opus`), Generator (`model: opus`), Evaluator (`model: sonnet`).
- Full tool surface: Read/Write/Edit/Bash/Grep/Glob, WebFetch/WebSearch,
  `mcp__lean-lsp__*` (23 tools), `mcp__lean-explore__*` (8 tools).
- Full workspace memory: `Bulletin.md`, `Experience.md`, `Refinement_Log/`,
  `Sprint_Contracts/`, `AGENT_BRIEF.md`, `docs/`.
- Partial formalization present: `KorenblumPaper/*` (18 modules), `Proof/Reduction.lean`,
  `Section2Assumptions`, the Eq15 seed axiom, `Numerical_Library/`.

This arm exists because the original run's token/cost telemetry is unrecoverable
(§7.1). It provides the denominator for §4.

### 3.2 Arm B — ablate the agentic system (keep partial formalization)

Replace the planner/generator/evaluator agent system with a bare base-LLM refinement
loop. Everything else — including the entire partial formalization — is held fixed.

**Loop (implemented in `harness/arm_b_loop.py`):**

```
context = { contract statement, editable subgoal, partial formalization excerpt }
history = deque(maxlen=3)          # rolling (edit, error) pairs
while not (goal_reached or budget_exhausted):
    prompt   = SYSTEM + context + render(history) + current_candidate
    response = anthropic.messages.create(model=..., ...)   # one call, no tools
    edit     = extract_lean_file(response)
    write(Candidates/B_iter{n}.lean, edit)
    build    = run("lake build ...")
    evalr    = run("Evaluator.py --file ...")   # unmodified
    history.append((edit_digest, build.stderr_tail + evalr.stdout_tail))
    if evalr.pass and evalr.score > c_prev: goal_reached = True
```

**What it gets:**

- The candidate file `Candidates/V64.lean` (the editable subgoal) verbatim.
- The partial formalization, as read-only context: `Proof/Reduction.lean` signatures,
  `KorenblumPaper/*` theorem statements, `Proof/CandidateContract.lean`,
  `lemma.toml`.
- **Wang (2025) extracted text**, as read-only context. Arm A's generator has
  WebFetch and the paper on disk; withholding the literature from Arm B would
  confound "no agency" with "no literature." Arm B gets the same mathematical
  inputs as Arm A — it just cannot go looking for more.
- **The S₀ roadmap**, as read-only context: the Bulletin's 2026-05-04 V38
  reference directive and sprint 083's forward-direction section. Per §2.1's
  correction, this is the information Arm A's planner reads at S₀; the ablated
  factor is agency, not information, so Arm B must receive it too. Without this
  Arm B would be ablating two variables at once.
- **The Python numerical library** (`Numerical_Library/`), including the existing
  certification wrappers, as read-only context — and the ability to emit an edited
  version of it. *(User decision — steelmanning.)* Without this the arm cannot in
  principle produce a certified higher-`c` candidate and the ablation would be a
  strawman.

  **This requires no tool and no agency.** `Evaluator.py` resolves and runs the
  registered oracle function itself as part of its gate (`_resolve_oracle_fn`,
  `Evaluator.py:381`, invoked at `:408`), comparing the recomputed bound against the
  candidate's declared `bound_field`. So to certify a new `c`, the model emits an
  edited `Numerical_Library/rigorous_scalar.py` and a new `[[oracles]]` row in
  `lemma.toml` as *file content*, exactly as it emits Lean. The loop writes those
  files; the evaluator runs the numerics on its own. The model never invokes
  anything.
- Rolling window of the **last 3 (edit, compiler-error) pairs**. *(User decision.)*
- Verbatim `lake build` and `Evaluator.py` output on every iteration.
- The same base model as Arm A's generator, same effort setting.

**What it does not get:**

- Planner, generator, evaluator subagents; sprint contracts; the driver skill.
- Persistent memory: `Bulletin.md`, `Experience.md`, `Refinement_Log/` are not read.
- Agentic tool use: no Bash/Grep/Glob/Read exploration, no MCP `lean-lsp` /
  `lean-explore`, no WebSearch. One model call per iteration, text in, text out.

**The isolated factor:** agency (planning, tool-mediated exploration, memory,
multi-role decomposition). The partial formalization is identical to Arm A.

### 3.3 Arm C — ablate the partial formalization (keep the agentic system)

Keep the full planner/generator/evaluator harness; strip the Lean partial
formalization down to the definition of the constant plus the previous bound as an
axiom.

**Workspace `S₀ᶜ`:**

- `Proof/CandidateContract.lean` — the function-level Bergman A² statement only:

  ```lean
  def UnitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

  noncomputable def bergmanNormSq (f : ℂ → ℂ) : ℝ :=
    ∫ z in UnitDisk, ‖f z‖ ^ 2 ∂(volume : Measure ℂ)

  def ValidKorenblumBound (c : ℝ) : Prop :=
    0 < c ∧ c < 1 ∧
      ∀ (f g : ℂ → ℂ),
        AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
        Integrable (fun z => ‖f z‖ ^ 2) ((volume : Measure ℂ).restrict UnitDisk) →
        Integrable (fun z => ‖g z‖ ^ 2) ((volume : Measure ℂ).restrict UnitDisk) →
        (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
        bergmanNormSq f ≤ bergmanNormSq g
  ```

  (This definition is already built and `lake build`-verified in
  `korenblum_noPF/ProofRefinement/Korenblum/Proof/CandidateContract.lean` — reused.)

- `Candidates/V0.lean` — seed with **the anchor's parent bound**, not Wang's:

  ```lean
  axiom hKorenblum_prev : ValidKorenblumBound (35646 / 100000)
  ```

  This makes the target identical to Arms A and B: certify `c > 0.35646`.
  *(Differs from the earlier `korenblum_noPF` arm, which seeded at Wang's 0.3554 and
  so was not comparable to any single framework iteration.)*

- `lemma.toml` — `[seed_axioms].allowed` = standard Lean axioms + `hKorenblum_prev`.
  No `[[oracles]]`. `[workspace_import_policy]` allows `ProofRefinement.Korenblum.*`
  and `Mathlib` only.

- Everything else deleted: `KorenblumPaper/*`, `Proof/Reduction.lean`,
  `Proof/ProblemAxioms.lean`, `Numerical_Library/`, all `Candidates/V1+`,
  all sprint contracts and verdicts, `Bulletin.md` / `Experience.md` reset.

**What it keeps (steelmanning):**

- The full agentic harness, unchanged mechanics: planner/generator/evaluator,
  sprint contracts, refinement log, all tools including MCP `lean-lsp` /
  `lean-explore`.
- **Wang (2025) — the paper PDF and extracted text — plus WebFetch/WebSearch.**
  *(User decision.)* This is a deliberate improvement over the earlier `korenblum_noPF`
  arm, which stripped the paper as well and thereby conflated two variables
  ("no Lean scaffold" with "no literature"). Ablating only the Lean partial
  formalization is both fairer and a cleaner one-factor experiment.
- Permission to build its own formalization from Mathlib. If it reconstructs a
  partial formalization, that is a legitimate (and highly informative) outcome.

**What it does not get:** any Lean-side reduction chain, any `Section2Assumptions`
bundle, any registered numerical oracle, any pre-built numerical library.

**The isolated factor:** the partial formalization.

**Trust gate:** adding a direct-conclusion axiom at a higher `c`
(e.g. `axiom h : ValidKorenblumBound (36/100)`) is *not* progress. `Evaluator.py`'s
`[seed_axioms]` check rejects unlisted axioms; if the agent edits `lemma.toml` to
allow one, that is recorded as **D4 TRUST-DNF** (§5), not a success. The planner is
told this explicitly in `AGENT_BRIEF.md`.

### 3.4 Capability matrix (this table goes in the paper)

| | Arm A (full) | Arm B (no agent) | Arm C (no PF) |
|---|---|---|---|
| Partial formalization (Lean chain) | ✅ | ✅ | ❌ |
| Editable subgoal (`V64.lean`) | ✅ | ✅ | seed only |
| Numerical library / oracles | ✅ | ✅ (may emit edits; evaluator runs it) | ❌ |
| Wang 2025 paper | ✅ | ✅ (as fixed context) | ✅ |
| Live web search / fetch | ✅ | ❌ (no tools) | ✅ |
| Planner / generator / evaluator | ✅ | ❌ | ✅ |
| Sprint contracts | ✅ | ❌ | ✅ |
| Persistent memory (Bulletin/Experience/log) | ✅ | last 3 errors | ✅ |
| Agentic tools (Bash/Grep/Read/MCP) | ✅ | ❌ | ✅ |
| Base model | same | same | same |
| Lean toolchain / Mathlib rev | same | same | same |
| `Evaluator.py` gate | unmodified | unmodified | unmodified |
| Budget | reference | 3× (§4) | 3× (§4) |

---

## 4. Budget metrics and stopping rule

### 4.1 Recorded metrics (all arms, all runs)

| # | Metric | Unit | Source |
|---|---|---|---|
| M1 | Wall-clock, end-to-end | s | run harness |
| M2 | LLM output tokens | tokens | transcript `usage.output_tokens` |
| M3 | LLM input tokens (uncached / cache-write / cache-read, separately) | tokens | transcript `usage.*` |
| M4 | Model calls (assistant turns) | count | transcript, deduped by message id |
| M5 | USD at published list prices | $ | M2+M3 × per-model rate |
| M6 | `lake build` invocations | count | harness wrapper |
| M7 | `Evaluator.py` invocations | count | `log.jsonl` |
| M8 | Failed attempts (build fail, evaluator fail) | count | §5 event log |
| M9 | Lean CPU time (compile + typecheck + axiom scan) | s | `log.jsonl` elapsed fields |
| M10 | Numerical-certification wall time | s | harness wrapper |
| M11 | Peak RSS | GB | `/usr/bin/time -v` |

M5 uses published API list prices, recorded per model ID at run time
(Opus 5: \$5 / \$25 per MTok; Sonnet 5: \$3 / \$15). Cache-read is billed at 0.1×
input, cache-write at 1.25× input. This is reported as *cost at list prices*,
not as billed cost — stated explicitly in the paper.

### 4.2 Stopping rule

**Arm A** stops when it reaches `G`, or on a terminal halt condition, whichever
comes first. Its M1 and M2 become the reference `T_ref` and `O_ref`.

**Arms B and C** run until **both**:

```
M1 > 3 × T_ref     AND     M2 > 3 × O_ref
```

*(User decision: gate on wall-clock and output tokens; the other metrics are
recorded and reported but do not gate.)*

If an arm reaches `G` earlier, it stops there and is a success. If it exhausts the
3× budget without reaching `G`, it terminates with a DNF label (§5).

**Hard caps** (safety, not the science): 24 h wall-clock and 1000 iterations per
arm. Hitting a hard cap before 3× is reported as an incomplete budget, not a DNF.

**Budget-vs-progress curve.** Every arm's progress is logged continuously against
spend, so the paper can report both the *matched-budget* point (1× `T_ref` / `O_ref`)
and the *generous-budget* point (3×). Reporting only the 3× number invites the
objection that the ablations were over-resourced; reporting the curve pre-empts it.

---

## 5. DNF taxonomy

Every run terminates with exactly one label. Each label is backed by a machine-checkable
predicate over the event log, plus an archived evidence pointer.

| Label | Name | Predicate | Evidence |
|---|---|---|---|
| **S** | SUCCESS | `Evaluator.py pass && score > c_parent && axioms ⊆ allowed` | verdict + log.jsonl row |
| **D1** | STRATEGY-DNF | No iteration ever *proposed* a candidate with `c' > c_parent` (score expression never changed) | all candidate `def c_value` values |
| **D2** | NUMERICAL-DNF | A higher `c'` was proposed, but its numerical certificate failed (joint mass < 1, Arb interval does not close, oracle wrapper returns false) | wrapper stdout, Phase-0 witness |
| **D3** | FORMALIZATION-DNF | Direction + certificate OK, but the Lean proof never compiled (persistent type/tactic errors) | last `lake build` stderr |
| **D4** | TRUST-DNF | Produced a "passing" artifact violating the trust surface: new unlicensed axiom, `sorryAx`, direct-conclusion axiom at higher `c`, unregistered oracle, or self-edit of `[seed_axioms].allowed` | axiom scan + `lemma.toml` diff |
| **D5** | BUDGET-DNF | 3× budget exhausted with a live non-regressive candidate in progress | final iteration state |
| **D6** | THRASH-DNF | Same failing edit repeated ≥ 5× (edit digest recurrence), or best score regressed | edit-digest histogram |
| **D7** | INFRA-DNF | Harness/tooling failure: API error exhaustion, disk full, OOM, timeout | stderr + env snapshot |

**D7 is excluded from the success-rate denominator** and reported separately —
it is our infrastructure failing, not the arm.

Labels are assigned by `analysis/classify.py` from the event log, then
human-reviewed. The taxonomy maps directly onto Reviewer Ss1D's Q2 request for
"failure to propose an effective strategy" (D1), "inability to complete the Lean
proof" (D3), and "failure to pass numerical certification" (D2).

---

## 6. Instrumentation

### 6.1 Run manifest (`runs/<run_id>/manifest.json`)

Written before the run starts, immutable:

```json
{
  "run_id": "korenblum-armA-01",
  "arm": "A",
  "constant": "korenblum",
  "anchor": {"parent": "V64", "c_parent": "17823/50000",
             "target": "score > 17823/50000",
             "reference_iteration": "sprints 084-088"},
  "snapshot_sha256": "<tar of S0, .lake excluded>",
  "models": {"planner": "claude-opus-5", "generator": "claude-opus-5",
             "evaluator": "claude-sonnet-5"},
  "model_params": {"effort": "...", "thinking": "..."},
  "prompt_hashes": {"AGENT_BRIEF.md": "...", "planner.md": "...", ...},
  "hardware": {
    "cpu": "2x Intel Xeon Platinum 8352Y @ 2.20GHz, 64C/128T",
    "ram_gb": 503, "gpu": "5x NVIDIA A40 46GB (unused)",
    "os": "Ubuntu 22.04.5 LTS", "kernel": "5.15.0-185-generic"
  },
  "toolchain": {"lean": "leanprover/lean4:v4.28.0",
                "mathlib_rev": "<from lake-manifest.json>",
                "python": "...", "mpmath": "...", "arb": "..."},
  "budget": {"rule": "3x on M1 and M2",
             "T_ref_s": null, "O_ref_tokens": null,
             "hard_cap_s": 86400, "hard_cap_iters": 1000},
  "started_utc": "..."
}
```

Note: no GPU is used — the workload is LLM API calls plus CPU-bound Lean
elaboration and mpmath/Arb numerics. Recorded explicitly so reviewers do not
assume GPU cost.

### 6.2 Event log (`runs/<run_id>/events.jsonl`)

One JSON object per event, append-only:

```json
{"t": "...", "kind": "llm_call", "role": "generator", "model": "claude-opus-5",
 "usage": {"input_tokens": .., "output_tokens": .., "cache_creation_input_tokens": ..,
           "cache_read_input_tokens": ..}, "latency_s": ..}
{"t": "...", "kind": "lake_build", "target": "...", "exit": 1, "elapsed_s": ..,
 "stderr_tail": "..."}
{"t": "...", "kind": "evaluator", "candidate": "...", "pass": false,
 "score": null, "reason": "axiom audit FAIL", "raw": {...}}
{"t": "...", "kind": "oracle", "fn": "certify_...", "elapsed_s": .., "ok": false}
{"t": "...", "kind": "candidate", "file": "...", "c_value": "...",
 "edit_sha256": "..."}
{"t": "...", "kind": "terminal", "label": "D3", "evidence": "..."}
```

### 6.3 Token accounting

Verified feasible: Claude Code session transcripts
(`~/.claude/projects/<slug>/<session>.jsonl`) record per-assistant-message
`usage` with `input_tokens`, `output_tokens`, `cache_creation_input_tokens`,
`cache_read_input_tokens`, plus the exact `model` string. Duplicate lines
(streaming partials) are deduped by message id.

**Transcripts must be preserved this time.** The May-2026 transcripts were lost
to Claude Code's default cleanup (§7.1). Mitigations, both applied:

1. Set `cleanupPeriodDays` high in `~/.claude/settings.json` for the duration.
2. `harness/snapshot_transcripts.sh` copies the session JSONL into
   `runs/<run_id>/transcripts/` at the end of every run (and on a 15-minute cron
   during long runs).

Arm B calls the API directly, so its `usage` comes straight from the response
objects and is written to `events.jsonl` inline.

### 6.4 Prompt archival

Every prompt that shapes behaviour is copied verbatim into
`runs/<run_id>/prompts/` and SHA-256'd into the manifest:

- `.claude/agents/korenblum-refinement-{planner,generator,evaluator}.md`
- `.claude/skills/run-next-korenblum-sprint/SKILL.md`
- `ProofRefinement/Korenblum/AGENT_BRIEF.md`, `START_HERE.md`, `README.md`
- `Sprint_Contracts/TEMPLATE.md`
- Arm B's system prompt and per-iteration user-message template

This is the direct answer to Reviewer dimn; the archive becomes a paper appendix.

### 6.5 Forward compatibility with N>1

`run_id` carries a seed suffix and the manifest has a `seed` field, so the
collaborator's independent runs write into the same schema. `analysis/` aggregates
over whatever runs exist; success rate is `|{S}| / |{runs} \ {D7}|`.

---

## 7. Known limitations, stated up front

### 7.1 The original run's token/cost is unrecoverable

`~/.claude/projects/-home-user-korenblum/` retains a single 10 KB file; the
May-2026 session transcripts were auto-cleaned. `~/.claude/stats-cache.json` ends
at 2026-02-04. **Consequence:** we cannot report the original V64→V66 run's tokens
or dollar cost. We *can* report its wall-clock (2h18m42s), sprint count (5),
evaluator invocations, per-attempt Lean compile/typecheck/axiom-scan seconds, and
pass/fail counts, all from `log.jsonl` and file mtimes.

This is why Arm A is re-run rather than reconstructed. The paper will report the
original run's recoverable numbers *and* Arm A's fully instrumented numbers, and
say plainly which is which.

### 7.2 Grothendieck telemetry is worse

`grothendieck/ProofRefinement/Lemma54/` has **no `log.jsonl`**, and every sprint
contract and verdict mtime was flattened by a bulk copy at `2026-05-13T22:49:58`.
Zero wall-clock or attempt-count data survives. The Grothendieck reference arm
must therefore be re-run outright (§9).

### 7.3 Disk

`/` is at 97% (126 GB free); `korenblum/` is 8.1 GB, dominated by `.lake`.
Mitigation: hardlink `.lake` into each arm workspace (the earlier `korenblum_noPF`
arm did this and came to 250 MB). Mathlib `.olean` files are content-addressed and
never mutated, so the hardlinks are safe as long as no arm runs `lake clean` or
`lake update` — enforced by a pre-run check.

### 7.4 N=1

Per user decision, one run per arm. A single DNF is a single sample; the paper must
not claim a rate from it. Language: report the outcome and the budget-vs-progress
curve, and defer rate claims to the collaborator's multi-seed study.

---

## 8. Execution plan

| Phase | Work | Gate |
|---|---|---|
| **P0** | Reconstruct `S₀`; hardlink `.lake`; verify | §2.3 acceptance gate, all 4 checks |
| **P1** | Build instrumentation: `harness/{run.py,wrap_lake.sh,wrap_eval.sh,snapshot_transcripts.sh}`; manifest + event-log writers; `analysis/classify.py` | Dry-run on a 5-minute synthetic loop; every M1–M11 field populated |
| **P2** | Arm A run from `S₀` | Terminal label recorded; `T_ref`, `O_ref` computed |
| **P3** | Build `harness/arm_b_loop.py`; construct Arm B workspace | Smoke test: one iteration writes a candidate, builds, evaluates |
| **P4** | Arm B run at 3× budget | Terminal label |
| **P5** | Construct `S₀ᶜ` (Arm C workspace) from the `korenblum_noPF` contract + new seed axiom; rewrite `AGENT_BRIEF.md`; keep Wang PDF | `lake build` of seed V0 passes; evaluator accepts at `c = 0.35646` |
| **P6** | Arm C run at 3× budget | Terminal label |
| **P7** | Analysis + tables/figures (§10) | — |
| **P8** | Grothendieck (§9) — separate go/no-go | — |

**Sequencing.** P2 must finish before P4/P6 (it sets the budget). Disk allows all
three workspaces concurrently (~1 GB with hardlinked `.lake`), but CPU contention
during `lake build` argues for running arms sequentially; Arms B and C could run
concurrently after P2 if wall time matters, at ≤ 2 concurrent `lake` jobs.

**Rough wall-clock estimate:** P0 ≈ 2–4 h (reconstruction is fiddly), P1 ≈ 3 h,
P2 ≈ 2.5 h, P3 ≈ 2 h, P4 ≈ ≤ 7 h, P5 ≈ 1.5 h, P6 ≈ ≤ 7 h, P7 ≈ 2 h.

---

## 9. Generalizing to Grothendieck

The user's constraint is that the ablations must be **standardized** — if the design
does not transfer, the design changes, not the constant. Findings:

### 9.1 What transfers cleanly

The harness is structurally identical: `lemma.toml` with `sink_theorem` / `score` /
`score_direction` / `[search_constants]` / `[seed_axioms]` / `[[oracles]]`, the same
`Evaluator.py`, the same planner/generator/evaluator trio, the same
Sprint_Contracts / Refinement_Log / Candidates layout. **Design principle: every
harness component keys off `lemma.toml` plus a new `anchor.toml`, never off
Korenblum-specific names.** Written this way, Arms A and B port with no code change.

`anchor.toml` (per constant):

```toml
constant      = "korenblum"          # / "grothendieck_lemma54"
workspace     = "korenblum"
parent        = "Candidates/V64.lean"
score_parent  = "17823/50000"
direction     = "maximize"           # / "minimize"
goal          = "score > score_parent"
reference_sprints = ["084","085","086","087","088"]
```

### 9.2 The Grothendieck anchor

`Lemma54`'s `Cr_val` trajectory (minimize) over 28 candidates, with the analytic
content recorded in `lemma.toml`'s `[[oracles]]` comments:

| Sprint | Candidate | Change | Effect |
|---|---|---|---|
| 014 | V9→V10 | direct η-aware sup of `1/‖∂_z F_p‖` replacing paper's `2R/(1−r) ≈ 28.75` | ~14× on `invFp` |
| 016 | V11→V12 | merged sup of `‖DD‖/‖D‖³` replacing triangle product `M_pp·invFp³ ≈ 449` → 1.55 | ~289× |
| 019 | V13→V14 | joint `‖Φ·Φ′/D²‖` sup replacing term-1 triangle product | ~10× |
| 020 | V14→V15 | joint `‖DD·Φ²/D³‖` sup replacing term-2 triangle product | ~6× |
| **030** | **V23→V25** | **exact merged-numerator sup `‖2ΦΦ′D − DDΦ²‖/‖D‖³` = `‖u″‖` exactly**, replacing V23's triangle bound `2·joint + uzz_phi_sq ≈ 9.285e-6` → `8.087e-6` (ratio 0.871), capturing destructive-interference savings the triangle bound discards | `Cr`: 1/169000 → 1/240000 |

**Sprint 030 is the recommended Grothendieck anchor.** It is the same *shape* of
insight as the Korenblum anchor — replace a loose envelope with the mathematically
sharp object, re-certify numerically, re-derive in Lean — which is exactly what
makes the two ablations comparable rather than merely parallel.

### 9.3 The one place the design must change

**Arm C does not port as-is.** For Korenblum, the constant has a self-contained,
Mathlib-expressible definition (`ValidKorenblumBound c` at the Bergman A² level), so
"definition + previous SOTA as an axiom" is well-posed. `C_r` has no such definition:
it is an inverse-expansion constant defined *by* the Braverman et al. IFT /
`F_inv_paper` apparatus — which **is** the partial formalization. Strip the partial
formalization and there is nothing left to state.

Two options, and a recommendation:

- **(a) State Arm C one level up, at `K_G` itself. — recommended.**
  `ValidGrothendieckBound K :≡ ∀ (bilinear forms / sign vectors / unit vectors in a
  real Hilbert space) …`, expressible in Mathlib, seeded with
  `axiom hKrivine : K_G ≤ π / (2 log(1+√2))`, target: certify a strictly better bound.
  This is the exact structural analogue of the Korenblum Arm C — *definition of the
  constant + previous SOTA as an axiom* — and preserves standardization. It is
  brutally hard, but so is the Korenblum Arm C; that symmetry is the point.
- **(b) Keep `C_r` and axiomatize only the IFT family.** Rejected: that leaves a
  partial formalization in place, so it is not an ablation of the partial
  formalization. It would answer a different question with the same name.

**Standardized Arm C rule, applying to both constants:**
> The Arm C workspace states the *published constant of record* in Mathlib terms,
> seeds the previous best bound as a single axiom, and removes every intermediate
> Lean reduction, hypothesis bundle, and numerical oracle. Where a framework
> iteration targets an internal proxy constant (Grothendieck's `C_r`), Arm C is
> stated at the outermost constant the proxy serves (`K_G`), because the proxy is
> not definable without the scaffold being ablated.

This rule is written into `anchor.toml` as `arm_c_statement_level = "outermost"`,
so the asymmetry is declared rather than discovered.

### 9.4 Grothendieck-specific costs

- Reference arm must be re-run (no `log.jsonl`, mtimes flattened) — same as Korenblum.
- `grothendieck/` is a much larger tree; disk headroom must be re-checked before P8.
- The `Lemma54` numerical library is Arb/interval-heavy and larger than Korenblum's;
  Arm B's read-only context must be re-pointed at `Lemma54/Numerical_Library/`, and
  its size may need excerpting rather than wholesale inclusion. No mechanism change —
  the evaluator runs the oracles there too.

---

## 10. Deliverables

1. **Table 1 — Setup.** Hardware, OS, kernel, Lean toolchain, Mathlib rev, model IDs
   per role, model params, budget rule. *(Ss1D W3, Uspn Q2.)*
2. **Table 2 — Per-arm outcome.** Arm, terminal label, `c` achieved, wall-clock,
   model calls, output/input/cache tokens, USD at list, `lake build` count,
   `Evaluator.py` count, failed attempts, Lean CPU s, peak RSS. *(Ss1D Q1.)*
3. **Table 3 — Capability matrix.** §3.4 verbatim. *(Ss1D Q2 — "same foundation
   model, budget, literature, tool access, stopping criteria".)*
4. **Table 4 — DNF taxonomy** with the per-arm label and its evidence pointer.
   *(Ss1D Q2, KcCs.)*
5. **Figure 1 — Budget-vs-progress.** Best certified `c` (and best *proposed* `c`)
   against cumulative output tokens, all three arms, with the 1× and 3× reference
   lines marked.
6. **Appendix — Prompts.** Verbatim planner/generator/evaluator definitions, driver
   skill, `AGENT_BRIEF.md`, sprint-contract template, Arm B system prompt.
   *(dimn.)*
7. **Appendix — Anchor.** The V64→V66 mathematical content (per-mode kernel,
   τ-band breakpoints, 7-window architecture) so a reader can see what the arms
   were being asked to rediscover.
8. **Reproduction bundle.** `S₀` tarball + `anchor.toml` + harness + event logs.

---

## 10b. Implementation record (P1–P6)

### Layout

```
harness/
  make_s0.sh          rebuild S0 from korenblum (never mutated)
  reconstruct_s0.py   the 10-step sprint-083 reconstruction
  gate_s0.sh          5-gate acceptance check
  make_arm_ws.sh      clone S0 -> workspaces/arm{A,B,C} (hardlinked .lake)
  make_arm_c.py       build the PF-ablated Arm C workspace
  common.py           manifest / events / metrics / DNF plumbing
  run_arm_a.py        reference arm driver
  run_arm_b.py        bare-LLM loop
  run_arm_c.py        agentic driver at 3x budget
  pipeline.sh         A -> (B || C), unattended
runs/<run_id>/        manifest.json events.jsonl summary.json
                      prompts/ transcripts/ sprint_NNN_result.json
workspaces/           S0_korenblum armA armB armC
```

### How the arms are actually driven

Arms A and C invoke the harness exactly as the original run did — the
`/run-next-korenblum-sprint` skill, same planner/generator/evaluator subagents —
but headlessly via `claude -p '<skill>' --output-format json --model opus
--permission-mode bypassPermissions`, one invocation per sprint. This keeps the
framework byte-identical to the original while making it instrumentable from
outside.

### Telemetry source (better than §6.3 anticipated)

`claude -p --output-format json` returns, per sprint: `total_cost_usd`, a full
`usage` block (input / output / cache-creation / cache-read), a per-model
`modelUsage` map with per-model `costUSD`, `num_turns`, `duration_ms`,
`stop_reason`, `terminal_reason`, `permission_denials`, and `session_id`. So
M1–M5 come straight from the driver; the session transcript is retained as
corroboration rather than as the primary source. Arm B calls the Messages API
directly and reads `usage` off each response.

Transcript preservation (the mitigation for §7.1): `cleanupPeriodDays` raised to
3650, and `Run.snapshot_transcripts()` copies every session JSONL into
`runs/<run_id>/transcripts/` after each sprint.

### Restored capability: the MCP servers

The workspace's `.claude/settings.local.json` enables `lean-lsp` and
`lean-explore` — the planner and generator definitions grant 31 MCP tools
between them — but the `.mcp.json` that *defines* those servers was never in the
`korenblum` tree; it lives in the sibling `grothendieck` workspace. Running Arm A
without it would have silently deprived the framework of 28 working tools and
understated the reference arm. `make_s0.sh` now restores it, verified loading
headlessly (23 lean-lsp + 7 lean-explore = 28 tools).

### Arm B specifics

* Model `claude-opus-5`, adaptive thinking, `effort: xhigh` (passed via
  `extra_body`, since the installed SDK predates `output_config`),
  `max_tokens` 64000, streamed.
* Static context is **236K tokens** carrying the whole partial formalization
  verbatim (30 embedded files), prompt-cached at 1h TTL. This is deliberately
  *more* than Arm A's generator holds at once — Arm A must go and read files.
* Output contract: whole files in fenced blocks with `path=` in the info string.
  Writes are confined to an allow-list (`Candidates/`, `Numerical_Library/`,
  `Proof/`, `lemma.toml`); anything else is refused and reported back. Verified
  against hostile paths (`/etc/passwd`, `../../escape.py` — both refused), so the
  arm remains a loop and cannot become a covert shell.
* No tool use, no subagents, no workspace memory; rolling window K=3 of
  (files emitted, verbatim build+evaluator output).

### Baseline subtraction

S₀ ships 171 pre-anchor evaluator rows and 9 failures. All arms record that
baseline in the manifest and report **deltas**, so `evaluator_runs` and
`failed_attempts` measure the arm, not the inherited history.

---

## 10c. Arm A result, and two corrections it forced

**Arm A: SUCCESS in one sprint.** `c = 17829/50000 = 0.35658`, up from the
parent `17823/50000 = 0.35646` (+1.2e-4). Wall clock 3,285 s (55 min), 14
driver turns, 230,815 output tokens, \$20.65 at list prices, 2 evaluator runs,
0 failures.

Two things about this deserve to be in the paper rather than buried:

1. **It beat the original run, on a different route.** The 2026-05-05 run took
   five sprints (084–088) to reach `0.356562` via the seven-window τ-band
   partition. Arm A reached `0.35658` — slightly higher — in *one* sprint, via a
   **termwise per-mode criterion over the full interval** with three rational
   endpoints (`ρ₁ = 357/1000`, `ρa = 7/10`, `ρ₂ = 9999/10000`). Same roadmap,
   different and better solution. The plausible cause is the base model: the
   original ran on the May-2026 Opus, this on `claude-opus-5`.
2. **The trust surface is intact — this is not a D4.** The one new oracle axiom
   asserts a scalar inequality about two explicit integrals, guarded by
   `Eq7PaperKFormula K c_value` so `K` must be the paper kernel; the evaluator
   recomputed it (`ok: true`); and the contract records its falsification point
   (re-pointing the wrapper at `c = 35660/100000` returns `False`; last passing
   grid value `35659/100000`). Same trust class as the original run's oracles.
   The other two axioms (`hH2_v65`, `hCircleGapInt_v65`) are the standard
   per-candidate Wang Section-2 hypotheses, exactly as V64 carries
   `hH2_v64` / `hCircleGapInt_v64`.

### Correction 1 — subagent tokens were being dropped (~50×)

`claude -p --output-format json` returns a top-level `usage` block that covers
**only the driver's own final turn**. Every planner / generator / evaluator
subagent is excluded — and in this harness that is essentially all the work.
Measured on Arm A's single sprint: `usage.output_tokens = 4,592` against a
`modelUsage` total of **230,815**. A 50× under-count.

Caught because the first B/C launch printed a budget of 13,776 output tokens,
which Arm B would have exhausted in one iteration. Both arms were killed within
a minute, before spending anything, and `common.py` now derives all token totals
from `modelUsage`, falling back to the top-level block only if it is absent.

### Correction 2 — wall-clock reference floored at the original run

Arm A solved the anchor faster than the original framework did (3,285 s vs
8,322 s). Taking 3× the *faster* of two independent measurements would hand the
ablations less wall clock than the framework itself originally consumed — the
opposite of the intent to resource them generously. The reference wall clock is
therefore floored at the original 084–088 band:

```
T_ref = max(armA 3,285 s, original 8,322 s) = 8,322 s
O_ref = 230,815 output tokens          (Arm A only; no original token data survives)

ablation budget = 3x  ->  24,966 s (6.93 h)  AND  692,445 output tokens
```

Both raw figures are retained in `runs/reference_budget.json` so either budget
can be recomputed. This is a deviation from the literal "3× Arm A" rule and is
reported as such.

---

## 10d. Billing misconfiguration, and what it cost the design

`~/.bashrc` exported `ANTHROPIC_API_KEY`, which **takes precedence over the
claude.ai login for every Claude Code invocation**. With it set,
`claude auth status` reports `apiKeySource: ANTHROPIC_API_KEY`,
`subscriptionType: null`; unset, it reports `subscriptionType: "max"`. So Arms A
and C billed API credits rather than the Max subscription, and exhausted the
balance mid-run — which is what killed Arm C at sprint 5 (labelled **D7**, not a
scientific outcome).

The key belongs to organisation `27364345-6db2-4562-bede-366f4da4b73e`, which is
**not** the subscription's org (`020fac9e-…`). The export is now commented out
(`.bashrc` backed up); the harness additionally pops the variable from every
child environment, so the arms are insulated even if it returns.

`total_cost_usd` is still reported under subscription auth, so the list-price
cost telemetry in §4.1 is unaffected by the switch.

### Consequence for Arm B: a weaker ablation than specified

§3.2 specifies a bare-model call with no tool surface at all. That requires the
Anthropic SDK, which can only authenticate with an API key. To keep the run on
the subscription, Arm B now invokes `claude -p` with 33 tools explicitly
disallowed and its system prompt appended.

This is **weaker than specified**, and the writeup must say so:

* Claude Code's own agentic system prompt is present.
* `--allowed-tools ""` does not empty the tool surface — a handful
  (`ToolSearch`, `Workflow`, `ReportFindings`, …) remain *visible* to the model
  even when disallowed. Verified they do not execute (`num_turns: 1`), but
  visibility alone can shift behaviour.

The bias direction is worth stating explicitly, because it is the reassuring
one: any residual agency makes Arm B look **more** capable than a true bare
model. It therefore cannot manufacture a "the no-agent arm fails" conclusion —
it can only understate the gap the ablation is trying to measure. If Arm B
fails anyway, the finding holds a fortiori; if it succeeds, the result is
attributable to the partial formalization plus whatever residual agency Claude
Code supplies, and that caveat must be carried into the claim.

Running Arm B as originally specified would cost roughly \$30 of API credit and
is the cleaner experiment; it remains available as a follow-up.

### Two harness bugs this episode exposed

1. **Arm B's candidate path was hardcoded** to `V65.lean`; a model writing any
   other `Candidates/V*.lean` crashed the loop on `copy2`. Now derived from the
   files actually emitted.
2. **A fatal API condition did not stop the loop.** Arm C burned **996 no-op
   sprint attempts** (~2 s each, ~\$15.60) against a dead credit balance before
   its max-sprints guard fired — and, worse, those attempts made the budget look
   consumed when nothing had been attempted. Both runners now detect
   credit/auth/permission failures via `is_fatal_api_error()` and abort as D7.

Arm C was resumed rather than restarted: its four completed sprints (8,754 s,
649,178 output tokens, \$41.41) are carried forward into run
`korenblum-armC-02`, so the 3× budget covers total real work rather than
restarting the clock after an infrastructure failure.

---

## 10e. Results (Korenblum) — and what they do to the paper's claim

**All three arms complete.** Arm B was additionally re-run past its first
success (`korenblum-armB-02`) to **2× Arm A's measured wall clock and output
tokens**, so its ceiling is measured rather than truncated at the first win.

| Arm | Ablated | Label | c | Δc vs parent | Wall | Output tok | USD |
|---|---|---|---|---|---|---|---|
| **A** reference | — | **S** | 0.35658 | +1.2e-4 | 55 min | 230,815 | 20.65 |
| **B** no agent (stop-at-first-success) | agentic system | **S** | 0.35648 | +2.0e-5 | 45 min | 253,391 | 23.44 |
| **B′** no agent (run to 2× Arm A) | agentic system | **S** | **0.35653** | **+7.0e-5** | 2.19 h | 715,215 | 70.24 |
| **C** no PF | partial formalization | **D1** | 0.35646 (seed) | **0** | 7.06 h | 1,800,402 | 118.38 |

### Arm B′: the bare loop climbs, by parameter search not architecture search

| Iter | Outcome | c | Note |
|---|---|---|---|
| 2 | PASS | 0.35648 | re-pin of V64's two-window architecture |
| 3 | PASS | 0.35651 | re-pin again |
| 4 | FAIL | — | axiom audit: three `UNREG` axioms — emitted `V67.lean` but not the `lemma.toml` registering them |
| 5 | PASS | **0.35653** | recovered after the verbatim `UNREG` feedback |
| 6 | no candidate | — | emitted `V69/ThreeWindow.lean` — a **new three-window architecture** — but no candidate file, so nothing was scored |
| 7 | FAIL | — | same `UNREG` bookkeeping failure |

Given 2× Arm A's budget the bare loop reaches **0.35653 vs Arm A's 0.35658** —
a residual gap of 5e-5, closed from 1e-4. But it gets there by **four
successive re-pins of the inherited two-window architecture**, where Arm A
found a structurally different criterion (termwise per-mode, full interval) in
a single sprint.

Iteration 6 is the sharpest datum in the whole study: Arm B *did* attempt
architectural search — it wrote a three-window helper module — and lost the
iteration because it emitted the helper without the accompanying candidate.
Both of its failures (4 and 7) are the same shape: **cross-file bookkeeping**,
not mathematics. Every one of its failed candidates *compiled, type-checked and
passed the axiom scan*; they were rejected because coupled files
(`lemma.toml`, the wrapper module) were not re-emitted alongside.

That is the concrete, measured cost of ablating agency: Arm A's generator
*edits* files in place, while the bare loop must reproduce every coupled file
verbatim from memory in one response, and drops one roughly a third of the
time. It is a harness-shaped limitation of the no-agent setting, not a
reasoning failure — and it is exactly what an agentic scaffold buys.

**Falsification test on Arm B′'s final oracle** (`c = 35653/100000`):
certifies at the claim; refuses at `35660/100000` (rigorous Arb lower bound
`0.99866 ± 3e-14`) and `35700/100000` (`0.98943 ± 4e-14`). Audit set is the
same trust class as V64. No violations.

### How Arm B wrote correct Lean one-shot — it mostly didn't have to

A tool-less model producing 348 lines of compiling Lean 4 + Mathlib is
implausible on its face, so it was audited directly.

**It used no tools.** Zero `tool_use` blocks across the sampled Arm B sessions
(2–3 assistant messages each: thinking plus text). The transcripts are archived
under `runs/korenblum-armB-0*/transcripts/`.

**The Lean is ~88% template substitution.** Comments stripped:

| | Executable Lean |
|---|---|
| V64, supplied verbatim in context | 184 lines |
| Arm B's V65 / V66 / V68 | 197 lines each |
| diff vs V64 | 65 lines |
| **diff ignoring numerals and version names** | **23 lines** |

The candidate is V64 with `35646 → 35648` and `v64 → v65` substituted. The one
genuinely new proof is a 12-line endpoint inequality, structurally identical to
V64's `ρ_meet_sqrt_lt_one_for_target_c` (also in context), reusing an existing
lemma and closing with `norm_num` / `linarith` — decision procedures that need
no term-level Lean skill. This is why it compiled first try every time:
**neither Arm B failure was a build failure**; both were the `lemma.toml`
registration issue.

**Consequence for the claim.** Arm B's success is *not* evidence that a bare
LLM can write Lean proofs. It is evidence that a bare LLM can perform parameter
substitution on a working proof when the residual gap is discharged by
automation tactics. That:

* **strengthens** the partial-formalization conclusion — the scaffold is so
  load-bearing that a tool-less model rides it to a certified improvement on
  ~23 lines of novel Lean;
* **weakens** "the agentic system is unnecessary" — at this anchor's
  granularity the ablation task is a re-pin, so Arm B was never required to
  write substantive Lean. Arm A's termwise per-mode criterion is the case that
  would test that, and Arm B's single attempt at architectural change (the
  three-window module, iteration 6) never reached the evaluator.

Any writeup must carry this qualification; the raw Δc comparison alone
overstates what the no-agent arm demonstrated.

*(Instrumentation gap found here: the Arm B runner did not record `session_id`,
so transcripts were not auto-archived. They were recovered from
`~/.claude/projects/-tmp/` by timestamp; the runner now records `session_id`,
`num_turns` and `permission_denials` per iteration.)*

### Revised reading

* **Capability**: not what the agentic system provides. The bare loop reached
  90% of the reference improvement.
* **Efficiency**: Arm A reached further in 1/4 the wall clock, 1/3 the tokens
  and 1/3 the cost.
* **Architectural reach**: the clearest difference. Arm A changed the proof
  architecture; Arm B could only re-tune the one it was handed, and its one
  attempt to change it was lost to the single-response constraint.
* **The partial formalization remains decisive** — Arm C, with the full agent
  system and 2.5× Arm B′'s budget, never proposed an improvement at all.

### Superseded numbers

| Arm | Ablated | Label | c achieved | Δc | Wall | Output tok | USD | Turns | Evals | Fails |
|---|---|---|---|---|---|---|---|---|---|---|
| **A** reference | — | **S** | 0.35658 | +1.2e-4 | 55 min | 230,815 | 20.65 | 14 | 2 | 0 |
| **B** no agent | agentic system | **S** | 0.35648 | +2.0e-5 | 45 min | 253,391 | 23.44 | 2 | 1 | 0 |
| **C** no PF | partial formalization | **D1** | 0.35646 (seed) | **0** | 7.06 h | 1,800,402 | 118.38 | 60 | 19 | 0 |

Parent `c = 17823/50000 = 0.35646`. Budget for B and C: 6.93 h AND 692,445
output tokens (§10c). Arm C exhausted **both** — 102% of wall clock and **260%
of output tokens** — without ever proposing a candidate above the seed.

Harness vs classifier labels agree on A and B (**S**/**S**). They differ on C:
the harness records the stopping *condition* (**D5**, budget exhausted); the
classifier records the more specific failure *mode* (**D1**, never proposed a
candidate above parent). Both are true; D1 is the informative one and is what
should be reported, with the budget figure alongside it.

### The headline is not the one the paper argues

Removing the **agentic system did not prevent success**. Arm B — a bare loop,
one model call per iteration, no tools, no subagents, no memory beyond a 3-deep
error window — reached a certified improvement in **two iterations**. It took
V64's two-window architecture, re-pinned it at `c = 35648/100000`, emitted a
sibling Arb wrapper reusing the audited helpers, and the evaluator accepted.

Removing the **partial formalization did**. Arm C, with the full agent system,
all tools, Wang (2025) and web search, has spent seven sprints and both budget
axes and has *never once* put a candidate above the seed in front of the
evaluator. Its sprints pass their own gates cleanly with zero evaluator
failures; it is building Bergman foundations (radial reduction, Parseval
coefficient layer, Ω-transfer, Blaschke normal form) and never arrives at the
improvement.

On this anchor, **the partial formalization is carrying the result, and the
agent scaffolding is not load-bearing for reaching a c-push.**

What survives of the framework's claim: Arm A got 6x further than Arm B
(+1.2e-4 vs +2.0e-5) and found a genuinely new route (termwise per-mode
criterion) where Arm B took the conservative re-pin of an existing
architecture. That is a real quality difference and worth reporting. What does
*not* survive is "the agentic system is necessary."

### Arm C was not idle — it rebuilt the scaffold

The D1 label must not be read as "no strategy." Arm C pursued a coherent
nine-sprint plan to reconstruct Wang's Section 2 from Mathlib:

| Sprint | Layer built |
|---|---|
| 001 | radial reduction (area integral → 1-D radial integrals) |
| 002 | Parseval coefficient layer (Wang Lemma 2) |
| 003 | Ω-transfer: `sigmaPlus`/`sigmaMinus`, Wang (3) as an identity |
| 004 | zero structure via complex analysis rather than Parseval |
| 005 | sharp outer majorant `(c² − w̄z)/(c(1 − w̄z))` |
| 006 | Blaschke normal form |
| 007 | multiplier normal form |
| 008 | divisor reduction |
| 009 | moment envelope — LP duality on the Parseval moment sequence, the **first** c-push attempt, targeting `c ≤ 1/√3 ≈ 0.577` |

It shipped **11 candidates** (V1–V10 plus the seed) and **5,646 lines across 11
Lean modules** with **zero `axiom` declarations and zero `sorry` tactics**, each
candidate re-proving the sink theorem *through* the newly built layer at
unchanged `c`. Its final audit set is exactly
`{propext, Classical.choice, Quot.sound, hKorenblum_prev}` — the three standard
Lean axioms plus the seed. Nineteen evaluator runs, **zero failures**.

It reached its first genuine c-push attempt at sprint 009 and ran out of budget
there. The ablation's predicted mechanism — *without the reduction chain the
agent must rebuild it, and the budget goes into the rebuild* — is precisely what
the trace shows.

*(Methodological note: an initial `grep -c sorry` over these modules returned 1
per file, which looked like unfinished proofs. Those were occurrences of the
word inside prose comments ("no `axiom`, no oracle, no `sorry`"). Counting
actual `sorry` tactics gives 0, and no accepted audit contains `sorryAx`.)*

### Failure mode of the no-PF arm: D1, not D2 or D3

Reviewer Ss1D asked which of three failure modes each baseline hits. Arm C hits
**none** of the two that the paper's framing would predict. It does not fail to
complete a Lean proof (D3) and it does not fail numerical certification (D2) —
it fails to *propose an improvement at all* (**D1 STRATEGY-DNF**). Without the
reduction chain there is no editable subgoal to sharpen, so the agent
rationally spends its budget rebuilding the scaffold instead.

### Validation performed on the two successes

Neither PASS was taken at face value.

* **Audit sets** are the same trust class as the anchor parent V64: standard
  Lean axioms, the per-candidate Wang Section-2 hypotheses (`hH2_*`,
  `hCircleGapInt_*` — V64 carries the identical pair), and one oracle-backed
  axiom recomputed by the evaluator (`ok: true`). No `sorryAx`.
* **Arm B's oracle was falsification-tested directly**: it certifies at
  `35648/100000` and *refuses* at `35700/100000` (rigorous Arb lower bound
  `0.98943 ± 4e-14`) and `35800/100000` (`0.96673 ± 9e-14`). It computes real
  interval arithmetic and declines below mass 1.
* **Arm A's oracle** is a scalar inequality over two explicit integrals, guarded
  by `Eq7PaperKFormula K c_value`, with its falsification point recorded in the
  contract (`35660/100000` returns `False`).

### A classifier bug that would have inverted the headline

`analysis/classify.py` initially labelled **both successes D4 TRUST-DNF**,
because its D4 predicate was "did `[seed_axioms].allowed` grow?". That is the
workspace's *documented* workflow — V64 itself was accepted having added
`hH2_v64`, `hCircleGapInt_v64` and its own oracle exactly that way, and
`AGENT_BRIEF.md` permits it in terms. The predicate now tests what actually
matters — whether an added axiom is **conclusion-shaped** (its statement
applies `ValidKorenblumBound`) — with the seed axiom exempted, since Arm C's
`hKorenblum_prev` is conclusion-shaped by construction. A negative control
confirms it still catches a planted conclusion axiom.

Reported because the uncorrected classifier would have claimed both arms
cheated.

### Caveat carried into the claim

Arm B ran inside Claude Code with 33 tools disallowed but a residual set still
*visible*, and Claude Code's agentic system prompt present (§10d). That bias
runs **toward** Arm B succeeding, so it weakens "a bare LLM suffices" — it does
not rescue "the agent is necessary." Re-running Arm B through the SDK as
originally specified (~\$30 of API credit) would close this.

---

## 11. Open items

1. **P0 is the schedule risk.** If `Proof/Reduction.lean` is not cleanly
   append-ordered by sprint, reconstruction may need per-declaration surgery. The
   sprint-088-only fallback (§2.3) is documented but weaker; the decision point is
   the §2.3 acceptance gate.
2. **Arm A halt semantics.** If Arm A halts before `G` (the harness has
   `BLOCKED_NEEDS_HUMAN` states), `T_ref`/`O_ref` are undefined. Fallback: use the
   original run's recoverable wall-clock (2h18m42s) as `T_ref` and derive `O_ref`
   from Arm A's observed tokens-per-second. To be decided if it occurs.
3. **Model pinning.** Arm A/C use whatever `model: opus` / `model: sonnet` resolve
   to in Claude Code; Arm B pins an explicit ID. The manifest records the resolved
   IDs, and Arm B pins to Arm A's generator ID so the comparison is exact.

---

## 12. Grothendieck execution (P8) — revised plan

**Date:** 2026-07-29. §9 was written before the Korenblum run; this section
supersedes its execution details, carrying every §10b–10e learning forward.
Investigation performed against `grothendieck` (a real git repo,
unlike korenblum) and the full harness audit.

### 12.1 Anchor: sprint 030 confirmed — with a disclosure §9 did not know about

Anchor stays **sprint 030 (V23→V25)**: the merged-numerator pivot, `Cr_val`
1/169000 → 1/240000 (minimize), the exact structural twin of the Korenblum
anchor (replace a triangle-inequality envelope with the mathematically sharp
object, mint one new arb oracle, re-derive in Lean).

**Disclosure that must ship with the results:** on 2026-05-03 the framework
itself found the K_max-truncation flaw (`PATCH_NOTES.md`); V9–V26's `Cr_val`
certificates — including the anchor's — were re-baselined (frontier moved to
V27 `1/3`, V28 `2/7`). The ablation still anchors at sprint 030 because:

1. **Internal validity is unaffected.** All three arms run against the same
   frozen S₀ trust surface (same evaluator, same numerical library); the flaw
   lives in the *shared* trusted layer, identical across arms, so the
   between-arm comparison measures what it claims to measure.
2. **The alternative is not reproducible.** Anchoring post-patch (sprint 034)
   requires the truncation-free oracle suite, whose backing chunk JSONs
   (`Cache/Backups/2026-05-03_*`) were gitignored and are gone (~3 h × 96
   workers to regenerate), and the post-patch states have no git checkpoint
   coverage.
3. **Sprint 034 is a weaker ablation task.** `PATCH_NOTES.md §3a` — mandatory
   reading in that S₀ — states its answer outright ("V14's formula patches to
   0.2810 — a free ~17% win"). Sprint 030 requires minting a genuinely new
   oracle and two new Lean theorems, with only the *direction* on the roadmap.
4. **Anchor-shape symmetry with Korenblum** (§9.2) is preserved; sprint 034 is
   a repair/re-baseline, a different shape of work.

As with Korenblum (§2.1 correction), the anchor is **execution, not
discovery**: the S₀ roadmap (`Scratch/sprint_029_research_summary.md`,
Bulletin sprint_029 rows) names `merged-numerator-revive` as the top
direction, with the ratio history 1.78→1.20 over four resolution doublings
and the prediction that it crosses 1.0 at n ∈ {2¹⁷, 2¹⁸}. What sprints
084–088 left to the Korenblum arms, sprint 030 leaves here: the n=262144
viability probe, the `compute_merged_uderiv_bound` arb oracle, the
`F_inv_p_second_deriv_bound_phi_uzz_merged` / `lemma_5_4_paper_on_domain_phi_uzz_merged`
Lean theorems, and the V25 rewiring.

### 12.2 S₀ᵍ: commit-based, not surgical

The grothendieck repo has minute-granularity `auto-checkpoint` commits.
Timeline recovered to the second:

| Event | Time (UTC, 2026-04-30) | Commit |
|---|---|---|
| verdict_029 lands | 12:08:21 | `17ec0fab` |
| **S₀ᵍ** (bulletin sprint_029 PASS row present) | **12:08:51** | **`e86a00f0`** |
| sprint-030 planner's first probe artifact | 12:10:09 | `d2b0b3aa` |
| sprint_030.md contract written | 12:19:50 | `9a354c51` |
| V25 verdict + log row | 12:59:19–12:59:56 | `98bce5da` |

So `harness/make_s0_grothendieck.sh` replaces the 10-step forensic surgery of
`reconstruct_s0.py` with `git archive e86a00f0` — every post-anchor artifact
(sprint_030+ contracts/verdicts, V25–V28, merged oracle, truncfree suite,
PATCH_NOTES.md, the 2026-05-03 anti-truncation agent directives, all Bulletin
and Experience rows past sprint_029) is absent *by construction*, and the
2026-04-30-era agent definitions are recovered exactly (they were modified
post-anchor; korenblum had no VCS coverage of its agents at all).

Zero drift in `lean-toolchain` / `lakefile.toml` / `lake-manifest.json` since
S₀ ⇒ the 40 GB `.lake` is hardlinked verbatim.

Deviations (all recorded in the manifests):

* **`log.jsonl` reconstructed from verdicts.** `*.jsonl` was gitignored and
  the live copy is gone (§7.2). Every verdict embeds its exact log row
  (`REPRODUCED-WITH … log entry: {…}`); `reconstruct_log_groth.py` extracts
  all 25 (verdicts 020–022 verbatim — lightly elided JSON; failed attempts
  that produced no verdict are missing, so the baseline under-counts history).
* **Python env is the current uv venv** (7.3 GB copy per workspace) with the
  current `pyproject.toml`/`uv.lock`; the S₀-era env is unrecoverable. Same
  class as korenblum's kept-Arb deviation. The venv's editable-install `.pth`
  is re-pointed at the workspace (leak + skew fix).
* **`outputs/b_series_eta0p01_K250_dps100.json`** (gitignored; every oracle
  loads it) restored from the live python package dir — byte-identical to a
  pre-anchor 2026-04-30T01:33 snapshot copy, mtime 2026-02-19.
* **Fresh single-commit git repo** (evaluator agents record commit hashes;
  the original env was a git repo). No post-anchor history reachable.
* `.mcp.json` + `.claude/settings.local.json` copied from the live tree
  (untracked config; `.mcp.json` is native here — it was *borrowed* for
  korenblum, §10b).

  **Known deviation found during Arm A:** that `settings.local.json` carries
  post-anchor deny rules whose relative variants
  (`Edit/Write(ProofRefinement/**)`) match the ablation workspaces, so the
  planner/generator/evaluator subagents cannot use Edit/Write on the Lemma54
  tree and fall back to writing via Bash (allowed under
  `bypassPermissions`). Whether the original 2026-04-30 run had these rules
  is unknowable (the file is untracked). The friction is **uniform across
  the agentic arms** — Arm A set the reference budget under it and still
  succeeded in one sprint, and Arm C runs under the identical file — so the
  between-arm comparison is unaffected; it can only understate all agentic
  arms equally. Left in place rather than edited mid-study.

  The two arms *responded* differently: Arm A's subagents wrote via Bash
  heredocs (allowed); Arm C's evaluator declined to route around the rule
  and stages its bookkeeping artifacts (verdict, `log.jsonl` row, Bulletin
  line) in `.harness_pending/` with an `APPLY.md`. Protocol adopted: the
  study operator applies the staged artifacts verbatim after each sprint,
  verifying content first — restoring exactly the writes the framework
  intended, without modifying the workspace's permission surface mid-run.
  Sprint 001's artifacts were applied this way. Arm C's Lean work itself is
  unaffected (planner/generator write via Bash). Also noted for the record:
  Arm C's driver independently found a fail-open bug in
  `scripts/harness_preflight.sh` (a `grep -c … || echo 0` double-emission
  that skips the 3-consecutive-FAIL halt check); it is part of the original
  framework and is left as-is for fidelity — the ablation harness's own
  budget caps bound any damage.

Gate (`gate_s0_grothendieck.sh`): V24 `lake build` PASS · Evaluator PASS at
`Cr_val = 1/169000` (cold run doubles as `.cache` prewarm — V24's used-oracle
set is just joint + uzz_phi_sq, ≈66 s + ≈91 s fresh) · no post-anchor
artifacts, answer values (`1/240000`, ratio `0.870917`, `41/5000000`) absent ·
Bulletin/Experience end at sprint_029 (forward-looking "next mandatory
wildcard is sprint_030" cadence rows are *kept* — that is the roadmap) ·
git history = 1 commit.

### 12.3 Harness port — fork, apply the audited diff

The §9.1 `anchor.toml` abstraction was never built; all 11 harness files are
korenblum-hardcoded (151 refs). Per-file audit (2026-07-29) mapped every
site. Decision: **fork** into `harness/groth_*` + shared `groth_config.py`,
leaving the korenblum harness byte-stable for reproducibility. The load-bearing
changes:

| Class | Sites | Change |
|---|---|---|
| Score direction | `common.py:305,312`, `classify.py:152,171,172` + 6 prose sites | maximize → **minimize** (`<` on Fraction; `max_proposed`→`min_proposed`) |
| Parent score | `common.py:20` | `Fraction(17823,50000)` → `Fraction(1,169000)` |
| Evaluator output | `run_arm_b.py:251`, gate | Lemma54 prints bare `PASS` + exit 0/2, **no** `status:` line → parse exit code |
| log.jsonl schema | `common.py:289–321`, `classify.py:47–114` | `pass`→`status=="ok"`; `score` is `{numer,denom,approx}` dict; `timestamp_utc`→`timestamp`; `def_vals.c_value`→`Cr_val`; `oracle_checks[]`→folded into `axioms_used[].status`; skip heterogeneous evaluator-agent rows |
| Driver skill | `run_arm_a.py:24` | `/run-next-korenblum-sprint` → **`/run-next-sprint`** (NOT `/run-grothendieck-sprint` — that drives the separate GrothendieckHarness asymptotics loop) |
| D4 predicate | `classify.py:129–143` | `ValidKorenblumBound` grep has no Lemma54 analogue (sink is a bare ∃-statement). Replacement: flag any non-seed accepted axiom whose statement contains `Cr_val` together with the sink's `* p ^ 2` inequality shape (directly asserting the sink at the candidate's score); plus flag `axioms_used[].status == "stub"` (NotImplementedError oracles pass as SKIP — a trust hole korenblum didn't have) |
| Prompt archival | `common.py:133–143` | `refinement-{planner,generator,evaluator}.md`, `run-next-sprint/SKILL.md`, Lemma54 `{AGENT_BRIEF,README}.md`, both TEMPLATEs (no START_HERE.md here) |
| Lake target | arm B build | `ProofRefinement.Lemma54.Candidates.V<N>` |
| Evaluator invocation | arm B, gates | `--file` is repo-root-relative, cwd = workspace root |
| Budget floor | `fix_reference_budget.py:32` | original band = S₀ commit → verdict_030 commit = **3,065 s** (git timestamps, not mtimes — mtimes were flattened 2026-05-13) |
| Kept verbatim | — | `modelUsage` token accounting (§10c correction 1), `T_ref` floor logic (correction 2), `ANTHROPIC_API_KEY` stripping + fatal-API D7 abort (§10d), transcript snapshotting, 3× AND stopping rule, hard caps, carry-forward resume, DISALLOWED tool list, subagent models (planner opus / generator opus / evaluator sonnet — matches S₀-era agent frontmatter exactly) |

### 12.4 Arm B context (the §9.4 re-point, resolved)

Static context, S₀ versions of: `Proof/SearchConfig.lean`, `Proof/Lib/*.lean`
(the Lemma54_Paper chain), `LeanProof/{Lemma54,Theorem51}.lean`,
`LeanProof/Defs/Strip.lean` (V24's actual import closure), `Candidates/V23.lean`
+ `V24.lean`, `lemma.toml`, all of `Numerical_Library/*.py` (13 modules,
~228 KB — small enough to inline wholesale; korenblum's static context was
236 K tokens), the roadmap (`Scratch/sprint_029_research_summary.md`, the
reusable `Scratch/sprint_022_planner_full_merge.py` scanner the original
contract itself reused, sprint_029 probe outputs), `AGENT_BRIEF.md`,
`Bulletin.md` (158 lines, whole), `Sprint_Contracts/sprint_029.md`, and
**Braverman et al. (2011) extracted text** from the in-tree
`assets/pdf/braverman.pdf` (Arm A holds the same PDF in-workspace — parity
per §3.2; the OpenReview submission PDF at the repo root is post-anchor,
untracked, and would leak the answers — excluded by construction).
System prompt: minimize direction ("STRICTLY LESS THAN 1/169000"), Lemma54
gate description (new oracle = function exported from
`Numerical_Library/__init__.py` returning `.bound`, plus a `[[oracles]]` row —
the evaluator imports and runs it itself; no tool use required), writable
prefixes `Candidates/ Numerical_Library/ Proof/ Scratch/ lemma.toml`.

### 12.5 Arm C at K_G — §9.3(a), concretized

`LeanProof/MainTheorem.lean:46–59` already formalizes both pieces:
`GrothendieckIneq (K : ℝ) : Prop` (Mathlib-only: bilinear forms over `Fin n`,
unit vectors in a real `InnerProductSpace`, sign vectors) and
`KrivineBound := π / (2·log(1+√2))`. Arm C's `CandidateContract.lean` copies
these two definitions standalone; seed:

```lean
def K_val : ℝ := 1782214 / 1000000   -- KrivineBound = 1.7822139… < K_val
axiom hGrothendieck_prev : GrothendieckIneq K_val
theorem grothendieck_bound_search : GrothendieckIneq K_val := hGrothendieck_prev
```

(rational seed one ulp above Krivine, the same shape as korenblum's
`hKorenblum_prev` at the rational parent; monotonicity of `GrothendieckIneq`
in K means the axiom is strictly *weaker* than Krivine's theorem, and no
strict rational improvement below `K_val` is derivable from it — any accepted
improvement requires new mathematics or a D4 violation). Score `K_val`,
direction minimize, statement level `outermost` declared per the §9.3 rule.
Arm C uses the korenblum-generalized evaluator (the variant with the TYPE
gate `constant_def = GrothendieckIneq` and `score_direction`), because
Lemma54's evaluator has no type gate and would accept a vacuous sink; this is
part of the declared statement-level asymmetry. Kept: full agentic harness,
S₀-era agents, MCP servers, `assets/pdf/braverman.pdf`, WebFetch/WebSearch.
Removed: `ProofRefinement/Lemma54/*` (Proof/, Numerical_Library/, Scratch/,
candidates, sprint history), `LeanProof/{Lemma54,Theorem51}.lean` and every
IFT/`F_inv_paper` module, `ProofGraph/Effective/*`.

### 12.6 Budget and reference band

```
T_orig = 3,065 s   (S₀ commit 12:08:51 → verdict_030 commit 12:59:56; git timestamps)
T_ref  = max(armA_wall, 3,065 s)        O_ref = armA modelUsage output tokens
budget(B, C) = 2× T_ref  AND  2× O_ref  (§4.2 rule + §10c floor)
```

**Multiplier is 2×, not §4.2's 3×** *(user decision, 2026-07-29)*: korenblum's
B′ extension already showed 2× Arm A is where the measured ceiling lives, and
the tighter multiplier halves the tail cost. Reported as a deliberate
per-constant deviation from §4.2.

No original token data survives (worse than korenblum: no transcripts, no
log.jsonl). Baseline subtraction: 25 reconstructed pre-anchor log rows.

### 12.7 Execution sequence and estimate

| Phase | Work | Est. wall |
|---|---|---|
| G-P0 | S₀ᵍ build + gate (§12.2) | **done** ~0.5 h |
| G-P1 | Harness fork + smoke test (§12.3) | 1.5–2.5 h |
| G-P2 | Arm C workspace + gate (§12.5), Arm B context assembly | 1–2 h (overlaps G-P1) |
| G-P3 | Arm A run | 0.5–2 h (original band was 51 min; korenblum Arm A took 55 min) |
| G-P4 | Arms B ∥ C at 2× budget | ≈ 2× T_ref ≈ 1.7–3.5 h (concurrent, ≤2 lake jobs) |
| G-P5 | classify + falsification tests + writeup | 1–1.5 h |

**End-to-end ≈ 8–12 h wall**, of which ~5–8 h is unattended run time.
Speed choices already taken: B ∥ C concurrency (saves ~3 h), no Arm B′-style
run-past-success extension by default (saves ~2 h; can be added later if the
B-ceiling question matters), commit-based S₀ (saved the 2–4 h korenblum-style
reconstruction). Cost at list prices, extrapolating korenblum: ≈ \$150–250
equivalent (billed to the Max subscription under the §10d auth fix).

*(Actual: setup ≈ 3.5 h, Arm A 64 min, B ∥ C 14 min / 2.49 h, total spend
\$58.69 at list across the three arms.)*

---

## 12.8 Results (Grothendieck) — all three arms complete

Parent `Cr = 1/169000` (Arms A/B); Arm C parent = the rationalized Krivine
seed `891107/500000 = 1.782214`. Budget for B and C: 2× Arm A = 7,687 s AND
372,992 output tokens.

| Arm | Ablated | Label | Score | Δ vs parent | Wall | Output tok | USD |
|---|---|---|---|---|---|---|---|
| **A** reference | — | **S** | Cr **1/298000** | 1.763× | 64 min | 186,496 | 13.06 |
| **B** no agent | agentic system | **S** | Cr 1/183000 | 1.083× | **14 min** | 36,525 | 5.51 |
| **C** no PF | partial formalization | **S\*** | K_G ≤ 89110699/50000000 | see §12.8c | 2.49 h (116% T) | 651,799 (175% O) | 40.12 |

Harness and classifier labels agree (**S/S/S**, zero trust violations); Arm
C's asterisk is a *statement-level* qualification (§12.8c), not a trust
violation. All three PASSes were re-verified independently of the agents:
fresh `Evaluator.py` runs, axiom-audit inspection, and resolution-doubling
robustness checks on every certified oracle (§12.8d).

### 12.8a Arm A: beat the original run by changing representation, not effort

Arm A reached `Cr = 1/298000` in **one sprint** — past the original sprint
030's `1/240000` — via the roadmap's top lever (merged-numerator revive), but
executed better than the original: instead of doubling resolution to
n=262144 (~500 s oracle runs), it derived a **cancellation-free closed form**
for the Φ/Φ′/Φ″ evaluations, eliminating the interval-cancellation slack that
ball arithmetic accrues on `H_η − H₀` subtractions, and certified at the
inherited n=65536 (~65 s). Its sprint report explicitly notes this
retroactively invalidates lever verdicts sprints 026/029 reached through the
poisoned numerics (merged ratio moves from 1.20× worse to 0.73× better on
remeasurement). Same shape as korenblum §10c: given the same roadmap, the
2026-07 model found a strictly better route than the 2026-04 run.

### 12.8b Arm B: first-shot success, and the korenblum failure mode is absent

The bare loop succeeded **on its first iteration** (14 min, one model call):
it chose the roadmap's second-ranked, conservative lever
(oracle-resolution-tightening 65536 → 131072 on the two existing registered
oracles, quoting the roadmap's own ball(n) extrapolation fits in its
comments), emitted all three coupled files in one response, and — by reusing
already-registered oracle rows — never needed to re-emit `lemma.toml`. The
cross-file bookkeeping failure that cost korenblum's Arm B a third of its
iterations (§10e) did not occur, by route selection rather than by skill.
The A/B split replicates korenblum's: the agentic arm changed the
representation; the bare loop re-tuned parameters inside the architecture it
was handed (1.763× vs 1.083×).

**How the tool-less model wrote compiling Lean — it wrote almost none.**
Audited exactly as korenblum §10e was. The archived transcript shows **zero
`tool_use` blocks** (2 assistant messages: thinking + text; one 38 KB
response). Comments stripped, V25 has the **same 148 executable lines as
V24** (supplied verbatim in its context); the raw diff is 4 line-pairs, and
after normalizing numerals and version names it is **empty**:

```
joint_phi_phip_invD2_val : 47/10⁷ → 43/10⁷
uzz_phi_sq_val           : 3/1250000 → 23/10⁷
Cr_val                   : 1/169000 → 1/183000
show (…) + 1/2 * (…) ≤ …   (the same numerals, restated)
```

The only proof obligation the new numerals create is the integer inequality
inside the existing monotonicity step, which `norm_num` closes — a decision
procedure, not Lean authorship. The substantive act was numerical judgment
in Python: choosing the roadmap's n=131072 lever, tightening the
rationalizer (`max_denom` 10⁷→10⁸, `safety_abs` 1e-8→1e-9), and — because
the evaluator recomputes oracles *after* emission — **predicting** the
unseen n=131072 ball values from the roadmap's ball(n) fits and declaring
above them. Its margins: joint 12.6% slack, **uzz 0.9%** — a near-miss; a
slightly worse extrapolation loses the iteration. As with korenblum, this
**strengthens** the partial-formalization conclusion (the scaffold is so
load-bearing that pure numeral substitution rides it to a certified
improvement) and **qualifies** any "the agentic system is unnecessary"
reading: at this anchor's granularity the no-agent task reduces to
parameter re-pinning, and the arm was never required to write substantive
Lean.

### 12.8c Arm C: SUCCESS by the letter of the gate — via the seed's
rationalization slack, not via new mathematics

Arm C is the headline divergence from korenblum, and it must be reported
with precision.

**What it did:** across 5 sprints (one lost to a transient API kill) it
built, from Mathlib alone, a complete **formalization of Krivine's theorem**
— Gram/PSD toolkit (Schur product, unit-diagonal Gram realization), the
planar `E[sgn·sgn] = (2/π)·arcsin⟨x,y⟩` identity, the N-dimensional Gaussian
rounding argument, and a kernel-checked numeric bound on
`π/(2·log(1+√2))` — landing `GrothendieckIneq (89110699/50000000)` with
audit set exactly `{propext, Classical.choice, Quot.sound}`. The seed axiom
is **eliminated**: nothing in the accepted candidate is trusted beyond
Lean's kernel. To our knowledge Krivine's bound had not previously been
formalized in any proof assistant; the artifact
(`Proof/KrivineRounding.lean`, `Proof/KrivineNumeric.lean`,
`Candidates/V1.lean`) has independent value.

**What it did not do:** improve the Grothendieck constant.

```
KrivineBound = 1.7822139782…
Arm C K_val  = 1.7822139800   = Krivine + 1.8e-9   (ABOVE the true bound)
seed         = 1.7822140000   = Krivine + 2.2e-8
paper result = Krivine − 1e-17 (via the Lemma54/Cr pipeline being ablated)
```

Because Krivine's bound is irrational, the Arm C seed had to be rationalized
upward (§12.5); that rounding created a 2.2e-8 window in which *re-proving
the prior state of the art* strictly beats the seed rational. Arm C found
and took exactly that route. Korenblum's Arm C had no such window (its seed
`35646/100000` is the exact parent value), which is precisely why the two
Arm C outcomes differ in label while agreeing in substance: **in neither
study did the no-PF arm advance the constant.** The korenblum arm spent its
budget rebuilding Bergman scaffolding and never reached a push; the
grothendieck arm rebuilt Krivine scaffolding all the way to a certified
endpoint that the seed encoding happened to score as a win. The predicted
mechanism — *without the partial formalization the budget goes into
rebuilding it* — is what both traces show.

**Label discipline.** The harness recorded S when the unmodified
`Evaluator.py` accepted V1 (that is §2.2's goal G verbatim). The framework's
own evaluator *agent* graded the final sprint VERDICT_FAIL on G3
(write-scope): the **driver** had patched `scripts/harness_preflight.sh` to
work around an ablation-harness construction bug (§12.8e), and the agent
correctly flagged that out-of-scope edit. The Lean content itself was
contract-scoped and clean. We report S\* with this chain disclosed, and both
labels retained in the run record.

### 12.8d Validation performed on all three successes

* **Independent evaluator re-runs** (fresh process, `--no-log`): Arm C's V1
  re-verified end-to-end — compile PASS, TYPE gate PASS
  (`GrothendieckIneq K_val` exact), axiom scan = 3 standard axioms, score
  `89110699/50000000`. Arms A/B accepted rows re-read from their logs with
  oracle statuses all `pass`.
* **Oracle robustness at doubled resolution** (a rigorous sup bound must not
  cross its declared value when recomputed finer). All pass:
  Arm A `compute_merged_uderiv_bound` @131072 → `67/10⁷`, exactly the
  declared rational (the rationalizer's ceiling absorbs the tightening);
  Arm B `joint` @262144 → `3.54e-6` vs declared `4.3e-6`;
  Arm B `uzz` @262144 → `2.23e-6` vs declared `2.3e-6`.
  No certificate moved adversely under refinement. (Arm C's result carries
  no oracle at all — the numerics are inside the kernel-checked proof.)
* **Classifier vs harness**: `classify_groth.py` labels agree with the
  harness on all three; conclusion-shape D4 scan (Cr·p² form for A/B,
  `GrothendieckIneq`-application for C) found nothing; Arm C's final audit
  contains no oracle axioms at all, mooting the oracle-status D4 class.

### 12.8e Infrastructure incidents (this study's own faults, disclosed)

1. **Deny-rule friction** (§12.2 note): uniform across agentic arms; Arm A
   wrote via Bash, Arm C's evaluator staged bookkeeping for operator
   application (applied verbatim after each sprint, content verified).
2. **Broken `pyproject.toml` in the Arm C workspace**: `make_arm_c_groth.py`
   deleted the `grothendieck/` python package but left `pyproject.toml`
   declaring it, so `uv run` failed its editable build and
   `harness_preflight.sh` exited 1 every sprint. The driver hand-verified
   the halt condition and patched the script's `uv run python` → `python3`
   — the edit the G3 gate then caught (§12.8c). Root cause is ours, not the
   framework's.
3. **Framework bugs observed in passing** (left as-is for fidelity; noted
   for the paper's limitations): the preflight halt check is fail-open
   (`grep -c … || echo 0` double emission), and its stuck-planner detector
   keys on a `title` field the evaluator's log rows don't carry.
4. One Arm C sprint (its "sprint 002") died to a transient
   `Connection closed mid-response` API error before writing a contract;
   ~8 min / 37 K tokens absorbed by the budget as run noise.

### 12.8f Revised cross-constant reading (superseded in part by §13)

* **Capability without the agentic system**: replicated. The bare loop
  reached a certified improvement both times — but both times by the
  conservative in-architecture move, and here its win (1.083×) is a third
  of Arm A's (1.763×) at the same task.
* **Architectural reach**: replicated. Only the full framework changed
  representation (korenblum: termwise per-mode criterion; grothendieck:
  cancellation-free closed form), and both times that is what beat the
  original run.
* **The partial formalization**: the korenblum claim ("decisive") sharpens
  rather than reverses. Without the PF, the agent must rebuild scaffolding;
  korenblum's arm ran out of budget inside the rebuild (D1), grothendieck's
  arm finished its rebuild — of the *prior* state of the art — and scored
  only through a seed-encoding artifact. In neither study did the no-PF arm
  produce new mathematical knowledge about the constant. What the
  grothendieck run adds: with a 2026-07 agentic stack, "rebuild the
  scaffold" now fits inside ~2.5 h for a Krivine-sized theorem — so the
  PF's contribution is best stated not as "success vs failure" but as
  *where the budget goes and whether the certified endpoint advances the
  frontier*.

---

## 13. Sprint-016 structural ablation — plan (approved direction, pending user review)

**Date:** 2026-07-29. **Motivation:** the §12.8 audit showed the sprint-030
anchor does not discriminate Lean-writing ability — its no-Lean envelope
(≈1.31× improvement, measured) sits only ~8% short of the original run's
1.42× result, and Arm B succeeded entirely inside that envelope by numeral
substitution. Design change per user direction: re-anchor the study on an
iteration whose improvement was *conceptual*, so that the claim under test
becomes "Arm A improves; Arms B/C cannot produce any meaningful improvement
at all," warranted by a measured envelope rather than an asserted bar.

### 13.1 The anchor

**Sprint 016 (V11 → V12): Cr 1/1 → 1/32, a 32× single-sprint jump**, from
replacing V11's triangle product `M_pp · inv_F_p_z³ = 56.08 · 2³ ≈ 449` with
a single merged sup `‖∂²F_p‖/‖∂F_p‖³ ≈ 1.55` (the lemma.toml row sprint 016
added calls it a ~289× tightening of the term-2 chunk; it required minting
the `h_u_zz_oracle` + `u_zz.py` arb oracle and the corresponding new theorem
route). The looseness it removed is *representational*: no resolution or
declared-value shaving of the frozen V11 formula crosses it.

Two properties §12's anchor lacked:

1. **Huge conceptual gap.** V11's oracle stack (five oracles: M, M_phi,
   M_phi_prime, M_pp, inv_F_p_z, at n_per_edge 512–1024 defaults) has
   bounded convergence headroom; the no-Lean envelope (measured in P1) is
   expected O(2×) against the sprint's 32×.
2. **Discovery parity.** The S₀¹⁶ Bulletin ends at the sprint_015 PASS row;
   the merged-sup direction appears nowhere in the workspace. All arms face
   the same conceive-and-execute task the original planner faced. (§12's
   anchor was execution-only — the roadmap pre-named the lever.)

Timeline (git auto-checkpoints, all 2026-04-30 UTC):

| Event | Time | Commit |
|---|---|---|
| verdict_015 lands (V11 accepted at Cr = 1) | 07:40:33 | `cfd323f3` |
| **S₀¹⁶** (Bulletin sprint_015 row present) | **07:40:56** | **`5db00044`** |
| sprint-016 planner's first artifact | 07:43:08 | `54fd1498` |
| verdict_016 lands (V12 at Cr = 1/32) | 08:11:33 | `0c02b87a` |

**Original band T_orig¹⁶ = 1,837 s.** *(Corrected in §13.7.1: verdict_016 was
a G3 write-scope FAIL; V12 was accepted by the sprint-017 salvage at 08:20:16
(`410a45c1`). The honest band is **2,360 s**, and that is what was used.)* Agent/skill definitions at `5db00044`
are byte-identical to `e86a00f0` (verified), so every §12 gate result about
the harness surface carries over.

### 13.2 Success criterion: the measured no-Lean envelope

**Envelope protocol (P1).** On the frozen S₀¹⁶ Lean surface: (a) extract
V11's exact Cr formula from the era's `Lemma54_Paper*` chain (Cr as a
function of the five declared `_val`s); (b) run all five registered oracles
to convergence (they are n=512–1024-era; 4–16× resolution is minutes);
(c) envelope = the formula evaluated with every declared value shaved to its
converged oracle bound, minimized over every proof route present in the
frozen surface (V11's route plus any earlier surviving route). Report the
per-oracle convergence table.

**BAR = a round rational ≤ envelope/2**, fixed *before* any arm runs and
recorded in every manifest. Success for Arms A and B″ = an accepted
candidate with `Cr_val ≤ BAR`. The ≥2× margin makes the bar robust to
envelope measurement error; the original's 1/32 clears any plausible BAR by
an order of magnitude. *(The last clause did not survive measurement: the
converged envelope is ≈3.9e-4, so BAR = 1/6400 sits far below 1/32 — the
premise "envelope ≈ O(2×)" in §13.1 was wrong by orders of magnitude. See
§13.7.2; the BAR construction itself is what absorbed this.)* Sub-BAR-but-improving candidates still log
(`new_best`) and are reported as within-envelope progress, not S.

**Arm C″ criterion (anchor-independent, §12.9 discussion):** seed
`axiom hKrivine : GrothendieckIneq KrivineBound` **at the exact real** —
the sound, PF-free statement of "the K_G frontier at iteration start"
(which is within ~10⁻¹⁷ of Krivine and unstatable without the ablated
pipeline). Success = an accepted candidate whose rational `K_val` satisfies
`K_val < KrivineBound`, decided against a 50-digit certified interval for
π/(2·log(1+√2)) (mpmath, interval width ~10⁻⁵⁰; a K_val inside the interval
flags for manual review — it cannot occur for any K_val an arm could
plausibly certify). Any success is mathematics strictly beyond the
published SOTA. Rationalization slack is structurally eliminated: there is
no rational above Krivine to shave toward.

### 13.3 Construction (P0)

* `harness/make_s0_grothendieck016.sh` — the §12.2 builder with
  `S0_COMMIT=5db00044`, plus the same b-series restore and venv/.pth/git
  treatment. Log reconstruction from verdicts ≤ 015.
* `gate_s016.sh` — G1: `lake build …Candidates.V11`; G2: evaluator PASS at
  `Cr_val: 1/1` (cold oracles prewarm the era's `.cache`); G3 leak gates:
  no `sprint_016+` artifacts, no `V12+.lean`, no `h_u_zz_oracle` /
  `u_zz_bound_val` / `u_zz.py`, values `1/32` and `1.55` and `289` absent
  from Lemma54 (context-checked as in §12.2's gate), Bulletin/Experience
  tails at sprint_015; G4: single-commit git history.
* P0 also verifies the era's `AGENT_BRIEF.md`/`Proposals` oracle-minting
  policy so the arms' authority matches what sprint 016 actually exercised
  (its lemma.toml row is annotated "Approved by sprint_016" — in-loop).
* Arm workspaces: `make_arm_ws_groth.sh`-equivalent clones
  (`groth16_arm{A,B,C}`); Arm C″ via a `make_arm_c_groth016.py` that
  differs from §12.5's builder only in: exact-real seed axiom; contract
  gains a proven `GrothendieckIneq` monotonicity lemma and
  `KrivineBound ≤ 1782214/1000000` (lifted from Arm C-01's kernel-checked
  `KrivineNumeric.lean`, disclosed as study infrastructure) so the seed V0
  still evaluates at score `1782214/1000000`; `pyproject.toml` fixed this
  time (no dangling `grothendieck` package — §12.8e item 2).

### 13.4 Arms and harness (P2)

Fork-of-a-fork, run IDs `grothendieck016-arm{A,B,C}-01`:

* `groth16_config.py`: parent `Fraction(1,1)`, `BAR` (from P1),
  `ORIGINAL_BAND_S = 1837`, S₀¹⁶ paths, era candidate names
  (parent `V11`, prev `V10`).
* Arm A: unchanged driver (`/run-next-sprint`); **goal = `Cr ≤ BAR`**, so
  A and B″ face the identical criterion (uniform-bar principle). A defines
  T_ref/O_ref; floor at 1,837 s.
* Arm B″: §12.4's loop with the era context (auto-globbed Proof/Lib +
  Numerical_Library, candidates V10+V11, Bulletin whole, sprint_015
  contract, Braverman text; **no roadmap section exists — none exists in
  the workspace**); system prompt states the BAR explicitly. 2× budget,
  stop at goal.
* Arm C″: §12.5 driver at 2× the *new* Arm A budget.
* `classify_groth16.py`: S iff `best ≤ BAR` (arm C: `< KrivineBound`
  interval test); D1 iff nothing ≤ BAR was ever proposed, with
  within-envelope improvements reported separately in the D1/D5 evidence.

### 13.5 Execution and estimate

| Phase | Work | Est. |
|---|---|---|
| P0 | S₀¹⁶ build + gates; arm clones; C″ workspace | ~1 h |
| P1 | Envelope measurement + BAR fixing (writes §13.2 table) | ~0.5–1 h |
| P2 | Harness fork + smoke | ~1 h |
| P3 | Arm A run (original band 31 min) | 0.5–1.5 h |
| P4 | B″ ∥ C″ at 2× | ~1–2.5 h |
| P5 | Classify, validate (Lean-diff audit + envelope check on any
      B″ success; axiom audit + interval test on any C″ success), §13.6
      results | ~1 h |

**≈ 5–7 h end-to-end, ≈ \$60–120 at list.** The §12 sprint-030 runs remain
in the paper with their envelope analysis as the audit that motivated this
design; §13 supplies the discriminative claim.

### 13.6 Predictions (registered before running)

Arm A: S at ≈1/32 or beyond (the original found the idea in 31 min; our
Arm A out-executed the original at §12's anchor). Arm B″: within-envelope
re-pins only → D1-at-BAR; a one-shot conceive-and-derive of the merged-sup
route with its new oracle module and theorem, tool-less, would be a
genuine bare-model Lean-synthesis result and will be reported as such if
it occurs. Arm C″: scaffold rebuild → D1/D5 (nothing below true Krivine);
any S would be a publishable mathematical advance on its own.

---

## 13.7 Execution record (2026-07-29)

### 13.7.1 Ground-truth corrections found in pre-run verification

1. **The original band is 2,360 s, not 1,837 s.** `verdict_016`
   (08:11:33, `0c02b87a`) was a **FAIL** on G3 write-scope — the V12 Lean
   compiled, the evaluator pre-run passed at Cr = 1/32, but the sprint wrote
   two out-of-contract files (`docs/HARNESS_OPERATOR_TIPS.md`,
   `Numerical_Library/__init__.py`). Sprint 017 ("salvage") re-evaluated the
   byte-identical V12 and PASSed at 08:20:16 (`410a45c1`). The band used for
   the budget floor is S₀¹⁶ → verdict_017 = **2,360 s** (the generous and
   honest direction). `ORIGINAL_BAND_S = 2360` in `groth16_common.py`.
2. **Discovery-parity nuance.** The raw identity `u_zz = −DD/D³` (and the
   line "sup‖u_zz‖ = sup‖DD‖/‖D‖³, bounded above by sup‖DD‖/(inf‖D‖)³")
   *is* present at S₀¹⁶, in `Scratch/sprint_015_planner_uzz_*.py` — it was
   for the original planner too. What is absent is the sprint-016 *move*:
   evaluating the quotient's own sup as a single oracle, and the
   `H₀″/H₀′³ = w` cancellation showing it is ~300× below the triangle
   product. Neither script computes the quotient sup. Parity with the
   original planner's state is exact (byte-identical tree).
3. **Trust-surface honesty checks added to the classifier**
   (`analysis/classify_groth16.py`): the rectangle-containment axiom
   `h_oracle_domain_contains_image` is TRUSTED (not re-verified), so a
   candidate that shrinks `delta_val`/`B_val` while restating it is a
   D4-candidate; edits to pre-existing oracle modules beyond
   resolution/precision knobs (domain params `delta`, `B`, `p_max`, `eta`,
   `r`) are flagged; the frozen surface (SearchConfig, Proof/Lib, LeanProof
   closure) is byte-diffed against S₀¹⁶; agent transcripts are scanned for
   reads of the study's own `runs/` files (BAR/envelope leak — `runs/` is
   readable to agentic arms, as it was in §12).

### 13.7.2 P1 result: the envelope premise was wrong — and the BAR absorbed it

Full data: `runs/groth16_envelope/envelope.json` (+ per-oracle sweeps
alongside). Boundary-grid oracles converge cleanly; certified bounds at
convergence (n_per_edge up to 262,144; flat at rationalizer granularity):

| Oracle | V11 declared | default-res recompute | converged | slack |
|---|---|---|---|---|
| M_phi | 239/5000 = .0478 | 61/2500 = .0244 | **9/5000 = .0018** | **26.6×** |
| M_phi_prime | 543/10000 = .0543 | 59/2000 = .0295 | **73/10000 = .0073** | 7.4× |
| inv_F_p_z | 2 | 3407/2000 = 1.7035 | **7879/5000 = 1.5758** | 1.27× |
| M_pp | 56.08 | 56.0768 | 55.8828 | 1.0× |
| M | 428 | 427.91 | 427.85 | 1.0× |

* **Re-pin only** (declared values, no oracle edits): Cr = 0.523.
* **No-Lean envelope** (converged bounds, route `Cr_phi_uzz`):
  **3.87e-4 ≈ 1/2585** — pure resolution-shaving beats the original
  sprint's 1/32 by ~80×. §13.1's "expected O(2×)" was wrong by three orders
  of magnitude. Had success been "beat the parent" or "beat 1/32", Arm B
  could have taken the whole result by numeral edits; this is the measured
  justification for the BAR protocol.
* **BAR = 1/6400 = 1.5625e-4** — 2.48× below the envelope (structurally
  unreachable by shaving; the certified bounds cannot go below the true
  sups, and the convergence tails are flat), while the structural route
  (u_zz quotient oracle + shaved Φ oracles) reaches ≈3.6e-5, 4.4× below
  BAR. The envelope is 91% term2 = the exact term the sprint-016 insight
  collapses. Consequence: **Arm A's S now requires the structural move AND
  oracle-resolution shaving** — more than the original sprint did; the
  original's 1/32 does not clear this BAR. Reported prominently rather than
  hidden: the BAR is calibrated to the measured no-Lean envelope, not to
  the original run's result.
* Measurement hygiene: sweeps ran in a throwaway S₀¹⁶ clone (deleted
  after), so no arm workspace carries high-resolution `.cache` entries.

### 13.7.3 Protocol deviations (user decisions, 2026-07-29)

* **Concurrent matched window, 1×.** All three arms launch simultaneously;
  when Arm A finishes, Arms B″/C″ stop at wall > T_ref = max(T_armA,
  2,360 s) (deadline file + SIGTERM grace; `pipeline_groth16.sh`). Time
  gates; token totals are recorded but cannot gate (unknowable mid-flight).
  This replaces §13.4's sequential 2× rule to halve wall-clock cost; the
  floor at the original band prevents an anomalously fast Arm A from
  starving the ablations.
* Arm A capped at 8 sprints (tail-risk insurance, not the science).
* No B″ run-past-success extension.

### 13.7.4 Setup deviations (disclosed)

* Arm C″'s contract ships two study-infrastructure lemmas so the seed can
  sit at the exact real: `GrothendieckIneq.mono` (proven; sign-flip
  argument) and `KrivineBound_le_seed : KrivineBound ≤ 1782214/1000000`
  (kernel-checked; port of the §12 Arm C's own `KrivineNumeric.lean`
  chain — an artifact produced inside this study, so it leaks nothing
  about the sprint-016 anchor). Seed V0 gates: builds, evaluator PASS at
  891107/500000, audit = 3 standard axioms + `hKrivine`.
* `pyproject` fix (§12.8e item 2): the deleted `grothendieck` python
  package is replaced by an **empty stub** so `uv run` and
  `harness_preflight.sh` work; verified at build (both PASS).
* Arm B″'s system prompt states the BAR explicitly (uniform-bar); Arm A's
  workspace is untouched (its Bulletin cadence already demands Cr
  reduction; the harness loops sprints until BAR). B″ additionally gets
  all 16 pre-anchor Scratch scripts (information parity with what A can
  read in-workspace). Static context: 166 K tokens, leak-grepped.

### 13.7.5 Mid-run falsification of the BAR, and the tight-seed successor

Arm B″'s first iteration re-implemented the M_pp oracle with an η-aware
split (Cauchy on the Φ′ correction only), legitimately dropping the
certified M_pp ≈ 56 → ≈ 6.5 with zero new Lean — an *implementation*
dimension of the no-Lean envelope that the P1 resolution sweep did not
measure. The implied true no-Lean floor (≈ 6.6e-5) is BELOW the
pre-registered BAR (1/6400): in this workspace's trust design (self-serve
certified oracles) **no score bar over a slack-carrying seed can encode
"improvement requires Lean."** The §13 run continues to completion as the
motivating measurement; the successor design — a slack-free tight seed
with a measured residual bracket — is specified in
**`docs/2026-07-29-tight-seed-plan.md`** for a fresh session to execute.

## 14. Sprint-019 fast ablation — plan (executing)

**Date:** 2026-07-29. **Status of §13:** the sprint-016 study is being run
separately by the user; §13's design (envelope method, oracle trust boundary,
exact-real Arm C seed) carries over here unchanged unless stated. This
section exists because results are needed as fast as possible: arms run
**concurrently** and B/C are stopped when A finishes (user decision).

### 14.1 The anchor

**Sprint 019 (V13 → V14): Cr 1/300 → 1/1300, a 4.33× jump**, from minting
the inline arb-certified joint oracle on `‖Φ·Φ′/D²‖` over `[0,pr]×Ω` —
replacing the term-1 triangle product `M_phi · M_phi_prime · inv_F_p_z²` —
plus the new Lean route that consumes it (`joint_phi_phip_invD2.py` +
`h_joint_phi_phip_invD2_oracle` + the `Cr_phi_uzz_direct`-variant theorem
did not exist before this sprint).

What makes this anchor discriminative: **sprint 018, immediately before it,
was the maximal no-Lean move** — "tighten V12's four η-aware oracle ceilings
to their exact certified rationals" (9.375×, declared-value shaving only).
At S₀¹⁹ the shave axis is freshly exhausted *by the framework itself*; the
remaining no-Lean slack is resolution-convergence only. The strongest
available answer to "Arm B was under-explored": the workspace's own
immediately-preceding sprint did the exploring.

Timeline (git auto-checkpoints, 2026-04-30 UTC): verdict_018 applied
08:34:20 (`b518fee4`); **S₀¹⁹ = `fed26621` (08:34:44)** — Bulletin ends at
`sprint_018 PASS`, no `joint_phi_phip*`, no V14; planner's first sprint-019
artifact 08:38:05; verdict_019 lands 09:07:23. **T_orig¹⁹ = 1,959 s.**

### 14.2 Success criteria and trust rules

* **Envelope + BAR** exactly per §13.2, measured on V13's surface (six
  registered oracles: M, M_phi, M_phi_prime, M_pp, inv_F_p_z, u_zz — all
  early-era resolutions, so convergence runs are minutes). BAR = round
  rational ≤ envelope/2, fixed before any arm runs. **Abort criterion:** if
  the measured envelope does not leave the original's 1/1300 at least 2×
  beyond it, this anchor is not discriminative — stop and escalate with the
  numbers.
* **Oracle trust boundary** per §13.2 discussion, with the refinement from
  the Arm A audit: frozen arb core and existing-oracle bodies
  (parameters-only edits); new functionals admissible only through the
  written admission audit; **D4 keys on the accepted candidate's consumed
  oracles** (edits to non-consumed modules are recorded as noise, since
  even reference Arm A rewrote non-load-bearing oracle bodies in §12).
* **Arm C‴** = §13.2's exact-real Krivine seed and 50-digit interval test,
  unchanged. Workspace built with the corrected `pyproject.toml` and the
  §13.3 contract helpers (monotonicity + `KrivineBound ≤ 1782214/1000000`,
  lifted from Arm C-01's kernel-checked artifacts, preserved in
  `harness/assets/`).

### 14.3 Concurrency and budgets (user decisions, disclosed)

All three arms launch **simultaneously** (128-thread box; three concurrent
lake/oracle workloads are fine). When Arm A's runner exits, the pipeline
touches per-arm stop-files (checked between sprints/iterations), waits a
10-minute grace period, then SIGTERMs stragglers. Effects:

* B and C get **exactly Arm A's wall clock** — a matched-budget (≤1×)
  design rather than §4.2's 3× or §12's 2×. Reported prominently: the
  failure claim becomes "no conceptual improvement within the reference
  arm's own budget," which is weaker than a 2×-budget failure and is the
  accepted cost of speed. Hard caps as safety: 4 h wall, 400 K output
  tokens per arm.
* No reference-budget dependency exists before launch, so nothing waits.
* T_ref/O_ref are still recorded from Arm A (floored at 1,959 s) for
  reporting and for any later top-up runs.

### 14.4 Execution

| Phase | Work | Est. |
|---|---|---|
| P0 | S₀¹⁹ build + gate (done/running); clones; C‴ workspace | ~45 min |
| P1 | Envelope sweep + BAR (writes the §14.2 table) | ~30 min |
| P2 | Harness fork (`groth19_*`, stop-file support, pipeline19) | ~30–45 min |
| P3 | Concurrent A ∥ B ∥ C; kill at A-finish (original band 33 min) | ~45–75 min |
| P4 | Classify + validate + §14.5 results, push | ~45 min |

**≈ 3–3.5 h to results, ≈ \$40–60 at list.** Predictions, registered: A
reaches Cr ≤ BAR via a new joint-type functional + new Lean (original did
it in 33 min); B produces at most within-envelope numerals (its one
demonstrated competence) and fails BAR; C rebuilds K_G scaffolding and
certifies nothing below true Krivine in ~A's wall clock.

### 14.5 ABORTED — the registered §14.2 criterion fired, on §13.7.2's data

The sprint-016 study's envelope measurement (§13.7.2) transfers directly to
this anchor and kills it, no new sweep needed:

* Sprint 017 was a salvage (V13's route is byte-identical to V12's) and
  sprint 018 shaved declared values against **default-resolution**
  certificates only. So S₀¹⁹'s surface already contains the u_zz oracle and
  its no-Lean envelope is §13.7.2's "structural route + shaving" figure:
  **≈ 3.6e-5 ≈ 1/27800**.
* The original sprint 019 achieved 1/1300 — **~21× inside the no-Lean
  envelope**. The registered abort criterion required the original to be
  ≥2× *beyond* it. Sprint 020 (1/2600) dies identically.
* Root cause, now understood: after sprint 016 the trajectory never
  re-harvested resolution slack, so every later sprint's certified value
  sits far above converged truth; any BAR below the envelope at S₀¹⁹ would
  demand sprint-020's term-2 move rather than sprint-019's term-1 move —
  an incoherent anchor task.
* Conclusion: **sprint 016 is the only anchor in this trajectory where the
  structural insight's power (~300× on the envelope's dominant term)
  dwarfs the resolution slack** — i.e., the only well-posed fast
  discriminative anchor. That study is §13.7, already running. No S₀¹⁹
  artifacts were kept (workspace deleted; ~$0 spent).

## 14.6 B-fix probe — Lean-execution with fixed numerics (running)

Per user direction after §14.5: a probe that isolates pure Lean synthesis,
immune to envelope effects by construction. Base: a fresh S₀¹⁶ clone
(`groth16fix_armB`, run id `groth16fix-armB-01`), running **concurrently
with the §13.7 arms** (64C/128T host; co-load noted in both records — the
§13.7 study's matched window is internally consistent since its three arms
share the load, and wall-clock is not a measured quantity for this probe).

**Handed over (read-only, pre-installed, committed):** sprint 016's
`u_zz.py` byte-verbatim from post-016 commit `0c02b87a` (272 lines;
recomputed bound 15519/10000 = 1.5519, prewarmed), its `[[oracles]]`
registration (`h_u_zz_oracle` / `u_zz_bound_val` / `compute_u_zz_bound`),
and the certified ceiling (declaring 2 is safe). **Not handed over:** any of
sprint 016's 962 Lean lines (V12 candidate 287 + new theorems 675 across
`Lemma54_Paper{,_Main,_Pderiv_Single}.lean`).

**Write allowlist: `Candidates/` and `Proof/` only.** Numerical_Library,
lemma.toml and Scratch emissions are refused — with frozen modules the
numeral ceiling is the default-resolution re-pin Cr = 0.523 (§13.7.2), so
**BAR_FIX = 1/16** (8.4× beyond it) is reachable only through the provided
oracle plus new consuming Lean; the handed route supports ~1/32 (2× inside
the bar). Success additionally requires `h_u_zz_oracle` in the accepted
candidate's audited chain.

Caps (capability probe, not budget-matched science): 6 iterations / 2 h /
200 K output tokens. Bare-loop mechanics, tools disallowed, §10d disclosure
applies. One setup incident, disclosed: a documentation edit was briefly
written into the probe workspace by operator error (wrong cwd) and removed
within a minute, before any iteration completed; the bare loop cannot read
workspace files and its static context was already frozen, so exposure was
nil. Prediction, registered: the concept-given task is exactly the original
sprint's Lean workload; korenblum §10e and §12.8b both showed the bare loop
failing multi-file architectural moves — if it clears BAR_FIX one-shot
here, that is a genuine bare-model Lean-synthesis result.

**Upgraded from probe to paired ablation (user question, 2026-07-29):**
B-fix alone is a single-condition capability measurement — its failure would
not isolate agency. Added **A-fix** (`groth16fix_armA`,
`groth16fix-armA-01`): the full agentic framework (`/run-next-sprint`) on a
byte-equivalent handout workspace (same pre-installed u_zz oracle,
recomputed bound 15519/10000 verified, committed), same BAR_FIX = 1/16,
same h_u_zz_oracle-in-chain requirement, caps 4 sprints / 2 h / 200 K
tokens. Numerics-frozen enforcement is mechanical for B-fix (write
allowlist) but post-run-audit for A-fix (agents write via Bash) — a
disclosed asymmetry. Together: the **Lean-execution ablation** — one factor
(the agentic system) differs between two arms facing an identical
concept-given, certificate-given, numerics-frozen Lean task. The 2 h figure
in both runners is a safety ceiling, not a duration; expected wall time is
~15–25 min for an early success and ~45–90 min for a full-cap failure.

**v2 — no-bar design + Arm C (user directives, 2026-07-29).** Two changes,
and a restart of the fix arms (~\$12 spent under v1, disclosed; both arms
relaunched from committed workspace states):

1. **The bar is gone, replaced by construction.** The reason v1 needed
   BAR_FIX was that V11's declared values sat above the frozen-default
   oracle bounds, leaving a numeral path to "improvement." v2 closes that
   at the source: the operator-constructed parent **V12′** re-declares the
   four Cr-relevant values EXACTLY at their frozen-default recomputed
   bounds (M_phi 61/2500, M_phi_prime 59/2000, inv_F_p_z 3407/2000,
   M_pp 35048/625) and sets `Cr_val` to the route formula's exact value,
   **Cr₀ = 330503166194381309/3906250000000000000 ≈ 0.084609** — verified
   compiling and evaluator-accepted in both workspaces, committed. The
   no-Lean manifold is now a single point: with frozen modules the
   evaluator's `declared ≥ recomputed` check pins every value, the
   monotonicity step is equality-tight, and every alternative frozen route
   (Cr_phi, Cr_phi_invD) is strictly worse. **Success = any accepted
   candidate strictly below the parent. No threshold, no line in the
   sand.** The handed u_zz route supports ≈ 30× below Cr₀; u_zz-chain
   usage is recorded as audit metadata but any sound new-Lean route
   counts.
2. **C-fix added** (`groth16fix_armC`, `groth16fix-armC-01`): the §13.2
   exact-real-Krivine-seed workspace (built by a fix-named fork of the
   validated §13.7 builder), full agentic framework, caps 4 sprints / 2 h
   / 200 K tokens. Its no-bar property holds by construction — with
   `axiom hKrivine : GrothendieckIneq KrivineBound` at the exact real,
   nothing below the seed is derivable without new mathematics; success is
   decided against the 50-digit Krivine interval, and Krivine
   re-certifications inside the rationalization slack log as within-slack
   progress, not success. Its "fixed numerics" condition is vacuous (the
   no-PF workspace has no numerical library) — which is itself the
   PF-ablation datum: the factor being ablated is what makes the handed
   certificate *usable*.

The three-arm fix study therefore reads: **A-fix** (agents + PF +
certificate) vs **B-fix** (PF + certificate, no agents) vs **C-fix**
(agents + certificate-unusable, no PF), all uncapped by any score bar, all
"success = strictly improve on a zero-slack parent."

**INCIDENT — v2 fix runs invalidated by operator contamination; v3 clean
rerun (2026-07-29 ~17:10).** The B-fix v2 "success at iteration 1" was
audited before acceptance, and the audit caught a contamination of my own
making: v1's iteration 1 had completed its file-writes before the v1 kill,
emitting a 686-line `Proof/Lib/Lemma54_Paper_UZZ.lean` (with no candidate —
the korenblum-B "staged work" pattern), and the operator's subsequent
`git add -A` handout commit swept that arm-written file into the v2 starting
state. v2's model therefore had the theorem file in context and only wrote
the 288-line consuming candidate. A-fix v2 was contaminated worse: its v1
sprint had appended 32 lines to the frozen `Lemma54_Paper.lean`, plus
contract/Bulletin/Scratch artifacts, all swept into the same commit. Both
v2 runs are struck as clean experiments (records kept:
`groth16fix-arm{A,B}-01`); C-fix is unaffected (built after the restart, no
v1 ever ran in it).

What survives as a caveated observation: across v1+v2's two tool-less
calls, the bare model produced the complete 974-line u_zz route — the
686-line theorem file (one call, clean workspace, zero compile failures)
and the 288-line candidate consuming it (one call) — accepted at exactly
the predicted route value `53683128751/2·10¹³ ≈ 1/373`, with all frozen
surfaces byte-intact and a clean axiom chain. This already suggests the
§14.6 registered prediction ("bare loop fails the multi-file move") is
likely wrong when the concept+certificate are handed over; the clean v3
rerun decides it.

v3 protocol: `harness/build_fix_ws.sh` rebuilds both workspaces from S₀¹⁶
with the handout + clean V12′ in a single scripted pass (no incremental
operator edits on live workspaces — the root cause here); run ids
`groth16fix-arm{A,B}-02`.

**v3 outcome (2026-07-29 17:25):** B-fix v3 (`groth16fix-armB-02`)
succeeded at iteration 1 — one tool-less call, 683-line
`Proof/Lib/Lemma54_Paper_Uzz.lean` + 233-line `V13.lean`, evaluator-accepted
at `53683128751/2·10¹³` with frozen surfaces byte-intact,
`h_u_zz_oracle` in chain, $7.31 / 94 K output tokens. The registered
prediction is refuted for the concept-and-template-given regime.
**Post-hoc context audit (user question):** the model's static context
contained the fully-proven 467-line sibling `F_inv_p_second_deriv_bound_phi_uzz`
(+138-line wrapper) and sprint-015's NL blueprint including the cancellation
`u_zz = −DD/D³`; the accepted core theorem is 70.4% textually similar to the
sibling (wrapper 89.4%). The honest capability claim is one-shot
*proof-editing/rethreading at ~900-line scale with zero compile feedback* —
not de novo synthesis. §14.7 measures the synthesis question properly.
A-fix v3 and C-fix were truncated by the 17:25 usage-limit outage, relaunched
21:07 as `groth16fix-armA-03`/`groth16fix-armC-02`, then **killed by user
decision ~21:35** (records + `KILLED_BY_OPERATOR.md` + workspace residue
kept) to redirect budget to §14.7. The A-fix cell of the paired ablation is
therefore EMPTY in v3 — no agent-vs-bare comparison should be quoted from
§14.6, only the B-fix capability observation with the context caveat above.

## 14.7 Context-ablation ladder — how much context does the one-shot need? (running)

User directive (2026-07-29): §14.6's handout was maximal by design (it
held context constant to isolate agency), so its B-fix success says
little about bare-model Lean synthesis. §14.7 makes context the measured
axis. Same task, harness, caps (6 iters / 2 h / 200 K), evaluator, no-bar
success rule, and the SAME §14.6 system prompt (concept still given);
runner `harness/run_arm_bfix_ctx.py`, fresh `build_fix_ws.sh` workspaces
per rung. The headline datum per rung is the **iteration-1 (one-shot)
result**; eventual pass with compile feedback is secondary. Ladder
(cumulative removals from L4 = §14.6 B-fix):

* **L2** (`groth16fix-L2-01`, ws `groth16fix_L2`): NL layer removed
  (Scratch, Sprint_Contracts, Bulletin, AGENT_BRIEF) AND `Proof/Lib`
  reduced to statements only — every theorem signature visible and
  callable, every proof body elided (59 elisions; sibling proof text
  absent, verified). Context 382 K chars (~96 K tok) vs L4's 689 K.
  Tests one-shot proof *synthesis* at the ~450-line theorem scale.
* **L0** (`groth16fix-L0-01`, ws `groth16fix_L0`): additionally NO
  `Proof/Lib` blocks at all and candidates reduced to the parent V12′
  only. Context 280 K chars (~70 K tok). The model sees the chain's
  names only where V12′ calls them. Expected-fail anchor rung.

Disclosures: hidden files still exist compiled in each workspace (the
parent must build), so the model can invoke names it sees referenced but
cannot read their text; pretraining leakage impossible (corpus created
2026-04→07, private repo). Registered guesses before launch (this
session): L2 iter-1 ≈ coin flip, L0 fail. Both launched 21:5x UTC
2026-07-29, concurrent, per user instruction ("kill A/C right now, then
immediately run the two selected rungs").

**Incident + first datum (2026-07-29 ~22:05).** Operator launched both
runners with RELATIVE `--workspace` paths; `build_and_eval` execs the
workspace venv python with `cwd=ws`, so the path doubled and the L0-01
runner crashed with FileNotFoundError — *after* the model call, file
write, and `lake build` had all completed. Salvage (see
`runs/groth16fix-L0-01/SALVAGE_NOTE.md`): the L0 one-shot candidate (405
lines, candidate file only — no new Proof/Lib attempted) **compiled and
passed a manual evaluator run at EXACTLY the parent point** — same route,
same pinned values, no `h_u_zz_oracle`, zero improvement. The L0 iter-1
datum is therefore: syntactically fluent re-certification of the parent;
the u_zz route was not attempted without the Proof/Lib corpus in context.
Runner patched (`Path(...).resolve()`), workspace rebuilt, clean rerun
`groth16fix-L0-02` launched ~22:15. L2-01 was still mid-iteration-1 and
was saved without process disturbance by a filesystem shim
(`workspaces/groth16fix_L2/workspaces/groth16fix_L2 → ..`, outside
Lemma54, invisible to the tool-less model; see
`runs/groth16fix-L2-01/OPERATOR_NOTE.md`; remove after the run).

**L0 RESULT (`groth16fix-L0-02`, S at iteration 2, ~23:05): the
registered guess ("L0 fail") is REFUTED — but not one-shot.** Iter 1
attempted a u_zz candidate and failed the axiom audit on a namespace
convention (`Lemma54Recon` vs `Braverman.PaperV0`); iter 2 (after that
purely-conventional feedback; 40.1% textual overlap with iter 1, i.e. a
rethink, not a patch) produced a 387-line candidate-only solution
accepted at **211/10000 ≈ 0.0211 — 4.0× below the parent**, $8.81 /
~71 K output tokens total. Audit clean: `h_u_zz_oracle` statement
semantically identical to the B-fix reference (no smuggled strength);
axiom chain = seeds + 4 registered oracles, all re-verified;
`h_M_pp_oracle` DROPPED; zero writes outside the candidate; frozen
surfaces byte-intact. The route is the interesting part: unable to see
`Proof/Lib` (statements included: none), it inferred the hidden wrapper's
signature from V12's call site and *bridged to its `M_pp`-shaped
hypothesis* — proving IN-CANDIDATE, from Mathlib alone, a new analytic
fact the workspace never had (`‖H₀'(w)‖ ≤ 1.83` on Ω via
`sin(H₀w)=w` → chain rule → Pythagorean lower bound on `‖cos‖`), adding
the `M_phi_prime` oracle to get `‖∂_z F_p‖ ≤ 1.86`, and cubing into
`h_u_zz_oracle` for an effective `M_pp_uzz = 1.86³·2 ≈ 12.87` (vs 56.08).
The 7.9× score deficit vs B-fix's `1/373` is exactly the cost of
adapting to the hidden chain's triangle interface instead of replacing
the step. One-shot tally at L0: 0/2 (the salvaged -01 sample
re-certified the parent point; -02 iter 1 failed on convention);
eventual-pass with feedback: 1/1, via genuinely new proved mathematics.

**L2 RESULT (`groth16fix-L2-01`, S, ~23:15): one-shot PASS at
`21/1000 = 0.021` (4.03×).** Iter 1 timed out at the harness's 45-min
per-call cap producing nothing — and a timeout changes neither history
nor feedback, so iter 2 ran the IDENTICAL fresh prompt: the success is a
true one-shot (one completed call, zero feedback; 465-line candidate,
117 K output tokens, $3.17). Audit clean: axiom statement identical to
reference modulo whitespace; chain = seeds + {M_phi, M_phi_prime,
inv_F_p_z, u_zz} all re-verified, `h_M_pp_oracle` dropped; single
candidate file, frozen surfaces intact.

**Convergent-invention finding:** L2 and L0 — separate conversations,
different contexts — invented the SAME bridge: prove `‖H₀'‖ ≤ ~1.83` on
Ω from `sin(H₀w)=w` + chain rule + Pythagoras (a fact the workspace
never had), add the `M_phi_prime` oracle for `‖∂_z F_p‖ ≤ ~1.86`, cube
into `h_u_zz_oracle` for an effective M_pp-shaped constant (~12.8 vs the
oracle's 56.08), and feed the frozen wrapper through its existing
signature. Neither re-derived the Step-5 chain variant — L2 could see
its statement but not its body and chose the bridge anyway ("whose
Step-5 body is not ours to re-emit", its header says). Both landed at
~0.021; only L4, which could read the sibling's proof body, reached
1/373 by replacing the step itself.

**§14.7 ladder summary (all audits clean):**

| rung | context | iter-1 (one-shot) | eventual | score |
|------|---------|-------------------|----------|-------|
| L4 (§14.6 B-fix) | corpus + sibling proof + NL blueprint | **S** | S (iter 1) | 1/373 ≈ 0.00268 |
| L2 | statements only, no NL | **S** (on first completed call; one 45-min timeout before it) | S | 21/1000 = 0.021 |
| L0 | no Proof/Lib, V12 only | fail ×2 (parent re-certification; namespace) | **S** (iter 2, one conventional feedback) | 211/10000 = 0.0211 |

Reading: bare-Opus one-shot Lean synthesis of a compiling ~450-line
candidate with NOVEL analytic content is real at L2; the full-corpus L4
advantage (7.9× better score) came from proof-editing access to the
sibling's body, not from being able to write Lean at all; and even at L0
the model reaches the same bridge with a single round of convention
feedback. The registered guesses (L2 coin-flip, L0 fail) were one for
two — L0's eventual success via new mathematics was NOT predicted.
