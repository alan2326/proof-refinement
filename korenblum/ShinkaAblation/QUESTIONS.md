# Open Questions for the Korenblum × ShinkaEvolve Ablation

Things I built around assumptions I am not 100% confident in. Please confirm
or redirect.

---

## 1. Folder location

I placed the ablation at `korenblum/ShinkaAblation/`, sibling to
`ProofRefinement/`. I considered:

- `korenblum/ShinkaAblation/` ← current choice. Lives next to the
  agent search, but kept fully separate from `ProofRefinement/` so neither
  contaminates the other.
- `grothendieck/experiments/korenblum_shinkaevolve/` — keeps it
  next to the existing ShinkaEvolve install, but mixes Lean projects.

I went with the first because the Lean project root (`korenblum/`)
has to be reachable by `lake build`, and we need to drop generated candidates
into `ProofRefinement/Korenblum/Candidates/` to evaluate them. Sibling layout
is the simplest.

**Confirm or redirect.**

---

## 2. ShinkaEvolve does not support Lean as a language

`shinka.core.runner.EvolutionRunner` hard-codes the supported `language` values
to `python | cpp | cuda | rust`. The same is true in `shinka.edit.apply_diff`,
`shinka.edit.apply_full`, and `shinka.database.complexity`.

I solved this with a **runtime monkey-patch** (`shinka_lean_patch.py`) that:

1. Adds `language="lean"` to all gates (extension `.lean`, comment char `--`).
2. Adds `claude-opus-4-7` to the pricing table and to the
   `REASONING_CLAUDE_MODELS` list.

Alternatives I considered:

- Forking ShinkaEvolve. Heavier; the patch would have to be re-applied on
  every upstream bump.
- Pretending the candidate is `cpp`. Doesn't work — Lean rejects `//` and
  Shinka inserts `// EVOLVE-BLOCK-START` markers into the seed.

**Is the monkey-patch acceptable, or do you want a fork?** If a fork, where
should it live?

---

## 3. "Latest opus model" — exact model ID

You said use the latest Opus. I used `claude-opus-4-7`, which my session
metadata says is the latest. ShinkaEvolve's pricing table currently only knows
about `claude-opus-4-6`, so the patch in (2) registers `4-7` at the same price
point as `4-6` (input $15/Mtok, output $75/Mtok).

**Confirm**: `claude-opus-4-7` is the right ID, and the per-Mtok price is
acceptable to copy from `4-6`.

---

## 4. Trust surface — same evaluator, same `lemma.toml`

The ablation does not duplicate the trust surface. `evaluate.py` shells out to
the existing `korenblum/ProofRefinement/Korenblum/Evaluator.py`
on the candidate file in-place. That means:

- compile gate, type gate, axiom gate, oracle gate, and score extraction all
  match the agent harness byte-for-byte,
- `lemma.toml` import policies are enforced exactly as in the agent run,
- the sink theorem is `korenblum_constant_search`, the score is `c_value`,
  larger is better.

The candidate is staged into
`korenblum/ProofRefinement/Korenblum/Candidates/Shinka_<gen>.lean`
before `Evaluator.py` runs, then deleted afterward (only the metrics persist).

**Confirm**: re-using `Evaluator.py` directly is what you mean by "same trust
surface and shape of output". If you want a frozen copy of the evaluator
inside `ShinkaAblation/`, say so.

---

## 5. Information-leak boundary [partially resolved 2026-05-07]

User confirmed: include `Proof/Reduction.lean`, `Proof/Integrability.lean`,
`Proof/Summability.lean`, and `Numerical_Library/*.py` in the trust surface
(Option A). Numerical_Library Python source is fair game for the prompt;
it's part of the trust surface, not solution-derived material.

### Resolution 2026-05-07: Option B implemented for `lemma.toml`

`build_task_prompt._sanitised_lemma_toml` now returns a hand-built V0-era
view of `lemma.toml`. The real file on disk is unchanged (the evaluator
still gates against the full real policy), but the prompt copy contains
only:

- the contract spec (`sink_theorem`, `constant_def`, `score`),
- import policies with all per-candidate `Candidates.V<N>` exact entries
  removed,
- six V0-era seed axioms (`hEq15_seed_3554` plus standard Lean),
- zero `[[oracles]]` table entries,
- zero sprint commentary.

### Related leak channel: `Numerical_Library/*.py` 🔴 still open

Even with sanitised `lemma.toml`, the test run showed the LLM can
sometimes guess oracle axiom names from `Numerical_Library` function
names. Concretely, `Numerical_Library/rigorous_scalar.py` (2433 lines)
contains functions like:

- `certify_eq15_at_hp_35645` → mirrors registered axiom `hEq15_oracle_certified_hp_35645`
- `certify_eq15_at_3560`     → mirrors `hEq15_oracle_certified_3560`
- `certify_seven_window_mass_at_356562_sqrt` → mirrors `h_seven_window_mass_certified_at_356562_sqrt`
- `certify_eight_window_mass_at_356564_modeJ7` → mirrors `h_eight_window_mass_certified_at_356564_modeJ7`
- `certify_eleven_window_mass_at_356565_modeJ10` → mirrors `h_eleven_window_mass_certified_at_356565_modeJ10`

A reasonably smart LLM, given the V0 seed pattern (`hEq15_seed_3554`),
can map the `certify_X` function name to the `hX_oracle_certified` /
`hX_certified_at_*` axiom name and try it. The evaluator continues to
gate against the real `lemma.toml` (which DOES list those axioms), so
guesses that match will pass.

A leak-string scan of the current 185 KB prompt finds:

- `oracle_certified`: 11 occurrences (all in Numerical_Library)
- `window_mass`: 130 occurrences
- `356562`, `356564`, `356565`: 32 occurrences total
- `certify_seven_window`: 15 occurrences
- `sprint 0`: 32 occurrences
- per-candidate references `V64`, `V66`, `V67`: 10 occurrences

**Decision needed.** Three options:

1. **Status quo (current ship):** include all of `Numerical_Library/*.py`
   per your earlier instruction. Fully ablation-aware users will note
   that this is a partial Option B. The LLM probably *will* still climb
   the oracle ladder, just by guessing instead of reading directly.
2. **Strip `rigorous_scalar.py` only.** It contains every `certify_*`
   function plus all sprint commentary. The other Numerical_Library
   files (`__init__.py`, `types.py`, `wang_box_math.py`,
   `wang_k_kernel.py`, `numerical_audit.py`, `independent_verify.py`,
   `generate_*.py`) stay. This removes ~95% of the leak strings.
3. **Strip all of `Numerical_Library/*.py` from the prompt.** V0 itself
   does not reference any oracle, so V0-era context strictly does not
   need any of this. Fully tight Option B.

### Resolution 2026-05-07: Option 2 (stricter than originally framed)

Per user direction, strip `rigorous_scalar.py` AND verify the other
Numerical_Library files do not reference specific c-values or proof
strategies/routes. Audit found 7 of 9 files leak the box-certificate
strategy or external-path references:

| file | reason | action |
|---|---|---|
| `__init__.py` | imports `certify_box`, `certify_partition`, `build_adaptive_certificate` | strip |
| `types.py` | `BoxCertificate`, `ScalarCertificate` dataclasses | strip |
| `wang_box_math.py` | `lambda_upper_witness_ok`, `mass_from_constant_box` | strip |
| `wang_k_kernel.py` | paper-level Wang K-kernel arithmetic only | **keep** |
| `numerical_audit.py` | parses `branch{N}_box_NNNN`; imports external `Korenblum/oracle/korenblum_oracle.K_product` | strip |
| `independent_verify.py` | imports same external oracle path; `_weighted_linear_mass_lower` | strip |
| `generate_candidate.py` | emits `KorenblumPaper.V{version}` namespace | strip |
| `generate_wang_candidate.py` | hard-codes `branch2_box_0369` (a prior-search artefact) | strip |
| `rigorous_scalar.py` | every `certify_*` function plus sprint commentary | strip |

After this change, leak-string scan reports **0 occurrences** across
the 51 needles (oracle_certified, window_mass, hCircleGapInt_v, hH2_v,
356562/356564/356565, V53–V68, certify_eq15_at_*, BoxCertificate,
build_adaptive_certificate, branch1_box/branch2_box, modeJ,
*_window, etc.). Prompt size dropped from 185 KB → 25 KB (≈ 6.2K
tokens). All V0-era essentials (paper, contract, sink theorem name,
Section2Assumptions, module index, wang K-kernel arithmetic) verified
present.

The `[seed_axioms]` block in `lemma.toml` contains 19 axioms. Of these,
only `hEq15_seed_3554` plus the standard Lean axioms (`Classical.choice`,
`propext`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`) are
V0-era. The other 13 are artefacts of prior search runs:

- `hEq15_oracle_certified_3554` / `_3560` / `_3562` / `_hp_3564` / `_hp_35645`
- `h_two_window_mass_certified_at_35646` (+ `_sqrt` variant)
- `h_seven_window_mass_certified_at_356562_sqrt`
- `h_eight_window_mass_certified_at_356564_modeJ7`
- `h_eleven_window_mass_certified_at_356565_modeJ10`
- `hCircleGapInt_v64`, `_v66`, `_v67`, `_v68`
- `hH2_v64`, `_v66`, `_v67`, `_v68`

By including the current `lemma.toml` verbatim in the prompt, the LLM
learns:

- the agent search has already reached at least c ≈ 0.35657
  (`356565` in the largest oracle name)
- specific techniques that worked: window-mass certification at 2 / 7 / 8 / 11
  modes, circle-gap integration, H² norm bounds
- that there are V64–V68 candidates (the `_v64`..`_v68` suffixes)

This is a real solution leak. Three ways to handle:

- **Option A (current default — show full `lemma.toml`):** maximises the
  realism of the trust surface and lets the LLM use prior oracle
  certifications. But effectively gives the ablation a "warm start" the
  agent search did not have.
- **Option B (sanitise `lemma.toml` for the prompt):** show a redacted
  `lemma.toml` to the LLM that lists only the V0-era seed axioms
  (`hEq15_seed_3554`, standard Lean) and zero oracles. The evaluator
  still gates against the full real `lemma.toml`, so the LLM *can* use
  prior oracles if it happens to mention them — but it has to invent
  the names, which means cleaner ablation. **Likely the right answer.**
- **Option C (rewrite `lemma.toml` to V0 state):** strictest. Fork
  `lemma.toml` for this run with seed_axioms = V0-era only and oracles
  = empty. Means the evaluator rejects any oracle-certified candidate.
  Maximally pure, but means the LLM cannot use any of the existing
  oracle infrastructure.

**Please confirm which option.** Default-shipped is A; B is one prompt-
build edit away.

Original notes preserved below for context.

---


You said the evolution must not see anything that could leak solutions from
prior runs. The system prompt and the seed include:

**Allowed (visible to the LLM):**

- `Wang2025.txt` — the source paper.
- `Proof/CandidateContract.lean` — the contract definition.
- `Proof/Reduction.lean` — the (15) → final-bound reduction (paper-faithful,
  trusted surface, not a search result).
- `Proof/ProblemAxioms.lean`, `Proof/Main.lean`, `Proof/Integrability.lean`,
  `Proof/Summability.lean`, `Proof/DiskInnerSeriesBridge.lean` — pinned
  trust surface (per `lemma.toml:[workspace_import_policy]`).
- `KorenblumPaper/*.lean` — pinned paper surface modules.
- The seed `Candidates/V0.lean` — the published `c = 0.3554` baseline.
- `lemma.toml` — what's allowed.

**Excluded:**

- `Candidates/V1.lean` … `Candidates/V68.lean` and any per-candidate
  subdirectories.
- `Bulletin.md`, `Experience.md`, `AGENT_BRIEF.md`, `START_HERE.md`,
  `AXIOM_EXTRACTION.md`, `V68_vs_Wang.md`.
- `Refinement_Log/`, `Sprint_Contracts/`, `Proposals/`, `Scratch/`.
- The agent harness wiring (`.claude/`, `scripts/`, `docs/`).

**Two things I'm uncertain about:**

1. `Proof/Reduction.lean`, `Proof/Integrability.lean`, `Proof/Summability.lean`
   — these are part of the trust surface today, but they were **derived during
   prior search sprints** (sprint comments in `lemma.toml` reference V53–V98
   hoists). Strictly, that's still solution-derived material that escaped into
   the trust surface. Including them gives the new run advantages the seed
   agent search did not start with.

   - Option A (what I shipped): include them, treat the trust surface as
     defined by `lemma.toml` today.
   - Option B: roll the trust surface back to what V0 actually used (just
     `Proof/CandidateContract.lean`, `Proof/Main.lean`,
     `Proof/ProblemAxioms.lean`, `KorenblumPaper/*`). Strictly cleaner
     ablation, but means re-establishing some intermediate lemmas in the
     evolution.

2. `Numerical_Library/*.py` — pure Python oracle code. It's part of the trust
   surface (referenced by `lemma.toml:[[oracles]]`) but only used at evaluator
   time. I am NOT showing it to the LLM in the prompt; the LLM only knows
   that registered oracle axioms exist. **Is that the right call?** If a
   candidate wants to invoke an oracle it would need the axiom name, which
   is in `lemma.toml`.

**Confirm Option A vs B for (1), and confirm the call on (2).**

---

## 6. Candidate staging — file lifecycle

ShinkaEvolve writes generated programs under
`results_dir/gen_<N>/program.lean`. To `lake build` them they must be inside
the Lean project. The flow is:

1. ShinkaEvolve writes `gen_<N>/program.lean`.
2. `evaluate.py` copies that file to
   `ProofRefinement/Korenblum/Candidates/Shinka_<run_id>_<gen_id>.lean`,
   rewriting the namespace to match the new module path.
3. `evaluate.py` runs `Evaluator.py --no-log` on the staged file.
4. `evaluate.py` parses the evaluator output, extracts the score, writes
   `metrics.json` for ShinkaEvolve.
5. `evaluate.py` removes the staged file (success or failure).

`--no-log` is passed so prior-run JSONL logs are not polluted.

**Resolved (2026-05-07):** running with `max_parallel_jobs=16`. Two
collision sources had to be made safe:

- *Staged candidate filenames* — already uuid-suffixed (`Shinka_<gen>_<uuid>.lean`).
- *`Evaluator.py` internal temp wrappers* — `theorem_type_check` and
  `collect_used_axioms` write fixed paths at `PROJECT_ROOT`. With 16
  parallel jobs they would clobber each other. Fix: `evaluate.py` now
  imports `Evaluator.py` in-process and monkey-patches just those two
  functions to use uuid-suffixed wrapper filenames. Gate logic
  unchanged. `Evaluator.py` itself is byte-untouched.

Lake handles the `.lake/build/` cache safely under concurrent invocations
(file locking on shared deps). Worth a single warmup `lake build
ProofRefinement.Korenblum.Proof.Main` before launching to populate caches.

---

## 7. EVOLVE-BLOCK scope — entire candidate or just the proof

The agent search rewrites the entire candidate file each sprint (V_n →
V_{n+1}). I made the EVOLVE-BLOCK encompass the **entire body** of the
candidate — `def c_value`, axioms, the theorem, all of it — so the search
space matches exactly.

There is one constraint outside the block: `import` lines and the
`namespace` declaration. The namespace must match the generated filename, so
I put `import` statements and `namespace` *outside* the EVOLVE-BLOCK and
have `evaluate.py` rewrite the namespace at staging time.

**Confirm**: full-file evolution is what you mean by "same search space".
If you want to lock down certain declarations (e.g. `c_value` as the only
target, with the rest of the proof fixed), tell me.

---

## 8. Lean trust-surface visibility — real asymmetry vs. the agent search

The agent search has Lean LSP tools (`lean_hover_info`, `lean_local_search`,
`lean_goal`, etc.) and uses them constantly. ShinkaEvolve has `tool_use=False`
(your spec) so the evolving LLM cannot interactively look up theorem
signatures or proof states.

I picked a middle ground for the prompt: include `CandidateContract.lean`
(24 lines), `ProblemAxioms.lean` (30 lines), `lemma.toml`, the paper text
(~12KB), the seed `V0.lean`, and a **module index** of the rest of the
trust surface (filename + one-line summary of each `Proof/*.lean` and
`KorenblumPaper/*.lean`). I did NOT inline the full source of `Reduction.lean`
(9.7K lines / 460KB), `WangKernelExact.lean` (1.1K lines), etc.

This is a known asymmetry. Two ways to handle it:

- **Match the agent search advantage** by inlining headers/signatures of
  every public theorem in the trust surface (probably 50–200KB of text,
  costly per generation but informative).
- **Accept the asymmetry** as part of the ablation — "tool-free baseline"
  is itself a meaningful comparison point.

I went with the second. **Confirm or override.**

---

## 9. Hyperparameters I picked (you said you'd fiddle later)

- `num_generations = 100`
- `max_parallel_jobs = 1`
- `patch_types = ["diff", "full"]` with probs `[0.7, 0.3]` — dropped `cross`
  because cross-pollination across Lean candidates is brittle.
- `num_islands = 2`, `archive_size = 30`, weighted parent selection,
  `parent_selection_lambda = 10.0`.
- One-model lineup: `["claude-opus-4-7"]`. You said "use the latest Opus";
  I read that as exclusive, so I did not mix in Sonnet or Gemini.
- `enable_tool_use = False`, as you specified.
- `max_patch_attempts = 3`, `max_patch_resamples = 3`.
- `temperatures = [0.5, 1.0]`.
- `reasoning_efforts = ["high"]`.

**Anything in here you want set differently up-front?**
