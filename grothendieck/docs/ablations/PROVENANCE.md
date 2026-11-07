# Provenance of every number in the ablation section

All paths are under `ablations/` unless stated.
Design and execution record: `docs/2026-07-27-ablation-design.md` (Korenblum
§2–§10e; Grothendieck sprint-016 study §13–§13.7), `docs/2026-07-30-ablation-writeup.md`,
`docs/2026-07-30-grothendieck-ablation-summary.md`.

## Grothendieck (checkpoint: sprint 016 of the Lemma 5.4 run, V11, C_r = 1)

| Claim | Source |
|---|---|
| Checkpoint C_r = 1 → original run 1/32 in one iteration (2,360 s band) | design §13.1, §13.7.1 |
| No-Lean envelope 3.87e-4, BAR 1/6400 fixed before runs | design §13.7.2, `runs/groth16_envelope/envelope.json` |
| Reference budget 8,651.9 s, 544,294 output tokens, $35.59 | `runs/reference_budget_groth16.json` |
| Full framework: 1/400000; -01 sprint 1 → 7/1000; -02 sprint 3 → 1/400000; 18+34 = 52 turns; 3+6 = 9 evaluator runs | `runs/grothendieck016-armA-01/{summary.json,events.jsonl}`, `runs/grothendieck016-armA-02/{summary.json,events.jsonl}` |
| Basic agent: 9/100, 3/250, 1113/100000 (time-matched best), 1/250 (token-parity extension); 7 calls; wall 4,490.6+4,961.2+1,927.2 = 11,379 s; tokens 212,510+186,505+168,973 = 567,988; cost 22.28+17.90+14.51 = $54.70; evaluator runs 2+2+2 = 6; 2 rejections | `runs/grothendieck016-armB-0{1,2,3}/{summary.json,events.jsonl}` |
| Basic agent linter failure, two calls routing around, 287-line in-candidate proof | summary doc §Failure modes; `linter` present in `runs/grothendieck016-armB-0{2,3}/events.jsonl` |
| No agent: 6 samples; accepted 1/14, 1/10, 2/25, 8143/100000; sample 2 no file; sample 3 rejected; 9,042 s; 781,503 tokens; $32.19; 44% token overrun (781,503/544,294) | `runs/grothendieck016-armBos-01/{summary.json,events.jsonl}` |
| No PF: best 1782213978231/10^12; 3.96e-11 above Krivine (computed with mpmath, 30 digits); wall 4,120 (active, -01) + 5,973 = 10,093 s; tokens 328,469+409,797 = 738,266; 47+33 = 80 turns; 1+6 = 7 evaluator runs; 0 failures; $18.74+$25.32 = $44.06 | `runs/grothendieck016-armC-0{1,2}/summary.json`; C-02 evidence string gives the 4,120 s active figure |
| Six real sprints for no-PF (3 in -01 before the usage-limit error burn + 3 in -02) | `runs/grothendieck016-armC-0{1,2}/events.jsonl` |

## Korenblum (checkpoint: V64, c = 17823/50000 = 0.35646)

| Claim | Source |
|---|---|
| Anchor selection; original run 0.35646 → 0.356562 in five sprints (084–088); direction already on the roadmap | design §2.1–§2.2 |
| Full framework 17829/50000 = 0.35658; 3,285.4 s; 230,815 tokens; 14 turns; 2 evaluator runs; 0 failures; $20.65; per-mode criterion, oracle falsification point 35660/100000 | `runs/korenblum-armA-01/summary.json`; design §10c |
| Basic agent matched window (both-exceeded gate at 3,285.4 s / 230,815 tok): iter 1 no candidate, iter 2 pass 1114/3125 = 0.35648, iter 3 pass 35651/100000; best 0.35651, +5e-5; window state 3,425 s / 316,291 tok | `analysis/window_cut_korenblum.json` (produced by `analysis/window_cut_korenblum.py`) |
| Basic agent full run: iter 4 fail (3 UNREG axioms), iter 5 pass 0.35653, iter 6 helper module without candidate, iter 7 fail; 2,721.3+7,868.9 = 10,590 s; 253,391+715,215 = 968,606 tok; $23.44+$70.24 = $93.68; 1+4 = 5 evaluator runs | design §10e; `runs/korenblum-armB-0{1,2}/summary.json` |
| ~23 lines of non-numeral diff vs V64; 12-line endpoint inequality closed by norm_num/linarith | design §10e "How Arm B wrote correct Lean one-shot" |
| No agent: 3 attempts in window, 0 candidate files (wrote lemma.toml and two_window_v65.py only); 4,092.6 s; 407,860 tok; $24.73; 4th attempt in flight at SIGTERM | `runs/korenblum-armBos-01/summary.json`, `runs/korenblum_armBos.console.log`, `analysis/window_cut_korenblum.json` |
| No PF: 25,409.6 s (7.06 h); 1,800,402 tok; 60 turns; 19 evaluator runs; 0 failures; $118.38; 11 candidates; 5,646 lines / 11 modules; 0 axioms, 0 sorry; first c-push attempt at sprint 009; 3× budget = 24,966 s and 692,445 tok | `runs/korenblum-armC-02/summary.json`; design §10e "Arm C was not idle"; `runs/reference_budget.json` |

## Other

| Claim | Source |
|---|---|
| Models: claude-opus-5 for all generative work; claude-sonnet-5 subagent in A and C | `per_model` blocks in every `runs/*/summary.json` |
| Tool-less arms inside Claude Code with tools disallowed; zero tool invocations verified | design §10d, summary doc §Caveats |
| Hardware: 2× Xeon Platinum 8352Y, 128 threads, 503 GB; Lean/Mathlib v4.28.0 | `lscpu`, `free -g`, `workspaces/S0_*/lean-toolchain`, `lake-manifest.json` |
| ShinkaEvolve: 100 generations, 103 programs, 88 pass at 0.3554, 15 fail, max 0.3554; claude-opus-4-7; tool use disabled; 4 islands, 16 jobs; seed = published V0 at 0.3554 | `korenblum/ShinkaAblation/{README.md,evo.log,results/experiment_config.yaml}`, sqlite `programs` table |

## Reconciliation with the rebuttal numbers (TODO.md table)

All four rebuttal cells are kept, under the rule the rebuttal note itself used:
every configuration runs to at least the full framework's wall clock and output
tokens, and the reported value is the best accepted candidate among iterations
that *began* within the token reference (`ablation_reviewer_response_additions.md`:
"iteration 2 started at 149,515 cumulative tokens (under budget) ... iteration 3
(0.35651, 1.4x tokens) ... fall outside the matched budget on the token axis").

* Korenblum basic agent: iteration 2 began at 149,515 < 230,815 tokens → 0.35648
  (+2.0e-5). Iteration 3 began at 253,391 → excluded. Run on to 10,590 s / 968,606
  tokens it reached 0.35653 (+7e-5), reported in the appendix.
* Grothendieck basic agent: its 1/250 iteration (`armB-03` iter 2) began at 477,826
  < 544,294 tokens → included, 250×.
* All other cells are unaffected by the cut.
* The success criteria (Korenblum: any gain; Grothendieck: Cr ≤ 1/6400) only govern
  when the *full framework* stops and so define the reference budget; the section
  no longer presents the ablated arms as stopping at success, since that would
  confound gain size with stopping. `korenblum-armB-01` did in fact stop at its
  first success under the registered protocol, and `armB-02` is the continuation;
  the token-start cut makes that distinction irrelevant to the reported cell.
* A both-exceeded cut (`analysis/window_cut_korenblum.json`) would give 0.35651
  (+5.0e-5) for the Korenblum basic agent; the appendix discloses this.

## Model attribution (what the records say)

* Ablations (July 2026): `summary.json` → `per_model` / `modelUsage.canonicalModel`
  records `claude-opus-5` for every generative role and `claude-sonnet-5` for the
  evaluator subagent in the full-framework and no-PF runs.
* Main runs (April–May 2026): the agent definitions (`.claude/agents/*.md`) use the
  aliases `model: opus` / `model: sonnet`; the May 2026 session transcripts are gone,
  so the concrete ids are not recoverable from disk. The manuscript's "Claude Opus 4.7"
  is consistent with the ShinkaEvolve baseline of 2026-05-07, which pinned
  `claude-opus-4-7` in `korenblum/ShinkaAblation/shinka_lean_patch.py`, and with the
  design doc's note that "the original ran on the May-2026 Opus, this on claude-opus-5" (§10c).
  Note the evaluator role in the main runs used the `sonnet` alias, so "all three agent
  roles backed by Claude Opus 4.7" in Section 4.3 is not quite what the agent files say.

## The two C_r scales

* The main run's certified C_r trace (paper_artifacts/refinement_math.tex "Summary of trace"):
  8.2e14 → 1.13e9 → 3.79 → 1 → 1/268,000 (pre-truncation-free units), then after the
  2026-05-03 K_max patch (ProofRefinement/Lemma54/PATCH_NOTES.md) → 0.3255 (patched V11)
  → 1/3 (V27, sprint 033) → 2/7 ≈ 0.2857 (V28, sprint 034, the last PASS in Bulletin.md;
  audit floor 0.2810).
* The ablation checkpoint is sprint 016 (2026-04-30), i.e. the "1" in that trace, three
  days before the patch; the S0 snapshot contains no PATCH_NOTES.md. Its values
  (1 → 1/400000 etc.) are pre-patch units on the shared K_max-era oracle surface
  (design §12.1 disclosure). The section now says so explicitly.
* The manuscript's "C_r ≤ 0.35" is not a value that appears in the logs. Nearest
  candidates: V27's 1/3 ≈ 0.333 and the patched-V11 floor 0.3255 (rounded up), or the
  final 2/7 ≈ 0.286. The authors should state which; it is outside this section.
