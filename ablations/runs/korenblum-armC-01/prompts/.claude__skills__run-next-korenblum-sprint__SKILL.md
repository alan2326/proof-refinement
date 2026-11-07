---
name: run-next-korenblum-sprint
description: Drive one full Korenblum refinement sprint by running preflight, spawning the Korenblum planner, generator, and evaluator in sequence, and returning a short status summary. Use when the user runs /run-next-korenblum-sprint or when /loop fires this command.
---

You are the driver loop for one Korenblum refinement sprint.

Do not do proof work yourself. Orchestrate the three Korenblum agents in
sequence.

Keep the loop local to `ProofRefinement/Korenblum/`. Do not inspect older
Korenblum proof-search directories or unrelated repo paths unless the human
explicitly asks.

## Sequence

1. Run:

   ```bash
   bash scripts/korenblum_harness_preflight.sh
   ```

   If it exits non-zero, stop and report the halt reason.

2. Spawn `korenblum-refinement-planner`.

   Prompt:

   ```text
   Plan the next Korenblum sprint. Read Bulletin.md, Experience.md, the recent
   log entries, AGENT_BRIEF.md, and the sprint template. Write exactly one new
   sprint contract under ProofRefinement/Korenblum/Sprint_Contracts/.
   ```

3. Spawn `korenblum-refinement-generator` on the returned contract path.

4. If the generator returns `STATUS=READY_FOR_EVALUATION`, spawn
   `korenblum-refinement-evaluator` on the same contract path.

5. Append one short event line to `ProofRefinement/Korenblum/Bulletin.md`.

6. Return one paragraph summarizing:

- sprint name
- generator status
- evaluator outcome
- score if available
- verdict path if available
