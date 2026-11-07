# Ablation study

Harness, analysis, design record, and run records for the ablations in the
paper (Section 5.3 and Appendix D). Each configuration restarts from a
checkpoint of a main run and optimizes the same quantity for a matched budget.

| Path | Contents |
| --- | --- |
| `docs/2026-07-27-ablation-design.md` | the design and execution record: Korenblum study (sections 1 to 10e), Grothendieck sprint-016 study (section 13). Later sections describe variants that were not used |
| `docs/2026-07-30-ablation-writeup.md`, `docs/2026-07-30-grothendieck-ablation-summary.md` | the write-ups the paper's numbers come from |
| `harness/` | runners for the four configurations, workspace builders, and acceptance gates |
| `analysis/` | the DNF classifiers and the matched-window cut, with their JSON outputs |
| `runs/` | one directory per cited run: `manifest.json`, `summary.json`, `events.jsonl`, the prompts, per-iteration results, and the static context the tool-less configurations received |
| `korenblum_no_partial_formalization/` | the seed workspace for the Korenblum no-partial-formalization configuration |

## Runs

| Study | Full framework | Basic agent | No agent | No partial formalization |
| --- | --- | --- | --- | --- |
| Korenblum | `korenblum-armA-01` | `korenblum-armB-01`, `-02` | `korenblum-armBos-01` | `korenblum-armC-02` |
| Grothendieck (sprint 016) | `grothendieck016-armA-01`, `-02` | `grothendieck016-armB-01`, `-02`, `-03` | `grothendieck016-armBos-01` | `grothendieck016-armC-01`, `-02` |

`runs/reference_budget*.json` hold the matched budgets, and
`runs/groth16_envelope/` holds the no-Lean envelope and the success bar fixed
before the Grothendieck runs. Model transcripts are not included, and the
`static_context.md` files have the source-paper text removed.

## Harness

Scripts resolve the repository root from their own location. The workspace
builders expect the sibling `korenblum/` and `grothendieck/` projects to be
built, and read them through `KORENBLUM_SRC` and `GROTHENDIECK_SRC` if they
live elsewhere.

```
harness/make_s0.sh                 reconstruct the Korenblum checkpoint (sprint 083, V64)
harness/gate_s0.sh                 acceptance gate for that checkpoint
harness/make_arm_ws.sh ARM         clone the checkpoint into an arm workspace
harness/make_arm_c.py              build the no-partial-formalization workspace
harness/run_arm_{a,b,b_oneshot,c}.py   the four Korenblum configurations
harness/pipeline.sh                the whole Korenblum study
harness/*groth16*                  the same for the Grothendieck sprint-016 study
```

Two things cannot be rebuilt from this repository alone. `make_s0_grothendieck016.sh`
takes its snapshot from a commit of the private development repository, and the
runners read the source paper text as context (`harness/braverman2011.txt` in
the original tree). The runners drive Claude Code's command line
(`claude -p`), so they need it installed and authenticated.

`harness/mcp.template.json` replaces the original MCP configuration, which held
an API key.
