# Korenblum constant

Lean 4 project for the lower bound on the Korenblum constant.

| Directory | Contents |
| --- | --- |
| `KorenblumPaper/` | formalization of Section 2 of Wang (2025): the one-mode kernel, the finite-mode window, the paper's equation (15), and the side conditions |
| `ProofRefinement/Korenblum/` | the refinement workspace: contract and reduction in `Proof/`, candidates V0 to V68, the Arb oracle library, the evaluator, and every sprint contract and verdict |
| `ShinkaAblation/` | the ShinkaEvolve evolutionary baseline reported in the paper's appendix, with its results |

The final accepted candidate is `ProofRefinement/Korenblum/Candidates/V68.lean`
(c = 71313/200000 = 0.356565, eleven windows). `V68_vs_Wang.md` in the
workspace explains what changed relative to Wang's argument. See the top-level
README for the distinction between V68's quadrature oracle and V66's
interval-arithmetic oracle.

## Build and check

```bash
lake exe cache get
lake build
lake env lean ProofRefinement/Korenblum/Candidates/V68.lean
scripts/run_eval.sh                                    # evaluator on V68
scripts/run_eval.sh ProofRefinement/Korenblum/Candidates/V66.lean
```

## Running the loop

Start with `ProofRefinement/Korenblum/START_HERE.md`. The agents are defined in
`.claude/agents/` and `.claude/skills/run-next-korenblum-sprint/SKILL.md`
drives one sprint.

## ShinkaEvolve baseline

`ShinkaAblation/launch.sh` needs `ANTHROPIC_API_KEY` and a virtual environment
with [ShinkaEvolve](https://github.com/SakanaAI/ShinkaEvolve) installed,
passed as `SHINKA_VENV`. `build_task_prompt.py` reads the paper text from
`ProofRefinement/Korenblum/Wang2025.txt`, which is not included; supply your own
text extraction of Wang, "A lower bound on the Korenblum's constant", Proc. AMS
153 (2025), before running it. The recorded run is in
`ShinkaAblation/evo.log` and `ShinkaAblation/results/`.
