# Proof refinement for analytic constants

Code, Lean formalizations, and run records for the paper

> **Improving Analytic Constants via AI-Guided Lean Proof Refinement**
> Rahul Saha, Alan Li, Anton Xue, Swarat Chaudhuri, Adam Klivans, Pravesh K. Kothari, Raghu Meka. NeurIPS 2026.

The paper lets an agent loop edit a *partially formalized Lean blueprint* of an
existing proof, one candidate file at a time, and keeps an edit only when Lean
accepts it, the axiom audit passes, and the numerical claims it relies on are
recomputed by a certified backend. The quantity being improved is a constant in
the final theorem.

| Case study | Quantity | Start | Result | Final candidate |
| --- | --- | --- | --- | --- |
| Grothendieck constant | remainder constant C_r of Lemma 5.4 in Braverman et al. (2011); upper bound on K_G | C_r on the order of 10^15 (Krivine's bound minus 9.56e-33) | C_r = 2/7, giving K_G <= pi / (2 log(1+sqrt 2)) - 10^-17 | `grothendieck/ProofRefinement/Lemma54/Candidates/V28.lean` |
| Korenblum constant | certified radius c, a lower bound on K_K | 0.3554 (Wang 2025) | 0.356565 | `korenblum/ProofRefinement/Korenblum/Candidates/V68.lean` |
| Polygon-pi warm-up | kappa - lambda in a two-sided bracket of pi | 1 | 721/12000 | `polygon_pi/ProofRefinement/PolygonPi/Candidates/V5.lean` |

## Layout

```
grothendieck/   Lean project: the Braverman et al. proof (LeanProof/), the Lemma 5.4
                refinement workspace (ProofRefinement/Lemma54/), the proof-graph audit and
                runner (ProofGraph/), and the certified-arb oracles (grothendieck/proof/certified/)
korenblum/      Lean project: Wang (2025) Section 2 formalized (KorenblumPaper/), the
                refinement workspace (ProofRefinement/Korenblum/), and the ShinkaEvolve baseline
polygon_pi/     Lean project for the warm-up problem, plus the Opus 5 comparison run
ablations/      harness, analysis scripts, design docs, and run records for the ablation study
```

Each Lean project is self-contained: it has its own `lakefile.toml`,
`lake-manifest.json`, and `lean-toolchain`, all pinned to Lean 4 v4.28.0 and
Mathlib v4.28.0. Each project's README says what is in it and how to check the
final result.

## What a refinement workspace contains

The three workspaces (`ProofRefinement/Lemma54`, `ProofRefinement/Korenblum`,
`ProofRefinement/PolygonPi`) share one layout.

| Path | Role |
| --- | --- |
| `lemma.toml` | the sink theorem, the score expression, the allowed seed axioms, and the registered numerical oracles |
| `Proof/` | the trusted surface: the candidate contract and the reduction chain that connects a candidate to the published theorem |
| `Candidates/V<n>.lean` | one file per accepted or rejected candidate; the score is the rational it declares |
| `Numerical_Library/` | the oracle functions, computed with [Arb](https://arblib.org) through `python-flint` |
| `Evaluator.py` | compiles the candidate, runs `#print axioms`, recomputes every oracle it uses, scores it, and appends to `Refinement_Log/log.jsonl` |
| `Sprint_Contracts/`, `Refinement_Log/` | the planner's contract and the evaluator's verdict for every sprint |
| `Bulletin.md`, `Experience.md` | the agents' running notes |
| `AGENT_BRIEF.md`, `START_HERE.md` | what the agents were told |

The agent loop itself is a set of [Claude Code](https://claude.com/claude-code)
role definitions under each project's `.claude/agents/` (planner, generator,
evaluator) and a skill under `.claude/skills/` that runs one sprint: the planner
writes a contract, the generator edits Lean, the evaluator grades the result.
The harness design is written up in
`grothendieck/docs/PROOF_REFINEMENT_HARNESS.md`.

## Requirements

- [elan](https://github.com/leanprover/elan). Each project's `lean-toolchain` selects Lean 4 v4.28.0.
- Python 3.11 or newer and [uv](https://docs.astral.sh/uv/). The evaluators need `mpmath` and `python-flint` (declared in each project's `pyproject.toml`); the polygon-pi evaluator needs only the standard library.
- Claude Code, if you want to run the agent loop rather than just check the artifacts.

Mathlib is large. In each project, run `lake exe cache get` once before `lake build`.

## Checking a result

From a project directory:

```bash
lake exe cache get
lake build                                   # the trusted surface and the formalized papers
lake env lean ProofRefinement/<Workspace>/Candidates/V<n>.lean
uv run ProofRefinement/<Workspace>/Evaluator.py --file ProofRefinement/<Workspace>/Candidates/V<n>.lean --no-log
```

The evaluator prints every stage it runs. Pass `--skip-oracle` to skip the
numerical recomputation, which is the slow step.

## Caveats

The Grothendieck C_r values live on two scales. On 2026-05-03 the loop found
that the oracles of that era truncated a series without a tail bound, so every
candidate was re-audited under truncation-free oracles and C_r was re-based.
V28's C_r = 2/7 is a post-audit value. Candidates V9 to V26 and the ablation
study are on the earlier scale, which is why the ablation table reports ratios
to a checkpoint rather than absolute values. The details are in
`grothendieck/ProofRefinement/Lemma54/PATCH_NOTES.md`.

The two best Korenblum candidates differ in how their oracles integrate. The
oracle behind V68 (0.356565) integrates each window with mpmath adaptive
quadrature at high working precision (`_two_window_mass_window` in
`Numerical_Library/rigorous_scalar.py`). The oracle behind V66 (0.356562) was
migrated to Arb interval arithmetic in sprint 102, so V66 is the best candidate
whose numerics are interval-certified end to end.

`grothendieck/LeanProof/Rounding.lean` carries two `sorry`s in the rounding
argument, as documented in `grothendieck/ProofGraph/README.md`. The Lemma 5.4
chain that the candidates prove is sorry-free; the sink that assembles the full
Grothendieck inequality inherits those two.

The ablation harness rebuilds its starting workspaces from a commit of the
private development repository. The scripts and the gates that check a rebuilt
snapshot are included; the commit is not. The run records under
`ablations/runs/` are complete except for the model transcripts.

## What was left out

Build caches, virtual environments, model-session transcripts, exploratory
scratch scripts that nothing imports, the text of the two source papers, and
abandoned side projects from the development repositories. The MCP
configuration that the harness copies into a workspace is shipped as a
template without API keys.

## Citation

```bibtex
@inproceedings{saha2026proofrefinement,
  title     = {Improving Analytic Constants via {AI}-Guided {Lean} Proof Refinement},
  author    = {Saha, Rahul and Li, Alan and Xue, Anton and Chaudhuri, Swarat and Klivans, Adam and Kothari, Pravesh K. and Meka, Raghu},
  booktitle = {Advances in Neural Information Processing Systems},
  year      = {2026}
}
```

## License

Apache License 2.0. See `LICENSE`.
