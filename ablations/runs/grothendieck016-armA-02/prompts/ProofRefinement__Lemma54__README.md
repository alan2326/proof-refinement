# Lemma 5.4 — Proof Refinement Workspace

Iterative proof-search workspace for refining the constant `Cr` in Lemma 5.4
of Braverman et al. (2011). Each candidate is a single Lean file in
`Candidates/`; the score is the rational `Cr_val` it declares. Smaller is
better.

**If you are an agent here to refine the proof, start with
[AGENT_BRIEF.md](AGENT_BRIEF.md).** This README is the layout reference;
the brief is the task.

## Relationship to the production proof

This workspace is **exploratory**. The current production proof of
Lemma 5.4 lives in:

- [`Proof/Lib/Lemma54_Paper_Main.lean`](Proof/Lib/Lemma54_Paper_Main.lean)
  — proves `lemma_5_4_paper_on_domain` and `lemma_5_4_paper` from 12
  trusted analytic axioms about the IFT-supplied family `F_inv_paper`
  (declared in [`Proof/Lib/Lemma54_Paper.lean`](Proof/Lib/Lemma54_Paper.lean)).
  Cauchy estimates, identity (75), `∂²ₚ F_inv` bound, Taylor-in-p in the
  `Lemma54_Paper_{Cauchy,Identity,Pderiv,Pderiv_Single,Taylor}.lean`
  chain.
- [`../../ProofGraph/Effective/Lemma54Effective.lean`](../../ProofGraph/Effective/Lemma54Effective.lean)
  — the proof-graph layer that instantiates `lemma_5_4_paper_on_domain`
  at the concrete tuple `(eta_val=1/100, r_val=23/25, M_val=4000)` over
  the explicit Step-1/Step-2 rectangle `Ω(δ_val=57/1000, B_val=293/250)`.

The candidate-iteration framework here predates that work. The seed
`Candidates/V0.lean` still uses `M = 5, R = 6/5` and one big
`paper_taylor_argument` axiom; it scores `Cr_val ≈ 1.4·10⁹` (intentionally
loose). It is a starting point for *alternative* refinement directions
(different `Cr` factorizations, different bound decompositions, candidate
proofs of axioms that could be ported to the production path), not an
approximation of the current state of the formalization.

For the production trust boundary, audit, and certified-arb runner, see
[`../../ProofGraph/README.md`](../../ProofGraph/README.md) and
[`../../ProofGraph/STATUS_AND_PLAN.md`](../../ProofGraph/STATUS_AND_PLAN.md).

## Layout

```
ProofRefinement/Lemma54/
├── Candidates/                 # Lean candidates. V0 = original paper-faithful seed.
│   └── V0.lean
├── Proof/                      # Non-evolved Lean infrastructure (also fed into production).
│   ├── SearchConfig.lean       # Locked: eta = 1/100, r = 23/25.
│   └── Lib/
│       ├── Lemma54_Cauchy.lean             # Cauchy coefficient bounds (Mathlib glue).
│       ├── Lemma54_Paper.lean              # 12 trusted axioms about F_inv_paper + Cr_paper closed-form definition.
│       ├── Lemma54_Paper_Cauchy.lean       # Recentred Cauchy estimates on disk r₁.
│       ├── Lemma54_Paper_Identity.lean     # Auxiliary z-identity from differentiating F_p ∘ F_inv = id.
│       ├── Lemma54_Paper_Pderiv.lean       # Paper's first-derivative bound.
│       ├── Lemma54_Paper_Pderiv_Single.lean # Single-M recasting (`F_inv_p_second_deriv_bound_paper`).
│       ├── Lemma54_Paper_Taylor.lean       # Taylor-remainder-in-p machinery.
│       └── Lemma54_Paper_Main.lean         # `lemma_5_4_paper_on_domain` and `lemma_5_4_paper`.
├── Numerical_Library/          # Python (Arb-backed) bound functions used by the candidate evaluator.
├── lemma.toml                  # Per-lemma config: sink, score, seed axioms, oracles.
├── Refinement_Log/             # Append-only JSONL log of evaluations.
├── Evaluator.py                # Audit + compile + score, single file.
├── Experience.md               # Agent log: findings, future directions.
├── Scratch/                    # Persistent research notebook across sprints.
│                                 #   Convention: sprint_<NNN>_<topic>.py
└── _archive/                   # Previous Banach-FPT-era artifacts (not active).
```

The certified-arb pipeline that ProofGraph uses (`compute_M_rigorous`,
`compute_Cr_full`, etc.) lives outside this workspace at
[`../../grothendieck/proof/certified/`](../../grothendieck/proof/certified/);
the Numerical_Library here wraps it for the per-candidate evaluator.

Design and rationale: see
[`../../docs/PROOF_REFINEMENT_DESIGN.md`](../../docs/PROOF_REFINEMENT_DESIGN.md).

## What V0 contains

`Candidates/V0.lean` is now a **production-faithful mirror** of
`ProofGraph/Effective/Lemma54Effective.lean`. Same constants
(`M_val = 4000`, `delta_val = 57/1000`, `B_val = 293/250`,
`SearchConfig.eta = 1/100`, `SearchConfig.r = 23/25`), same oracle
rectangle `Ω(δ_val, B_val)`, same `Cr_paper` formula. The sink
`Braverman.PaperV0.lemma_5_4_search` is proved by direct delegation
to `Braverman.Paper.lemma_5_4_paper_on_domain` at the production
tuple.

```
Cr_val := Cr_paper r_val M_val (R_val_paper r_val) ≈ 8.196·10¹⁴
```

(Same as production. The Evaluator falls through to
`proof_graph.cert_compute.evaluate_symbolic` to get a rational upper
bound.)

V0 declares **two custom axioms**, matching production:

| Axiom | Source | Meaning |
|---|---|---|
| `h_M_oracle` | eq. (76) | Single-`M` sup bound on `Ω(δ_val, B_val)`. Backed by `compute_M_bound_production` (≈ 3600.44). |
| `h_oracle_domain_contains_image` | Lemma 5.3 + Rouché | `F_inv_paper(disk r) ⊆ Ω(δ_val, B_val)`. Structural (Rouché-certified by the production runner; not re-checked per candidate run). |

Plus the standard Lean 3 (`propext`, `Classical.choice`, `Quot.sound`)
and the **12 trusted analytic axioms** about `F_inv_paper`
(transitively pulled from `Proof/Lib/Lemma54_Paper.lean`).

The legacy V0 (paper-faithful seed with `M = 5`, `R = 6/5` and
`paper_taylor_argument` mega-axiom) lives at
`_archive/seed_v0_pre_production_mirror/V0.lean` for reference.

## Workflow

```bash
# Evaluate a candidate (compiles + audits axioms + scores):
uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V0.lean

# Faster iteration (no oracle reverification):
uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean --skip-oracle

# Just parse + score, no Lean build:
uv run ProofRefinement/Lemma54/Evaluator.py --file Candidates/V0.lean --skip-compile
```

The evaluator's pipeline (see `Evaluator.py` docstring for details):

1. **PARSE** — extract `def *_val : ℝ := <rat>` and `axiom *` declarations.
2. **COMPILE** — `lake env lean Candidates/<file>` must succeed with no
   errors.
3. **AXIOM AUDIT** — every dependency reported by `#print axioms` must be
   either a SEED axiom (registered in `lemma.toml:[seed_axioms].allowed`)
   or an oracle-backed axiom (registered in `lemma.toml:[[oracles]]`)
   whose recomputed bound is `≤` the candidate's declared rational.
   `sorryAx` is a hard fail.
4. **SCORE** — symbolically evaluate `Cr_val` over the candidate's other
   `*_val` rationals.

The companion proof-graph audit
(`PYTHONPATH=ProofGraph uv run python -m ProofGraph.proof_graph
--audit-snapshot`) checks the *production* axiom boundary — not
candidates here. Two separate audit pipelines, two separate purposes.

## Adding an oracle-backed axiom

When a candidate splits a structural axiom into smaller pieces, each new
"numerical" axiom must be wired to a Python function in
`Numerical_Library/` and registered in `lemma.toml`. The evaluator will
then recompute the bound on every run and reject the candidate if the
declared rational is below the certified value.

Concrete steps:

1. Implement `compute_<X>_bound(...) -> OracleResult` in
   `Numerical_Library/<x>_bound.py` and re-export it from
   `Numerical_Library/__init__.py`.
2. Add an `[[oracles]]` table to `lemma.toml`:
   ```toml
   [[oracles]]
   axiom       = "h<X>_bound"
   bound_field = "<field>_val"
   oracle_fn   = "compute_<X>_bound"
   ```
3. In the candidate, declare both:
   ```lean
   def <field>_val : ℝ := <num> / <den>
   axiom h<X>_bound : <Lean statement bounded by <field>_val>
   ```

To carry over a paper-cited axiom from V0 (or from later candidates)
without an oracle, append its fully-qualified name to `lemma.toml`'s
`seed_axioms.allowed`.

## Refinement log

Every evaluation (pass or fail) appends one JSON record to
`Refinement_Log/log.jsonl`. Fields include the candidate path + sha256,
the optional `-- @parent <path>` declared at the top of the candidate,
the score (as a Fraction), the def-vals snapshot, the audited axioms
classified seed/oracle, and timing. To opt out: `--no-log`.

## Per-run isolation

For a fully isolated run (separate `Candidates/`, `Experience.md`,
`Scratch/` per agent loop), copy this directory:

```bash
cp -r ProofRefinement/Lemma54/ ProofRefinement/Lemma54_run_$(date +%Y%m%d_%H%M)/
```

The Lean imports use absolute module paths
(`ProofRefinement.Lemma54.Proof.SearchConfig` etc.), so the *original*
`Proof/` and `Numerical_Library/` are still referenced unless you also
adjust the `lakefile.toml` to add the run-specific lib. For lightweight
isolation (everything besides the shared `Proof/Lib`), having only
`Candidates/` and `Experience.md` per run is usually sufficient — the
agent only writes new candidate files anyway.

## Long-running harness (Planner / Generator / Evaluator)

When you want a hands-off iteration loop instead of a single agent
session, use the three-role harness defined in
[`docs/PROOF_REFINEMENT_HARNESS.md`](../../docs/PROOF_REFINEMENT_HARNESS.md).

Layout the harness adds to this directory:

```
ProofRefinement/Lemma54/
├── Bulletin.md                 # Volatile, ≤100 lines, current priority + recent events.
├── Sprint_Contracts/           # One contract per sprint (NNN-numbered).
│   ├── TEMPLATE.md
│   └── sprint_001.md           # First shakedown contract.
├── Sprint_State/               # Per-sprint scratch (lake build logs, etc).
└── Refinement_Log/
    ├── log.jsonl               # Append-only verdict log.
    └── verdict_<NNN>.md        # One Markdown verdict per sprint.
```

Three sub-agents (defined in `.claude/agents/`):

- **`refinement-planner`** writes one Sprint Contract per invocation.
  Reads `Bulletin.md`, the last 10 log entries, the current contract,
  `STATUS_AND_PLAN.md` (priorities only), and this `AGENT_BRIEF.md`.
  Never edits Lean. Opus.
- **`refinement-generator`** executes one Sprint Contract. Edits only
  the files the contract names. Cannot add new axioms. Terminates
  with a labeled `STATUS=` line. Sonnet.
- **`refinement-evaluator`** runs the validation gates literally and
  writes a verdict file. Cannot edit Lean. Sonnet.

Drive a single end-to-end sprint with the slash command:

```
/run-next-sprint
```

Or run autonomously with the built-in loop (interval-based or
self-paced):

```
/loop 30m /run-next-sprint
```

Helper scripts:

- `scripts/harness_reset.sh` — archives all current candidates (V1+),
  Sprint Contracts (sprint_002+), verdicts, log entries,
  Sprint_State scratch, Bulletin and Experience into
  `_archive/runs/<timestamp>/`. Re-seeds `log.jsonl` with V0's most
  recent baseline. Run before kicking off a fresh harness session.
  `bash scripts/harness_reset.sh --dry-run` previews moves.
- `scripts/harness_preflight.sh` — halts the loop on
  3-consecutive-FAILs on the same goal.
- `scripts/runner_cache_check.sh` — short-circuits the slow
  `--run-all` gate when the four cache-input files
  (`_index.toml`, `Lemma54Effective.lean`, `Theorem51AtPExplicit.lean`,
  `Theorem51Effective.lean`) are byte-identical to a previous
  fully-passing certificate. The runner records `inputs_sha256` in
  `certificate.json`. Used during human-driven post-port
  verification, not in the loop itself.

The harness's hard constraints, repeated here so they're impossible
to miss:

1. **Contract-driven write scope.** The Generator may modify any
   pre-existing file in the Lemma 5.4 ecosystem (`Proof/Lib/`,
   `Numerical_Library/`, `ProofGraph/Effective/Lemma54*.lean`,
   `LeanProof/Lemma54.lean`, `LeanProof/Defs/Strip.lean`) — but
   only files named in the Sprint Contract's `Concrete edits
   expected:` list. The Evaluator's `G3: write scope` gate
   enforces this. Loss prevention is handled by the project's git
   auto-checkpoint hook (every Edit/Write commits), so any
   modification is recoverable from history.
2. **History is sacrosanct.** Older candidates
   (`Candidates/V<K>.lean` for `K < N`) are never modified.
   Sprint Contracts, `Evaluator.py`, runner code, TOML node
   configs, and helper scripts are also off-limits — those encode
   the trust boundary itself.
3. **No new axioms.** A candidate may use existing seed/oracle
   axioms registered in `lemma.toml`; it may *prove* an axiom as a
   theorem (removing it from the audited set); it may not introduce
   a new `axiom` declaration. The Evaluator's `G4: no new axioms`
   gate enforces this.
4. **Generator never grades its own work.** The Evaluator runs in a
   separate session and only consults the gates, never the
   Generator's narrative.
5. **All-cheap gates.** No sprint runs the production audit or
   `--run-all`. All six gates are fast (~30s total). Production
   verification happens out-of-loop when a human ports a winning
   candidate.
6. **File-based handoff.** No agent state lives in conversation
   context; everything important is in a file under this directory.

## Where the production proof picks up

When a candidate's improvement is significant and well-validated, the
natural next step is to port it to the production path:

- **Tighter `Cr` formulations** → add a parallel `Cr_*` definition
  in `Proof/Lib/Lemma54_Paper.lean` and a corresponding bridge
  theorem in a new file alongside it; then update
  `ProofGraph/Effective/Lemma54Effective.lean:Cr_val` to use it.
- **Newly-proved analytic axioms** → move the proof from `Candidates/`
  into the appropriate `Proof/Lib/Lemma54_Paper_*.lean` file, then
  remove the axiom from `Proof/Lib/Lemma54_Paper.lean`. The production
  audit count (currently 12 trusted analytic at the lemma level,
  contributing to the sink's 24) drops by one.
- **Tighter numerical bounds** → reduce `M_val` in
  `ProofGraph/Effective/Lemma54Effective.lean` (currently `4000`,
  certified above the `compute_M_rigorous` value of `~3531`) and
  re-run the proof-graph audit + runner to confirm the cross-checks
  still pass.
