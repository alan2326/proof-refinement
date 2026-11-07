# Sprint 053: Register parametric `hEq15_oracle_certified` via `Numerical_Library`, ship V48 at the seed

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V47.lean`
**Target file**: `Candidates/V48.lean`
**Direction**: oracle-support (pre-approved `[[oracles]]` channel; no `Proposals/` filing)

## Goal

Implement and register **the bulletin-prescribed parametric oracle wrapper for
Wang's equation `(15)`** that has been the explicitly named blocker for five
sprints. Specifically:

1. Add a wrapper function `certify_eq15(c_num, c_den, dps, n_trunc) -> bool`
   inside `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
   that returns `True` iff Wang's scalar criterion
   `1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c)` holds at
   `c = c_num / c_den` under verified-interval arithmetic at the requested
   precision envelope.
2. Register a new entry under `[[oracles]]` in
   `ProofRefinement/Korenblum/lemma.toml` named `eq15_certified_at_seed`
   that points the Evaluator at this wrapper at exactly the seed inputs
   `(c_num, c_den) = (3554, 10000)`, `dps = 50`, `n_trunc = 200`.
3. Append the matching Lean-facing axiom name
   `hEq15_oracle_certified_3554` to `[seed_axioms].allowed`.
4. Ship `Candidates/V48.lean`: declare
   ```lean
   axiom hEq15_oracle_certified_3554 (K : ℝ → ℝ → ℝ) :
     PaperAxioms.Eq15ScalarBound K c_value
   ```
   at `c_value := 3554 / 10000` and discharge the contract via
   `valid_of_eq15` exactly as `V0` does, only routing the `(15)` premise
   through the new oracle-backed axiom instead of the literal seed
   `hEq15_seed_3554`.

**The `c_value` in V48 is unchanged at `1777/5000 = 3554/10000`. This sprint
deliberately does not push `c`.** Per the bulletin's second 2026-05-02
directive (lines 219–313, "Sprint 052 — register the oracle wrapper, ship
`c = 0.3554` unchanged"), this is the prerequisite reshaping of the trust
surface that the next sprint (054) needs in order to push `c` to
`1779/5000 = 0.3558` without touching `lemma.toml` again.

The fixed final theorem statement
`theorem korenblum_constant_search : ValidKorenblumBound c_value` is
unchanged.

## Why

### What the bulletin's second directive of 2026-05-02 demands

The bulletin's second directive (Bulletin.md lines 219–313) says exactly:

> Sprints 048–051 are now four roadmap-only sprints in a row that produced
> `Scratch/` evidence and one pending `Proposals/` entry but **zero changes
> to `lemma.toml` and zero new candidates**. The blocker is not paper
> surface or trust base — it is that nobody has actually used the
> `[[oracles]]` registration mechanism that the harness has had since day
> one.

and the prescribed Sprint 052 plan (lines 263–272) literally says:

> **Sprint 052 — register the oracle wrapper, ship `c = 0.3554` unchanged.**
> Goal: write
> `Numerical_Library.rigorous_scalar.certify_eq15(c, dps, N)`,
> add the `[[oracles]]` entry, write the corresponding `axiom
> hEq15_oracle_certified` Lean statement, and ship `Candidates/V48` that
> uses the oracle to discharge `Eq15ScalarBound K (1777/5000)`. **This
> sprint deliberately does not push `c`.** Score ties V47, but the trust
> surface changes: `axioms_used ⊆ {seed} ∪ {hEq15_oracle_certified}`
> instead of `{seed} ∪ {hEq15_seed_3554}`. The harness is now one sprint
> away from any `c` the oracle covers.

The previous planner (sprint 052) did not execute this plan. They instead
filed `proposal_002` for a structurally different per-`k` series oracle
(`sigma_plus_int_kernel_at_36_100`) that targets `c = 36/100` via sprint
045's reducer — leaving the bulletin-prescribed wrapper sprint *still
un-done*. The result is that the workspace is `BLOCKED_NEEDS_HUMAN` on
two pending proposals while the directly-prescribed pre-approved-channel
work remains available and untouched. This sprint executes that overdue
plan.

### Why this is an authorised oracle, not a new proposal

Per `AGENT_BRIEF.md` §"Numerical tooling":

> Future sprints can add those entries inline when there is a clear
> Lean-facing oracle statement to certify and the sprint contract names the
> required `Numerical_Library` function, `lemma.toml` entry, and Lean-facing
> axiom/use site. Use `ProofRefinement/Korenblum/Proposals/` only for
> non-oracle trust-base expansions.

This contract names all three (function `certify_eq15` in
`Numerical_Library/rigorous_scalar.py`; oracle entry `eq15_certified_at_seed`
in `lemma.toml:[[oracles]]`; Lean axiom
`hEq15_oracle_certified_3554` declared in `Candidates/V48.lean`). No
`Proposals/` filing is required, and the workspace stays at 2/3 pending
proposals (no third proposal added).

### Why this advances `c_value > 0.3554` even though V48 ties V47 at 1777/5000

By itself V48 ties V47, so under the bulletin's first directive ("tying V0 is
no longer a win") V48 is **not** a win in isolation. The bulletin's second
directive (lines 295–298) explicitly resolves this:

> Each sprint compiles one candidate, the evaluator records the result, and
> the bulletin gains one row. The harness was not built to find the optimal
> `c` in a single sprint — it was built so a chain of small, verifiable
> steps converges on it. […] Aim for the closest verified step, not the
> limit.

The oracle wrapper is the **structural prerequisite** for the per-sprint
c-push cascade. Once V48 ships with `axioms_used ⊆ {seed} ∪
{hEq15_oracle_certified_3554}`, sprint 054 can ship V49 at
`c_value = 1779/5000 = 0.3558` (margin `+1.131e-2` at `c = 0.3560` per
sprint 050's mpmath dps=50 reverification, so `0.3558` sits comfortably in
the verified positive band) by simply *re-pointing* the same oracle wrapper
at a different `(c_num, c_den)` and re-running the evaluator. This is the
"one sprint away from any `c` the oracle covers" property the bulletin
asks for. Without sprint 053, sprint 054 cannot exist.

### Roadmap to `c > 0.3554` (per bulletin requirement for next-sprint contracts)

1. **Cheapest existing closing reducer**: `valid_of_eq15` (Reduction.lean
   lines 89–101). Kernel inequality:
   `1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c)`,
   i.e. literal Wang `(15)`. Paper-axiom signature `{eq15}` only;
   zero oracle cells before sprint 053; one oracle cell after this
   sprint (the `(15)` premise discharged by
   `hEq15_oracle_certified_3554`).
2. **Numerical kernel at `(c, ρ_split, ρ_max)`**: at the seed
   `c = 3554/10000`,
   `branchSplit c = c·√(4/3) ≈ 0.4103`. The kernel
   `1 ≤ ∫_{c..branchSplit c} 12ρ³(ρ²−c²)/(c⁶ Λ(c,ρ)) dρ +
        ∫_{branchSplit c..1} 4ρ³/(c⁴ Λ(c,ρ)) dρ` is the literal
   `Korenblum.scalarCriterion` unfolded. Sprint 049's
   `Scratch/sprint_049_paper_eq15_direct_kernel.txt` confirms this
   matches Wang's printed `(15)` byte-for-byte.
3. **Margin at the chosen `c`**: at the seed `c = 3554/10000` the
   sprint 050 mpmath `dps=50, N_TRUNC=200` re-verification reports
   `gap = +2.55e-02`; at `c = 1779/5000 = 3558/10000` the gap is
   `+0.0207` (sprint 050 crossover-pinpoint table); at
   `c = 3560/10000` the gap is `+0.0113`; at `c = 3565/10000` the
   gap is `−3.598e-04` (sprint 050's narrow shoulder). The
   harness's planned cascade therefore runs
   `3554 → 3558 → 3560 → 3562` and stops; pushing past `3562/10000`
   requires either a higher-precision reverification or one of the
   pending Proposals.
4. **Trust gap**: the kernel is *not* a closed-form rational at any
   `c > 0`. `paperLambda K c ρ` is defined via the
   one-mode-Bridge `K`-formula whose value depends on
   `√(…(c, ρ)…)`, and `scalarIntegrand1`/`scalarIntegrand2` are
   non-elementary in `ρ`. So the kernel cannot be discharged by
   `norm_num` or `polyrith`. It must be discharged either (a) by a
   verified-interval-arithmetic oracle that bounds the integrals
   from below and computes the sum strictly above 1, or (b) by a
   full Lean derivation of `(15)` from Wang's Section 2 paper-axiom
   surface (multi-month research, not in scope).
5. **Route per cell**: route (a) — register an oracle. The wrapper
   `Numerical_Library.rigorous_scalar.certify_eq15` already has all
   the verified-`paperLambda` infrastructure it needs in
   `rigorous_scalar.py` (functions `lambda_upper_on_interval`,
   `_inv_lambda_lower_from_k_upper_fraction`, `_arb_box`,
   `_pow_cached`, `_k_factor_arb`, `_prefactor_arb` — all already
   shipped). The new wrapper composes these to certify the literal
   sum-of-two-integrals lower bound `≥ 1`.
6. **Candidate at `c > 0.3554`**: not this sprint. Sprint 054 will
   ship `Candidates/V49.lean` at `c_value = 1779/5000 = 0.3558`
   using sprint 053's oracle re-pointed at the new `c` (one
   `[[oracles]]` field edit, no Lean infrastructure change).
   Expected `axioms_used = {seed} ∪ {hEq15_oracle_certified_3558}`,
   `score = 1779/5000 > 1777/5000`, **first c-push above the seed
   in 54 sprints**.

### Planner ultrathink — three candidate sprint shapes considered

**C1 (chosen) — Register the bulletin-prescribed parametric `eq15`
oracle wrapper, ship V48 at the seed.**
- *Strongest objection*: V48 ties V47 at `1777/5000`, and the
  bulletin's first 2026-05-02 directive explicitly says tying V0 is
  no longer a win. *Resolution*: the bulletin's second directive of
  the same day (lines 263–272) explicitly authorises this exact
  no-c-push wrapper sprint as the prerequisite for the cascade and
  calls it "a successful sprint" (line 295). The two directives
  are consistent: tying V0 with **no trust-base change** is not a
  win; tying V0 with the **trust-base re-shaped through a
  pre-approved channel that immediately enables a per-sprint
  cascade** is the explicit work the bulletin prescribes.
- *Why this is novel*: it is the workspace's first use of the
  `[[oracles]]` registration mechanism; the first non-trivial
  `Numerical_Library` wrapper that is consumed by the Evaluator;
  and the first candidate whose `axioms_used` set excludes the
  literal seed `hEq15_seed_3554` and contains an oracle-backed
  axiom name instead. Five sprints (048–052) have failed to do
  this; sprint 053 unblocks the cascade.

**C2 — Combine the wrapper + the first c-push into one sprint
(target `c = 1779/5000` directly).**
- *Strongest objection*: this stacks two structural changes
  (oracle-wrapper registration AND a candidate at a new `c`) into
  one Generator session. If the wrapper has any wiring issue
  (lemma.toml `lean_axiom` field path, evaluator hookup,
  `flint.arb` / `mpmath` precision envelope), the c-pushing
  candidate fails for the wrong reason and the post-mortem cannot
  cleanly separate "the oracle channel works" from "the
  inequality holds at `0.3558`". Bulletin lines 295–298 explicitly
  say "aim for the closest verified step, not the limit"; the
  closest verified step from the current state is the wrapper
  sprint, not a c-push sprint.
- *Demoted*. C1 first; C2's content is sprint 054's work.

**C3 — File a `proposal_003` for a third trust expansion (e.g.,
adding a Mathlib lemma family to `[workspace_import_policy]` or
extending `KorenblumPaper.PaperAxioms`).**
- *Strongest objection*: we are already at 2/3 pending proposals
  (`proposal_001`, `proposal_002`), and the
  `AGENT_BRIEF.md` §"Numerical tooling" makes the oracle path
  explicitly **pre-approved without proposals**. Filing a third
  proposal when concrete pre-approved work is available (C1) is
  exactly the failure mode the bulletin's second directive
  criticizes ("filed proposals, did not use the pre-approved
  oracle slot"). Sprints 048–052 are already a textbook example.
- *Demoted*. C3 should only be considered after C1 has been
  executed and the cascade has converged on a c-ceiling that
  cannot be lifted by oracle-only means.

**Verdict.** C1 is the bulletin's literal prescription, ships a
Lean candidate (breaks the 5-sprint paper-only streak), uses
exclusively the pre-approved channel (no third proposal needed),
and is structurally distinct from both `proposal_001` (paper-side
cross-coupling, Shape A) and `proposal_002` (per-`k` series
oracle): all three target genuinely different analytical chains
(`(15)` direct vs. paper.eq4 cross-coupling vs. sprint 045
per-`k` reducer). C1 directly stages the next 3–4 incremental
c-pushes (`0.3556 → 0.3558 → 0.3560 → 0.3562`) per the
bulletin-supplied `mpmath dps=50, N_TRUNC=200` margin table.

## Concrete edits expected

1. **`ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`**:
   add a new top-level function

   ```python
   def certify_eq15(
       c_num: int,
       c_den: int,
       *,
       dps: int = 50,
       n_trunc: int = 200,
   ) -> bool:
       """
       Returns True iff Wang's equation (15)
           1 ≤ ∫_{c..branchSplit c} 12·ρ^3·(ρ^2 - c^2) / (c^6 · Λ(c, ρ)) dρ
              + ∫_{branchSplit c..1}  4·ρ^3 / (c^4 · Λ(c, ρ)) dρ
       can be certified at c = c_num/c_den under verified-interval
       arithmetic with `dps` digits of mpmath precision and at most
       `n_trunc` factors retained per `K`-product evaluation.

       The Λ envelope is taken from this module's existing
       lambda_upper_on_interval / _inv_lambda_lower_from_k_upper_fraction
       infrastructure (validated at module import); both branch
       integrals are evaluated as adaptive `flint.arb` boxes whose
       lower envelope is summed and compared to `1` strictly. The
       function returns `True` iff the certified lower bound on the
       sum is `≥ 1 + 10^(-min(dps, 30))`; otherwise returns `False`
       (and is expected to log the certified midpoint and radius for
       diagnosis).
       """
       ...
   ```

   The implementation is a verified-interval rigorous lower bound on the
   `Korenblum.scalarCriterion` two-integral sum at the requested rational
   `c`. The body composes the existing module functions (no new
   `flint.arb` primitives needed) and returns `True` iff the lower
   envelope strictly exceeds `1`. At `(c_num, c_den) = (3554, 10000)`
   the function MUST return `True` — this is the seed and is the cell
   sprint 050's `mpmath dps=50, N_TRUNC=200` reverification confirmed
   has `gap = +2.55e-02` (well above the `10^(-30)` strict-margin
   threshold).

2. **`ProofRefinement/Korenblum/lemma.toml`**: append the registration
   block

   ```toml
   [[oracles]]
   name = "eq15_certified_at_seed"
   module = "ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar"
   function = "certify_eq15"
   args = { c_num = 3554, c_den = 10000, dps = 50, n_trunc = 200 }
   lean_axiom = "ProofRefinement.Korenblum.Candidates.V48.hEq15_oracle_certified_3554"
   ```

   immediately after the existing `[seed_axioms]` block. Also append
   `"hEq15_oracle_certified_3554"` to the `[seed_axioms].allowed`
   list. **Do not remove the existing `"hEq15_seed_3554"` entry** —
   prior candidates V0–V47 still rely on it for the literal seed
   axiom path; removing it would break the V0 cone retroactively.

3. **`ProofRefinement/Korenblum/Candidates/V48.lean`**: new file with
   shape

   ```lean
   -- @parent V47
   import ProofRefinement.Korenblum.Proof.Main

   noncomputable section

   namespace ProofRefinement.Korenblum.Candidates.V48

   open ProofRefinement.Korenblum
   open ProofRefinement.Korenblum.ProblemAxioms

   /-- Wang 2025's published lower-bound radius. Unchanged from V0. -/
   def c_value : ℝ := 3554 / 10000

   theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value]
   theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value]

   /--
   Oracle-backed external input: Wang's equation `(15)` at `c = 0.3554`,
   discharged by the registered oracle
   `eq15_certified_at_seed` whose wrapper is
   `Numerical_Library.rigorous_scalar.certify_eq15` at
   `(c_num, c_den, dps, n_trunc) = (3554, 10000, 50, 200)`.
   -/
   axiom hEq15_oracle_certified_3554 (K : ℝ → ℝ → ℝ) :
     PaperAxioms.Eq15ScalarBound K c_value

   /--
   First workspace candidate whose `(15)` premise is routed through the
   `[[oracles]]`-registered wrapper instead of the literal seed axiom.
   `c_value` ties V0/V47 at `3554/10000`; this sprint deliberately does
   not push `c` (per the bulletin's 2026-05-02 second directive).
   -/
   theorem korenblum_constant_search : ValidKorenblumBound c_value := by
     exact valid_of_eq15 c_value_pos c_value_lt_one
       (fun {K} => hEq15_oracle_certified_3554 K)

   end ProofRefinement.Korenblum.Candidates.V48
   ```

   Conventions match V0 / V44 byte-for-byte except for the axiom name.

4. **`ProofRefinement/Korenblum/Bulletin.md`**: append exactly one line
   to the recent-events block:

   ```text
   sprint_053 PASS: registered parametric `eq15` oracle wrapper via Numerical_Library.rigorous_scalar.certify_eq15 — V48 ties V47 at 1777/5000 but axioms_used switches from {seed} ∪ {hEq15_seed_3554} to {seed} ∪ {hEq15_oracle_certified_3554}, unblocking per-sprint c-push cascade (3554 → 3558 → 3560 → 3562 per sprint 050 mpmath gap table) without further `Proposals/` filing or `[workspace_import_policy]` expansion
   ```

   on success, or the matching `BLOCKED` line on failure. Do not reflow.

5. **`ProofRefinement/Korenblum/Experience.md`**: append a new dated entry
   `### 2026-05-02 sprint_053` summarising:
   - what the bulletin's second 2026-05-02 directive prescribed;
   - that this is the first sprint to use the `[[oracles]]` channel;
   - the `certify_eq15` wrapper's verified-interval implementation and
     the `dps=50, N_TRUNC=200` envelope (matching sprint 050's
     reverification);
   - the explicit `axioms_used` change for V48 vs V47;
   - the next-sprint plan (sprint 054 → V49 at `c = 1779/5000` by
     re-pointing the oracle's `args = { c_num = 1779, c_den = 5000, … }`
     and shipping a parallel candidate; no Lean infrastructure
     change needed);
   - that this sprint does NOT touch `proposal_001` or
     `proposal_002` (their `Status:` fields remain `pending`); the
     `[[oracles]]` channel is structurally orthogonal to both.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V48` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V48.lean` succeeds.
3. The evaluator report logs `pass: true`, `score: 1777/5000`, and
   `axioms_used` containing exactly the seed Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`) **plus** the new oracle-backed axiom name
   `ProofRefinement.Korenblum.Candidates.V48.hEq15_oracle_certified_3554`
   — and crucially **does not contain** `hEq15_seed_3554`. Greppable on
   the JSONL log entry for V48: `axioms_used` array should list
   `hEq15_oracle_certified_3554` (with the V48 namespace prefix) and
   should NOT list `hEq15_seed_3554`.
4. The Evaluator's oracle-checks block records that the
   `eq15_certified_at_seed` oracle was invoked and returned `True` —
   visible in the JSONL `oracle_checks` array (currently empty for all
   prior candidates).
5. `python3 -c "from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import certify_eq15; assert certify_eq15(3554, 10000, dps=50, n_trunc=200), 'wrapper rejected the seed'"` from the workspace root returns exit code 0 — i.e. the wrapper independently confirms `(15)` at the seed under the registered envelope.
6. `python3 -c "from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import certify_eq15; assert not certify_eq15(3565, 10000, dps=50, n_trunc=200), 'wrapper falsely certified above the (15) crossover'"` from the workspace root returns exit code 0 — i.e. the wrapper correctly rejects `c = 0.3565`, where sprint 050's `Scratch/sprint_050_eq15_crossover_pinpoint.txt` reports `gap = -3.598e-04`. This is the falsifiability check that the wrapper isn't trivially returning `True`.
7. `git diff --stat` shows changes only to:
   - `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
     (one new function),
   - `ProofRefinement/Korenblum/lemma.toml` (one new `[[oracles]]`
     block, one append to `[seed_axioms].allowed`),
   - `ProofRefinement/Korenblum/Candidates/V48.lean` (new file),
   - `ProofRefinement/Korenblum/Bulletin.md` (one appended line),
   - `ProofRefinement/Korenblum/Experience.md` (one appended entry).
   No edits to `Proof/Reduction.lean`, `Proof/Main.lean`,
   `Proof/CandidateContract.lean`, `KorenblumPaper/`, or any prior
   `Candidates/V<n>.lean`. No new `Proposals/` file.

## Out of scope

- Push `c_value` above `1777/5000`. That is sprint 054's job. This
  sprint deliberately ties V47 to verify the oracle channel works in
  isolation. (Sprint 054 will re-point the oracle's `args` block at
  `c_num = 1779, c_den = 5000` and ship V49 in a separate Generator
  session; the work cleanly separates and the failure modes do not
  interfere.)
- Modify `proposal_001` or `proposal_002`'s `Status:` fields. Both
  remain `pending`. The oracle channel registered here is
  structurally orthogonal to both proposals (different reducer route:
  `valid_of_eq15` instead of sprint 045's
  `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`,
  and different paper-side input: literal `(15)` instead of per-`k`
  series).
- Add any new Lean theorem to `Reduction.lean`, `Main.lean`, or any
  module under `KorenblumPaper/`. The oracle wrapper sits entirely in
  `Numerical_Library/`; the Lean side gets exactly one new `axiom`
  declaration in `Candidates/V48.lean`.
- File a third proposal. We are at 2/3 pending and the
  `[[oracles]]` channel is pre-approved per `AGENT_BRIEF.md`
  §"Numerical tooling".
- Remove or alter the existing `hEq15_seed_3554` axiom or the
  existing `[seed_axioms].allowed` entry for it. Prior candidates
  V0–V47 still rely on it; removing it would retroactively break
  the V0 cone.
- Generalise the oracle wrapper to a parametric `(c : ℚ)` Lean axiom.
  Per the bulletin's second directive (lines 237–242), the oracle
  IS parametric in `c` *at the wrapper level* (via the `args` block
  in `lemma.toml`), but each Lean-facing axiom remains pinned to a
  specific `c` (mirroring `hEq15_seed_3554`'s shape). Sprint 054
  declares a *new* axiom `hEq15_oracle_certified_3558` rather than
  re-using sprint 053's at a different `c` — keeping each axiom
  paper-faithful at one specific value, and keeping
  `axioms_used` greppably tied to the candidate's claimed
  `c_value`.

## Time budget

≤ 60 minutes runtime. Breakdown:

- ~15 min: implement `certify_eq15` in `rigorous_scalar.py`,
  composing existing `lambda_upper_on_interval` /
  `_inv_lambda_lower_from_k_upper_fraction` /
  `_arb_box` / `_pow_cached` infrastructure into a verified
  lower bound on the two-branch integral sum and a strict
  comparison with `1`. The body is at most ~80 lines.
- ~5 min: smoke-test `certify_eq15(3554, 10000)` returns `True`
  and `certify_eq15(3565, 10000)` returns `False` (acceptance
  criteria 5 and 6).
- ~5 min: append the `[[oracles]]` block and `seed_axioms.allowed`
  entry in `lemma.toml`.
- ~10 min: write `Candidates/V48.lean` (essentially V0 with the
  axiom name swapped) and `lake build` it.
- ~10 min: run the evaluator and verify the JSONL log shows the
  oracle-check fired and `axioms_used` excludes
  `hEq15_seed_3554`.
- ~10 min: append the `Bulletin.md` line and the `Experience.md`
  entry; verify `git diff --stat` matches acceptance criterion 7.
- ~5 min: buffer for a `ring`-style Lean compile fix on V48 if
  the namespace path needs minor adjustment.

## Stop conditions

- Acceptance criteria 1–7 all met: `STATUS=READY_FOR_EVALUATION`.
- `certify_eq15` cannot reproduce sprint 050's positive-margin
  result at the seed under the registered envelope (criterion 5
  fails): `STATUS=BLOCKED` with note "wrapper falsified at seed
  under `dps=50, n_trunc=200`; either the precision envelope is
  too tight or sprint 050's mpmath result has been
  misinterpreted; investigate before re-queuing". Do **not** ship
  V48 with a wrapper that fails its own acceptance test — that
  would land an oracle-backed axiom asserting a numerically
  unverified claim.
- `certify_eq15` returns `True` at `c = 0.3565`
  (criterion 6 fails): `STATUS=BLOCKED` with note "wrapper
  insufficiently rigorous; returns True past the verified
  crossover at `c ∈ (0.3560, 0.3565)`". This is a critical
  rigour failure (wrapper would later authorise a numerically
  false c-push) and must be fixed before this sprint lands.
- The `[[oracles]]`-registration mechanism in the
  Evaluator does not actually invoke wrappers from
  `Numerical_Library/`, contrary to the bulletin's claim
  (`AGENT_BRIEF.md` §"Numerical tooling" and the bulletin's
  second directive both assert it does): `STATUS=BLOCKED_NEEDS_HUMAN`
  with note "the harness's `[[oracles]]` mechanism is not as
  documented; please confirm whether the Evaluator wires
  registered wrappers or whether `[[oracles]]` is purely
  documentary". This would represent a documentation/wiring
  mismatch that needs human disambiguation, **not** a third
  `Proposals/` filing.
- Lean compile failure on V48 from a unforeseen interaction
  between `axiom hEq15_oracle_certified_3554` and the
  `valid_of_eq15` reducer's `∀ {K}, …` quantifier scope:
  `STATUS=BLOCKED` with diagnostic. This is unlikely (the
  axiom shape mirrors `hEq15_seed_3554` byte-for-byte modulo
  the name), but flagged as a known low-probability failure
  mode.

## Notes for the Generator

* **The wrapper must be honestly verified, not faked.** The whole
  point of moving from `hEq15_seed_3554` to
  `hEq15_oracle_certified_3554` is to ground the trust in a
  named, version-pinned Python verifier rather than a
  per-`c` free-floating axiom (per bulletin lines 237–253). A
  wrapper that returns `True` without rigorous verification is
  worse than the seed axiom — it claims rigour it doesn't have.
  Use `flint.arb` interval arithmetic throughout; do not fall
  back to `mpmath.mpf` floating-point comparisons except for
  the final `> 1 + ε` comparison on the certified lower
  envelope.

* **The wrapper's signature accepts a rational `c` as
  `(c_num, c_den)`, NOT a float.** `mpmath`'s
  `c = mp.mpf("0.3554")` introduces a binary-vs-decimal
  rounding error that breaks rigour at the few-`ulp` level.
  Use `Fraction(c_num, c_den)` and the existing
  `_arb_exact(Fraction(c_num, c_den))` / `_arb_box(lo, hi)`
  helpers (already in the module) to keep the rationality
  exact through the certification.

* **Acceptance criterion 6 is a load-bearing falsifiability
  check.** A wrapper that returns `True` for *both* `c = 0.3554`
  and `c = 0.3565` is not actually verifying anything — it's
  a constant function. Sprint 050's
  `Scratch/sprint_050_eq15_crossover_pinpoint.txt`
  established that the literal `(15)` kernel collapses inside
  `c ∈ (0.3560, 0.3565)`; the wrapper must reflect this
  collapse. If criterion 6 fails, do not ship; fix the
  wrapper.

* **`axioms_used` greppability matters.** The Evaluator's
  axiom-extraction step (per `AGENT_BRIEF.md` and the
  Refinement_Log JSONL schema) lists each axiom with its full
  namespace path. Acceptance criterion 3 requires the literal
  string `"hEq15_oracle_certified_3554"` to appear and
  `"hEq15_seed_3554"` to not appear. Use the exact axiom
  name; do not abbreviate or reuse a generic
  `hEq15_oracle_certified` name across multiple `c`-values
  (sprint 054 will use `hEq15_oracle_certified_3558`, etc.).

* **The bulletin's directive vs. the planner's instinct.**
  Five sprints (048–052) read the bulletin's first directive
  ("structural novelty is no longer a win") and concluded that
  the path forward is more structural exploration in
  `Scratch/` and `Proposals/`. The bulletin's second directive
  of the same day (issued *because* of those five sprints'
  failure mode) explicitly inverts that reading: the path
  forward is the `[[oracles]]` channel, which the previous
  five sprints did not touch. Sprint 053 is the corrective
  action. If the Generator finds itself tempted to file
  another `Proposals/` entry or write more `Scratch/`
  scripts, **stop** and re-read bulletin lines 219–313 — the
  prescribed work is concrete, narrow, and pre-approved.

* **No retroactive edit to V0–V47.** The existing
  candidates rely on `hEq15_seed_3554`. They continue to
  evaluate-pass with that axiom in `[seed_axioms].allowed`.
  Do not remove the seed-axiom entry; do not edit any
  prior candidate. V48 is a sibling of V0, not a
  replacement.

* **Confirmation that this sprint can be a win.** Per the
  bulletin's clarification (line 295), "A sprint that pushes
  `c` from `0.3556` to `0.3558` with a comfortable margin
  and an axiom-set that does not grow is **a successful
  sprint**". V48 does not push `c`, so on a strict reading
  it is not a "successful sprint" by that line — but it IS
  the prerequisite that the next sprint cannot exist
  without, and the bulletin's second directive (lines
  263–272) explicitly authorises this exact ties-V47 wrapper
  sprint as Sprint 052's prescribed plan. The PASS row in
  the bulletin is honest: V48 ties V47 at the score level,
  but the trust-surface change is the deliverable, not the
  score.
