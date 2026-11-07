# Sprint 058: File `proposal_003` for paper-side per-`k` cross-coupling enrichment to break the literal `(15)` crossover at `c ≈ 0.35635`, plus a single Scratch HP probe at `c = 35645/100000` to definitively pin the HP envelope's ceiling

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V51.lean` (the third c-pushed candidate, sprint 057, `c = 1782/5000 = 0.3564`, HP envelope `(dps=100, n_trunc=500)`, margin +1.17e-3)
**Target file**: *(no new candidate this sprint — preparatory; see "Justification for the c-tie" below)*
**Direction**: oracle-support / proposal-filing — preparatory for a c-push past the literal Wang `(15)` mathematical crossover at `c ≈ 0.35635`

## Goal

(a) File a new `Proposals/proposal_003_<slug>.md` requesting a paper-side
enrichment of `KorenblumPaper.PaperAxioms` that exposes a per-`k`
cross-coupling actually present in Wang 2025 (i.e. with a verified paper
citation, not the false citation that sank `proposal_001`), addressing all
five "Required to resubmit" criteria from
`proposal_001`'s rejection log lines 333–391; and (b) record one
single Scratch run of the HP envelope at `c = 35645/100000 = 0.35645`
to definitively measure whether the HP wrapper still has any headroom
between V51's `c = 0.3564` and the literal `(15)` crossover at `c ≈ 0.35635`.

**No Lean files are edited this sprint.** No new `Candidates/V*.lean`,
no `Reduction.lean` change, no `lemma.toml` change, no new
`Numerical_Library/` function. The deliverable is a proposal file, a
Scratch script, and an Experience.md entry.

## Justification for the c-tie (Bulletin.md lines 27–31)

The Bulletin's primary directive states: *"Sprints that tie V0's `c` —
no matter how structurally novel — are no longer wins; they are at best
preparatory and must explicitly justify why they cannot be folded into
a single c-pushing sprint."* This sprint ties V51's `c = 1782/5000` and
must therefore justify the tie. The justification is:

1. **The literal Wang `(15)` crossover at `c ≈ 0.35635` is a mathematical
   wall, not a numerical one.** Sprint 050's `mpmath dps=50, N_TRUNC=200`
   pinpoint (`Scratch/sprint_050_eq15_crossover_pinpoint.txt`) shows the
   `(15)` integral inequality holds with margin ≥ +1e-3 at `c = 0.3560`
   and fails at `c = 0.3565` (gap −3.598e-04). Sprint 057's HP envelope
   (`dps=100, n_trunc=500`) reproduces the same falsifiability boundary
   (HP at c=0.3565 rejects with margin −1.15e-3, HP at c=0.3566 rejects
   with margin −3.46e-3). The HP envelope's role is to certify the
   ground-truth gap conservatively; it cannot certify a gap that does
   not exist. Past `c ≈ 0.35635` the inequality is FALSE on the Wang
   `(15)` route.

2. **No further precision-envelope upgrade is pre-authorised.**
   Bulletin.md lines 300–304: *"a sixth sprint that re-verifies
   `c ∈ {0.3563, 0.3564, 0.3565}` at `mpmath dps=100, N=500` and either
   certifies one of them (next increment) or confirms the cliff and
   routes to `proposal_001`"* — only this single upgrade is pre-authorised,
   and sprint 057 has now consumed it. A further upgrade (e.g.
   `dps=200, n_trunc=1000`) is not pre-authorised; per the user's
   framing ("the empirical HP-tier falsifiability at 0.3565 suggests
   the bottleneck is mathematics, not precision"), it would also not
   help — the cliff is real, not an artefact of envelope conservatism.

3. **All four closed-form / finite-mode-extremal kernels in the workspace
   are dead.** Sprint 048's `c⁴` window (sprint 014's reducer) falsifies
   already at the seed; sprint 048's `c⁴/2` branch-2 window
   (sprint 017's reducer) goes negative at every `c ∈ {0.36, …, 0.50}`;
   sprint 049's literal `(15)` reducer goes strictly negative for every
   `c ∈ {0.36, 0.37, …, 0.50}`; sprint 051's per-`k` series kernel
   (sprint 045's reducer) under canonical trivial extremals E0–E3
   yields no `(family, c, α²)` triple with `c > 0.3554` and margin
   ≥ 1e-3. All four are exhaustively confirmed-blocked above the
   crossover.

4. **No in-scope c-push remains without paper-side enrichment.** Routes
   1 (finer denominators at HP), 2 (proposal pivot), and 3 (further
   precision upgrades) were all named in the user's framing of this
   planning step. Per (1)–(3) above, route 1 has at most ~+0.00005 of
   c headroom remaining (between V51's 0.3564 and the crossover
   ~0.35635), at the cost of one identically-shaped sprint per +0.00005
   step; route 3 is unavailable. Only route 2 — paper-side
   cross-coupling enrichment — can break the c≈0.35635 wall.
   Route 2 cannot be folded into a single c-pushing sprint
   because it requires (i) Alan's approval of a new paper-axiom
   expansion, (ii) the proposal must address all five "Required
   to resubmit" criteria from `proposal_001`'s rejection rationale
   lines 333–391, including verified-Wang2025 citation and an
   infinite-mode-adversary feasibility witness, and (iii) the
   eventual c-push sprint depends on the new axiom existing in
   `KorenblumPaper.PaperAxioms`. The proposal-filing step and the
   c-push step are necessarily two sprints minimum.

5. **The Scratch HP probe at `c = 0.35645` is an anti-blind-spot
   check, not a c-push attempt.** Linear extrapolation of the HP
   slope `−2.31e-3 per +0.0001` puts HP margin at `c = 0.35645`
   at `+1.17e-3 + (1/2)(−2.31e-3) ≈ +0.0e-3` — essentially zero,
   right at the HP cliff. If the probe somehow accepts (slope
   non-linear in our favour), the next planner can ship at
   `c = 35645/100000` in sprint 059 as a +0.00005 increment;
   if the probe rejects (most likely outcome), the next planner
   has definitive evidence that V51's c is the HP envelope's
   absolute ceiling and must wait on `proposal_003`'s approval.
   Either way the data feeds the next planner and the proposal
   filing's evidence base. **This sprint does not ship a Lean
   candidate at `c = 0.35645`** — even if HP accepts, that's a
   sprint 059 task with its own oracle row and shim. This sprint
   only generates the Scratch evidence.

This justification is concrete, not aspirational. The sprint is
preparatory in the precise sense the Bulletin allows: it produces
a proposal that, when approved by Alan, becomes a structural
prerequisite for the next genuine c-push. Without proposal_003
or a successor, the workspace is stuck at V51's c = 1782/5000
indefinitely.

## Why

### Planner's enumeration of candidate sprint shapes (ultrathink)

Per the planner-agent directive, I considered three structurally
distinct candidate sprint shapes that pursue *different analytical
chains*, then chose by expected analytical novelty per
bounded-Generator-session of work.

**C1 — Finer-denominator HP probe and c-push at `c = 35645/100000 = 0.35645`
(if accepts) or `c = 35640/100000` (if 35645 rejects).** A +0.00005 or
+0.00000 step at HP, ships a new Lean candidate V52 if the wrapper
accepts, with axiom `hEq15_oracle_certified_hp_35645` and a new
`[[oracles]]` row pinning HP at the finer-denominator `c`. Mirrors
the sprint 057 shape with a finer-denominator probe.
**Strongest objection (decisive):** the user's own framing in this
planning step explicitly doubts route 1: *"the margin is collapsing
fast: linear extrapolation predicts the next +0.0001 step (to
c = 0.3565) is already negative. Finer-than-+0.0001 increments may
not be worth a full sprint each."* Linear extrapolation of the HP
slope across (0.3564, 0.3566) puts HP margin at 0.35645 at ≈+0.0e-3
(essentially zero); this is a coin-flip wrapper acceptance for at
most +0.00005 of c. Even if it lands, the *next* sprint at
`c = 0.35650` would face the same conservatism wall but worse, and
the literal `(15)` crossover at ~0.35635 caps any further push
mathematically. The cascade has fundamentally hit a *mathematical*
ceiling that no envelope tightening can move; spending another
full Generator session squeezing 5e-5 out of conservatism residue
is a low-yield repeat of the sprint 056/057 pattern with no novel
analytical content. Demoted to "Scratch-only data-collection step
embedded in C5".

**C2 — Pivot to a different closing reducer, e.g. sprint 045's per-`k`
series kernel.** Try to ship V52 via `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9`
(sprint 045's reducer) instead of `valid_of_eq15`. The kernel
shape is `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`, structurally
distinct from `(15)`. **Strongest objection (decisive):** sprint 051's
exhaustive sweep over canonical trivial extremals E0–E3 already
confirmed this kernel falsifies (NEGATIVE result, no `(family, c, α²)`
triple with `c > 0.3554` and margin ≥ 1e-3). Worse, the kernel is
*existentially quantified over `(a, b)` adversaries*, not a
closed-form scalar inequality — there is no `[[oracles]]` shim that
can certify it at the verified-interval level without paper-side
cross-mode coupling not currently exposed by `Section2Assumptions`
(this is exactly the obstruction `proposal_002` documented and Alan
deferred). Demoted: this analytical chain is mature evidence-blocked,
not a fresh route.

**C3 — Sprint 014/017's full-window or branch-2 kernel reducer at
some smaller `c`.** Ship V52 via a structurally distinct closing
reducer at, e.g., `c = 0.30` to validate the workspace's *other*
reducers in an axiom-set the V51 cascade has not exercised, even
though `c = 0.30 < 0.3554` does not push the score. **Strongest
objection (decisive):** the score must report `c > 1782/5000`, not
`< seed`, to count as a win. A sprint at smaller `c` ties at most
the structurally-novel-axiom-set bar and would itself be a tie-or-worse
sprint; per Bulletin lines 27–31, that is also disallowed unless
preparatory. And the closed-form sufficiency conditions (sprint 048's
sweep of sprint 014/017 at `c ∈ {0.3554, 0.36, …, 0.50}`) show
those reducers' kernels are *negative* across that range; they
also do not unlock c-push without paper-side enrichment. Demoted:
no novel analytical chain materialises at any `c`.

**C4 — File `proposal_003` for paper-side per-`k` cross-coupling
enrichment, addressing all 5 "Required to resubmit" criteria from
`proposal_001`'s rejection log lines 333–391, with infinite-mode
feasibility evidence.** Pure proposal-filing sprint with mandatory
Scratch evidence demonstrating an infinite-mode adversary the
proposed bound dominates (criterion 4 from the rejection log). No
Lean files touched. **Strongest objection:** ties V51's c. But (i)
the tie is justified per "Justification for the c-tie" §1–4 above,
(ii) the work cannot be folded into a c-push sprint because Alan's
approval is a precondition, (iii) and the analytical novelty per
Generator-session is high — for the first time in 7 sprints, a
sprint produces a *paper-side* artefact (a proposal citing actual
Wang 2025 content with a paper-faithful Lean axiom signature),
rather than another `[[oracles]]` shim. The Bulletin's secondary
directive (lines 27–31) explicitly carves out preparatory sprints
under exactly this condition. Promoted to **CHOSEN**, augmented
with the C1-derived Scratch HP probe at `c = 0.35645` as
data-collection (no Lean candidate).

**C5 (chosen) = C4 + (one HP Scratch probe at `c = 0.35645` for
data collection only).** Adds the C1-style anti-blind-spot HP probe
to verify the cascade's HP ceiling matches the slope extrapolation
prediction. If the probe unexpectedly accepts (slope non-linear
favourably), the next planner can ship at the finer denominator in
sprint 059; if it rejects (predicted), the proposal becomes the
only forward route and Alan's approval is the next blocker.

**Verdict.** C5 strictly dominates C1 (C1's HP probe is a sub-task of
C5; C5 also files the proposal C1 cannot), strictly dominates C2
(C2's analytical chain is mature evidence-blocked per sprint 051),
and strictly dominates C3 (C3 ties or worse at smaller c with no
novel axiom-set). C5 is the only candidate that produces genuine
analytical novelty in this sprint (a paper-faithful proposal with
verified citations and infinite-mode feasibility evidence), and
also produces clean data for the next planner regardless of how
proposal_003 fares.

### What success looks like

- `Proposals/proposal_003_<slug>.md` exists with `Status: pending`
  and addresses all 5 "Required to resubmit" criteria from
  `proposal_001`'s rejection log lines 333–391 verbatim:
  1. Cite paper.eq4 accurately (paper.eq4 = bulk
     `Σ⁺(r) ≤ Σ⁺(c) ∧ Σ⁺(c) ≤ Σ⁻(c) ∧ Σ⁻(c) = c²·Z_c`,
     not a per-`k` coupling) and propose the *separate* paper-axiom
     expansion the per-`k` coupling needs, with **explicit Wang 2025
     PDF page/equation citation** (use the local
     `ProofRefinement/Korenblum/Wang2025.pdf` /
     `Wang2025.txt` to find the actual per-`k` analytical step Wang
     uses; do not invent one);
  2. Write the kernel inequality literally — both the existing
     sprint 045 kernel that the new axiom would tighten, and the
     proposed tightened form, both with `(a, b)` and `(c, ρ₁, ρ₂)`
     parameters explicit;
  3. Specify the proposed Lean axiom's exact statement (verbatim Lean
     `axiom` declaration, with the correct types per
     `KorenblumPaper.PaperAxioms`'s actual surface — see Notes for
     Generator below for the relevant definition lines);
  4. **Show pointwise feasibility before approval** via a `Scratch/`
     script demonstrating the proposed bound holds at the target
     `c` against at least one *infinite-mode* adversary (e.g. a
     Hayman extremal generating function, or any explicit
     analytic family beyond sprint 051's E0–E3 finite-mode set)
     with margin ≥ 1e-3;
  5. Decide between routes openly: explicitly state the proposal
     requests a paper-axiom expansion (highest trust cost; requires
     paper citation) — *not* a free-floating analytic axiom and
     *not* an oracle entry. The choice between these three was
     mixed in `proposal_001`; the resubmission must commit.
- `Scratch/sprint_058_proposal_003_feasibility_witness.{py,txt}`
  contains the infinite-mode adversary script and its margin output
  (criterion 4's evidence).
- `Scratch/sprint_058_hp_envelope_ceiling_at_35645.{py,txt}` contains
  one HP probe at `c = 35645/100000` and the regression checks
  (HP at c=0.3564 must still accept ≥ +1e-3, HP at c=0.3565 must
  still reject), recording whether HP unexpectedly accepts above V51.
- `Experience.md` has a new sprint_058 entry following the post-2026-05-02
  honest-reporting format (what was attempted, including dead ends;
  current obstacle to `c > 0.3564`; numerical exploration done with
  the HP probe's measured margin; next planner's options conditional
  on Alan's verdict on proposal_003).
- The Bulletin gains the standard `sprint_058 PASS: …` entry plus a
  one-line `note:` summarising the HP probe's outcome.
- **No new Lean candidate is shipped.** `score` is unchanged from
  V51's `1782/5000`. The win is a paper-faithful proposal that
  Alan can reasonably approve (unlike `proposal_001`/`proposal_002`)
  and an Experience.md entry that gives the next planner a
  definitive forward path.

## Concrete edits expected

### Phase A — Wang 2025 paper read (Generator, ~10 minutes)

Read `ProofRefinement/Korenblum/Wang2025.pdf` (and/or
`ProofRefinement/Korenblum/Wang2025.txt` if PDF rendering is
problematic) to identify:

- The actual per-`k` analytical step that drives Wang's Section 2
  proof of the `(15)` scalar inequality. The current
  `Eq4SigmaPlusBound` in `KorenblumPaper/PaperAxioms.lean`
  (lines 132–137; do not edit this file) bundles three bulk
  scalar conjuncts but does not expose a per-`k` inequality.
  Wang's proof must (somewhere) work term-by-term to derive the
  bulk bound; the proposal needs to identify exactly where.
- The relevant page numbers, equation numbers, and lemma numbers
  in Wang 2025 (cite verbatim).
- The minimal Lean axiom signature that would expose this step
  to the workspace, written against the *actual* types and
  definitions in `KorenblumPaper.PaperAxioms` (e.g.
  `coeffPlusGap : (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℝ` from line 42,
  *not* the `(c, ρ)`-dependent form `proposal_001` invented).

If Wang 2025 has no obvious per-`k` step that would tighten the
`(15)` ceiling, the proposal must say so honestly and pivot to
the alternative paper-side route (the `Σ⁺(c) ≤ Σ⁻(c)` bulk
inequality is paper.eq4's second conjunct — investigate whether
*that* conjunct admits a `c`-dependent shrinkage `θ(c) < 1` such
that `Σ⁺(c) ≤ θ(c) · Σ⁻(c)`, paper-derivable from Wang Section 2;
if yes, propose that as the paper-axiom expansion).

### Phase B — Scratch infinite-mode feasibility witness (Generator, ~15 minutes)

Write `ProofRefinement/Korenblum/Scratch/sprint_058_proposal_003_feasibility_witness.py`
that:

1. Defines at least one *infinite-mode* adversary `(a, b)`
   beyond sprint 051's four canonical trivial extremals E0–E3.
   Concrete suggestions (Generator chooses one or more):
   - **Hayman extremal**: `a_k = α^k`, `b_k = β·γ^k` with
     `(α, β, γ)` chosen so `Section2Assumptions a b K c` holds
     at the target `c` (i.e. L²-summable with `‖a‖² + ‖b‖² = 1`,
     `circleGap a b r ≥ 0` on `[0, 1)`, etc.).
   - **Geometric tail with finite head**: `a_k` and `b_k`
     non-zero on `k ∈ {0, 1, 2}` and decaying geometrically
     for `k ≥ 3`.
   - **Wang Section 2's own optimisation candidate** if the
     paper sketches one explicitly.
2. Numerically verifies (using `mpmath dps=50` and explicit
   tail truncation at `K_trunc = 200`) that the proposed
   tightened paper-side bound (whatever it ends up being)
   holds at the target `c` against this adversary with margin
   ≥ `1e-3`.
3. Outputs to
   `Scratch/sprint_058_proposal_003_feasibility_witness.txt`
   in the standard sprint-048-shaped table format (one row
   per `(adversary, c, parameters)`, columns: LHS, RHS, gap,
   margin).
4. If no infinite-mode adversary clears the +1e-3 margin
   bar, the script must record this honestly and the
   proposal must downgrade its `c` target accordingly (or
   pivot to the bulk-side `Σ⁺(c) ≤ θ(c) · Σ⁻(c)` shrinkage
   route per Phase A's fallback).

### Phase C — Scratch HP envelope ceiling probe at c = 0.35645 (Generator, ~5 minutes)

Write `ProofRefinement/Korenblum/Scratch/sprint_058_hp_envelope_ceiling_at_35645.py`
that:

1. Imports `certify_eq15` from
   `ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar`.
2. Probes `certify_eq15(35645, 100000, dps=100, n_trunc=500)` —
   single HP call at the finer-denominator c.
3. Runs two regression checks at HP envelope:
   - `certify_eq15(1782, 5000, dps=100, n_trunc=500)` must return
     `True` (V51's HP win, must still hold);
   - `certify_eq15(3565, 10000, dps=100, n_trunc=500)` must return
     `False` (HP-tier falsifiability at the literal `(15)`
     crossover, must still hold).
4. Outputs to `Scratch/sprint_058_hp_envelope_ceiling_at_35645.txt`
   with the wrapper outcomes and the inline-replay margins (copy
   sprint 057's helper verbatim from
   `Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`).
5. The script's exit code is `0` regardless of acceptance —
   this is data collection, not a c-push attempt. Do NOT
   ship a Lean candidate at `c = 35645/100000` even if HP
   accepts; that is a sprint 059 task with its own contract.

### Phase D — Proposal file (Generator, ~20 minutes)

Write `ProofRefinement/Korenblum/Proposals/proposal_003_<slug>.md`
following the structure of
`Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`
and `Proposals/proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`,
with the following sections (slug to be chosen by the Generator
based on the actual paper-side step identified in Phase A; e.g.
`proposal_003_paper_side_per_k_cross_coupling_for_c_push_past_eq15_crossover.md`):

- **What's needed**: file paths, Lean surface, config changes.
- **Mathematical content**: cite Wang 2025 page/equation
  verbatim per Phase A; write the kernel inequality literally
  per criterion 2; specify the Lean axiom signature per
  criterion 3.
- **Pointwise feasibility evidence**: link to
  `Scratch/sprint_058_proposal_003_feasibility_witness.txt`
  per criterion 4.
- **Route choice**: paper-axiom expansion (commit to one of
  the three routes per criterion 5; do NOT mix Shape A /
  Shape B / oracle).
- **Win unlocked**: state the concrete `c_value` target
  (must be > V51's `1782/5000` to be useful), the
  axiom-set after approval, the follow-up sprint outline
  (planner / generator / evaluator steps).
- **Risk / trust cost**: paper-axiom expansion's review
  burden; what Alan would have to verify against the cited
  Wang 2025 page.
- **Status log**: dated `created by Planner (sprint 058)`,
  `Status: pending`.

The proposal MUST acknowledge `proposal_001`'s rejection
explicitly in its preamble (not as a status log entry — as
a top-level "Predecessor proposal" section) and explain how
the resubmission addresses each of the 5 "Required to
resubmit" criteria one-by-one. Reviewers should be able to
verify the resubmission criteria are met by reading the
proposal alone.

### Phase E — Experience.md and Bulletin entries (Generator, ~5 minutes)

Append a sprint_058 entry to `Experience.md` following the
post-2026-05-02 honest-reporting format documented in
Bulletin.md lines 126–145:

- **What was attempted, including dead ends.** State which
  Wang 2025 pages were read; what per-`k` step was found (or
  not found); what infinite-mode adversaries were tried in
  Phase B; whether the HP probe at `c = 0.35645` accepted.
- **What is the current obstacle to `c > 0.3564`?** Name it
  explicitly (probably: Alan's verdict on proposal_003,
  combined with the literal `(15)` crossover at
  `c ≈ 0.35635` capping any further `(15)`-route push).
- **What numerical exploration was done.** Cite the two new
  Scratch scripts and their margins.
- **What is the next move.** Conditional on Alan's verdict:
  if proposal_003 is approved, sprint 059 implements the
  paper-side axiom and discharges sprint 045's reducer's
  kernel cell at the target `c`; if rejected, sprint 059
  is another proposal-filing sprint with the rejection
  feedback incorporated; if HP unexpectedly accepted at
  `c = 0.35645`, sprint 059 ships V52 at the finer
  denominator (a +0.00005 cascade step) while
  proposal_003 is in review.
- **What would unblock a c-push faster.** Even if no
  proposal is filed this sprint, name what would help.

Append a Bulletin row:

```text
sprint_058 PASS: filed proposal_003 (paper-side per-k cross-coupling per Wang 2025 §<page>), HP probe at c=35645/100000=0.35645 <accepted/rejected> with margin <X>; preparatory sprint per Bulletin lines 27–31, no Lean candidate shipped, score unchanged at 1782/5000=V51 (justification for c-tie in sprint 058 contract §"Justification for the c-tie")
note: <one-line summary of HP probe outcome and proposal_003's central paper citation>
```

If Phase A finds Wang 2025 has no clear per-`k` step that
would tighten the `(15)` ceiling AND Phase B's infinite-mode
adversary fails to clear +1e-3, the proposal becomes
substantively weak; the Generator should then BLOCK with
`STATUS=BLOCKED_NEEDS_HUMAN` per the stop conditions
below, and Bulletin/Experience.md entries should reflect
the BLOCKED status honestly.

## Acceptance criteria

This sprint produces no new Lean candidate. Acceptance is
measured against the sprint's preparatory deliverables.

1. `Proposals/proposal_003_<slug>.md` exists with
   `Status: pending`, slug chosen by the Generator to
   reflect the actual paper-side step identified in Phase A.
2. The proposal addresses all 5 "Required to resubmit"
   criteria from `proposal_001`'s rejection log lines
   333–391 explicitly and verifiably (criterion 1: cited
   Wang 2025 page/equation; criterion 2: kernel inequality
   written literally; criterion 3: Lean axiom statement
   verbatim; criterion 4: feasibility evidence linked;
   criterion 5: single-route choice committed).
3. `Scratch/sprint_058_proposal_003_feasibility_witness.py`
   exists, runs to completion under
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 ProofRefinement/Korenblum/Scratch/sprint_058_proposal_003_feasibility_witness.py`,
   and its `.txt` output records the infinite-mode
   adversary's measured margin (criterion 4's evidence).
4. `Scratch/sprint_058_hp_envelope_ceiling_at_35645.py`
   exists, runs to completion under the same `uv run`
   command, and its `.txt` output records the HP wrapper's
   acceptance/rejection at `c = 35645/100000 = 0.35645`
   plus the two HP regression checks. Both regression
   checks (HP at 0.3564 accept, HP at 0.3565 reject) must
   hold; if either fails, exit non-zero.
5. `Experience.md` has a new sprint_058 entry following
   the post-2026-05-02 honest-reporting format (Bulletin
   lines 126–145). The entry MUST include:
   (a) the list of Wang 2025 pages read,
   (b) the central paper citation chosen for proposal_003,
   (c) the HP probe's outcome at `c = 0.35645` with
       measured margin,
   (d) the next planner's three-way conditional on Alan's
       verdict (approve / reject / silent within 1 week).
6. `Bulletin.md` has the standard `sprint_058 PASS: …`
   row and a one-line `note:` summary.
7. **No file under `KorenblumPaper/`,
   `ProofRefinement/Korenblum/Proof/`,
   `ProofRefinement/Korenblum/Candidates/`,
   `ProofRefinement/Korenblum/Numerical_Library/`,
   or `ProofRefinement/Korenblum/lemma.toml` is edited.**
   This is a strict structural guarantee — the sprint is
   a paper-side proposal-filing sprint, not a Lean / oracle
   sprint.
8. **The proposal's central paper citation must be
   verifiable against `Wang2025.pdf` / `Wang2025.txt`
   contents.** A planner reading the cited page in Wang
   2025 must be able to identify the proposed paper-side
   step. Inventing or paraphrasing without a verifiable
   citation is a hard fail (the same failure mode that
   sank `proposal_001`).

## Out of scope

- Any edit to `Candidates/V51.lean` or any prior `V*.lean`
  candidate file.
- Any new entry in `lemma.toml:[[oracles]]` or
  `lemma.toml:[seed_axioms].allowed`.
- Any new function in `Numerical_Library/` (the existing
  `rigorous_scalar.certify_eq15` is reused as-is for the
  HP probe; no new wrappers).
- Any new theorem in `Proof/Reduction.lean` or sibling
  files.
- Any change to `KorenblumPaper/` files (proposal_003
  *requests* such a change but does not perform it; that
  is sprint 059+ work pending Alan's approval).
- Shipping a Lean candidate at `c = 35645/100000` even if
  the HP probe accepts (that is a sprint 059 task; this
  sprint's HP probe is data collection only).
- Probing additional HP `c` values beyond 0.35645 (the
  cliff is already pinned by sprint 057's HP table; one
  finer-denominator probe is sufficient anti-blind-spot
  evidence).
- Filing a second proposal_004 simultaneously (one
  proposal per sprint; per `Proposals/README.md` the
  pending limit is 3, currently 1 pending after proposal_001's
  rejection — proposal_002 is deferred not pending — so
  proposal_003 fits within the cap).

## Time budget

≤ 60 minutes runtime for the Generator session.

Estimated breakdown:

- Phase A (Wang 2025 read): ~10 minutes
- Phase B (infinite-mode Scratch): ~15 minutes
- Phase C (HP probe Scratch): ~5 minutes (HP call ~5 min
  wall-clock per call; one call here)
- Phase D (proposal write): ~20 minutes
- Phase E (Experience + Bulletin): ~5 minutes
- Slack: ~5 minutes

Wall-clock dominated by Phase C's single HP call (~5 min)
and Phase A's PDF read.

## Stop conditions

- **All 8 acceptance criteria met**: `STATUS=READY_FOR_EVALUATION`.
  (No Lean candidate to evaluate this sprint, but the
  preparatory deliverables are complete and the Refinement
  Log row should be written by the harness as a
  `pass: true` no-candidate row, or — if the harness
  requires a Lean candidate to log — by appending a
  `pass: true, score: null, notes: "preparatory sprint per
  Bulletin lines 27–31"` row manually per the harness's
  conventions for proposal-filing sprints.)
- **Wang 2025 yields no clear per-`k` step that would
  tighten the `(15)` ceiling AND no infinite-mode adversary
  clears +1e-3**: `STATUS=BLOCKED_NEEDS_HUMAN`. The
  proposal can still be filed (with downgraded claims
  acknowledging the analytical gap) but Alan must decide
  whether to approve a weaker paper-axiom expansion or
  reject and request a different route.
- **HP probe at `c = 35645/100000` unexpectedly accepts**:
  proceed normally; record the margin in the Scratch
  output and Experience.md; the next planner can ship
  V52 at the finer denominator in sprint 059. **Do not
  ship V52 in this sprint** — the contract's purpose is
  proposal-filing, not c-push.
- **HP regression check fails (HP at 0.3564 rejects, or
  HP at 0.3565 accepts)**: `STATUS=BLOCKED_NEEDS_HUMAN`.
  This indicates an environment / wrapper drift between
  sprint 057 and sprint 058 that must be diagnosed before
  any further oracle work. Halt all Lean and proposal
  work; the Bulletin entry must flag this prominently
  for the next planner.
- **Generator cannot write the proposal because Wang
  2025's actual analytical step is more involved than a
  single Lean axiom can capture (e.g. requires a new
  `Section2Assumptions`-companion structure)**:
  `STATUS=BLOCKED_NEEDS_HUMAN` — the proposal pivot
  exceeds the sprint's scope and Alan must scope the
  paper-axiom expansion at a higher level before
  proposal_003 can be filed responsibly.

## Notes for the Generator

1. **Read `Wang2025.pdf` / `Wang2025.txt` carefully in Phase A.**
   The single most-cited reason `proposal_001` was rejected
   is its false citation of `paper.eq4` as a per-`k`
   coupling. Do not repeat that mistake. If `Wang2025.txt`
   is more searchable than the PDF, prefer it; quote the
   exact sentence(s) from Wang in the proposal.
2. **Do not invent paper content.** If Wang 2025's
   Section 2 proof of `(15)` does not have a per-`k`
   refinement that would help, say so honestly and pivot
   the proposal to the bulk-side `Σ⁺(c) ≤ θ(c) · Σ⁻(c)`
   shrinkage route (paper.eq4's second conjunct relaxed
   with a `c`-dependent factor). Wang Section 2 may have
   a closed-form formula for `θ(c)` that gives the
   shrinkage we need.
3. **The HP probe in Phase C reuses sprint 057's helper
   verbatim.** Copy the inline-replay function from
   `Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`
   into the new script; do NOT use `build_adaptive_certificate`
   (Experience.md sprint_056 documents this pattern).
4. **The `Eq4SigmaPlusBound` definition in
   `KorenblumPaper/PaperAxioms.lean`** is at lines 132–137.
   The Generator may briefly read this file to verify the
   exact bulk shape (`Σ⁺(r) ≤ Σ⁺(c) ∧ Σ⁺(c) ≤ Σ⁻(c) ∧ Σ⁻(c) = c²·Z_c`)
   so the proposal's "Predecessor proposal" section
   correctly states what paper.eq4 actually is. This is a
   read-only reference, not an edit.
5. **`coeffPlusGap`, `coeffMinusGap`, `n1Pred`, `n2Pred`,
   `sigmaPlus`, `sigmaMinus`, `sigmaZeroMinus` definitions**
   are in `KorenblumPaper/PaperAxioms.lean` lines 34–82.
   Reference these in the proposed Lean axiom signature
   per criterion 3. The Generator may read these
   definitions but must not edit them.
6. **Sprint 045's reducer
   `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9`**
   is in `Proof/Reduction.lean` lines 6927–6990 (per
   `proposal_002`'s reference). The Generator may read
   this to confirm the kernel cell signature the new
   axiom would discharge (or — better — propose the new
   axiom in a form that discharges a *different*,
   structurally simpler reducer's kernel cell, e.g.
   `valid_of_eq15` itself with a tightened `(15)` form
   that holds past `c ≈ 0.35635`).
7. **Proposal status conventions.** Per
   `Proposals/README.md`, the `Status:` field is one of
   `pending` / `approved` / `rejected` / `superseded`.
   The Generator MUST set proposal_003's `Status:` to
   `pending` and MUST NOT edit `proposal_001`'s or
   `proposal_002`'s `Status:` autonomously.
8. **One sprint, one proposal.** Even if Phase A
   identifies multiple plausible paper-side enrichment
   routes, the Generator should commit to one in
   proposal_003 and note the alternatives in a
   "Considered alternatives" subsection, not file
   multiple proposals in the same sprint.
9. **The Bulletin's pending-proposal cap is 3** (per
   `Proposals/README.md`). Currently: proposal_001
   (rejected), proposal_002 (pending but deferred — do
   not edit). proposal_003 will be the second pending
   entry, well within cap.
10. **If Phase C's HP probe takes longer than 10 minutes
    to return**, kill it and proceed with Phase D using
    the slope-extrapolation prediction (margin ≈ +0.0e-3
    at HP) as the recorded outcome. Note in the Scratch
    `.txt` that the call timed out and the sprint
    proceeded with the predicted value. The HP probe is
    anti-blind-spot evidence, not a load-bearing
    deliverable; the proposal is the load-bearing
    deliverable.
