# Sprint 051: Scratch sweep of sprint 045's per-`k` series kernel under canonical trivial extremal `(a, b)` sequences

**Created**: 2026-05-02 by Planner
**Parent candidate**: *(none — fourth roadmap/Scratch-only sprint in a row; the latest evaluator-passing candidate remains `Candidates/V47.lean`)*
**Target file**: *(none — this sprint produces no Lean candidate)*
**Direction**: roadmap (Scratch evidence on the only structurally-distinct kernel family that sprint 050 explicitly demoted as "not closed-form numerical")

## Goal

Test whether **sprint 045's per-`k` series kernel** has positive headroom above
the seed `c = 0.3554` under any **canonical trivial extremal** `(a, b)`
sequence — i.e. an `(a, b)` choice with finite support and `O(1)`-many
non-zero modes, computable by hand. The kernel is

> `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³ · Z_ρ / Λ(c, ρ) dρ`

with

> `Σ⁺_int(c) := Σ'_{k ∈ N1} coeffPlusGap_k(a,b) · c^(2k+2)/(k+1)`,
> `Z_ρ := sigmaZeroMinus(a, b, ρ) = Σ'_{k ∈ N2} coeffMinusGap_k(a,b) · ρ^(2k-2)`,
> `N1 = {k = 0} ∪ {k : ‖a_k‖ ≥ ‖b_k‖}`,
> `N2 = {k > 0 : ‖a_k‖ < ‖b_k‖}`,
> `coeffPlusGap_k = ‖a_k‖² − ‖b_k‖²`,
> `coeffMinusGap_k = ‖b_k‖² − ‖a_k‖²`.

**This is the kernel that sprint 050's enumeration table explicitly demoted
as "depends on `(a, b)`; NOT closed-form numerical".** It is also the only
remaining structurally-distinct candidate kernel for any future `c > 0.3554`
push without a paper-side trust expansion (sprint 040's mixed `c²·Σ⁺(c) ≤ ∫…`
is the only sibling and is dominated for the same reason — both LHS shapes
are `(a, b)`-dependent). Since the kernel is `(a, b)`-dependent, "tested
numerically" requires committing to a *specific* `(a, b)` family. Sprint 050
ruled out *Hayman-extremal* `(a, b)` sequences as research-level. This sprint
covers the strictly weaker, bounded test case: **canonical trivial
extremals**, listed below.

This sprint produces:

1. A `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.py` script
   that evaluates LHS and RHS of sprint 045's kernel at each
   `(extremal-family, c)` pair on a small grid;
2. A `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
   captured-stdout file with the sweep table;
3. A new bullet appended to `Proposals/proposal_001_…md`'s `## Status log`
   summarising the per-`k` numerical evidence and stating concretely
   whether sprint 045's per-`k` route still has any numerical headroom
   above the seed under any canonical trivial extremal;
4. A decision tree (in this contract's "Why" section, materialised by the
   Generator into `Experience.md`) for the next sprint:
   - **If at least one canonical trivial extremal yields LHS ≤ RHS at some
     `c > 0.3554` with margin ≥ `1e-3`:** the next sprint should ship a
     Lean candidate using sprint 045's reducer instantiated at the
     witnessed `(a, b, c)`, pushing `c_value` directly. (Hard subcase:
     the witness `(a, b)` may force the workspace's `Section2Assumptions`
     to be discharged by hand at that `(a, b)` rather than using
     `valid_of_eq15`. The Generator must verify that `Section2Assumptions
     a b K c` is constructible at the witness — this may require an
     additional small Lean lemma but is bounded.)
   - **If no canonical trivial extremal yields a positive margin:** the
     workspace is exhaustively confirmed-blocked on every kernel reachable
     from existing `Reduction.lean` reducers without a trust-base
     expansion. The next sprint must file `proposal_002`, narrowing
     `proposal_001` Shape B to a precise oracle signature for a
     numerically-sharp upper bound on `Σ⁺_int(c)` (or alternatively
     filing a paper-side proposal for the missing analytical machinery).

**This sprint produces no Lean theorem.** It does not add a new candidate.
It does not register a new oracle. It does not modify `proposal_001`'s
`Status:` field. It does not file a new proposal. The workspace remains
`BLOCKED_NEEDS_HUMAN` on `proposal_001` after this sprint.

## Why

### What sprint 050 said about this kernel

Sprint 050's enumeration table (in its "Why" section) explicitly excluded
sprint 045's per-`k` series kernel from numerical testing:

> sprint 045 — `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ` (per-`k` series) —
> depends on `(a_k, b_k)`; **NOT closed-form numerical**; explicitly named
> in `proposal_001` Shape B as the route requiring the per-`k` numerical
> oracle.

And in its "Out of scope" section:

> Test the per-`k` series kernel under an explicit extremal `(a, b)`
> sequence. The planner considered this candidate (proposal_001 Shape
> B's testing under e.g. a Hayman-extremal sequence) but concluded it
> exceeds a single bounded-Generator-session budget — selecting,
> computing, and validating an extremal sequence is a research move.

Sprint 050's exclusion is correct **for Hayman-extremal sequences** — those
are genuinely research-level and require selecting an analytically-extremal
`(a_k, b_k)` from a continuum of possibilities. But the exclusion is
**too strong** for a much weaker test: enumerating all `(a, b)` with
support inside `{k = 0, 1, 2}` and `‖a‖² + ‖b‖² = 1`, evaluating the
kernel at each, and reporting the result. This is bounded — finitely
many extremals × small `c` grid × two integrals each — and falsifiable
in one Generator session.

### The four canonical trivial extremals

Per the structural definitions of `N1` / `N2` / `coeffPlusGap` /
`coeffMinusGap` / `sigmaZeroMinus` in `KorenblumPaper.PaperAxioms`
(lines 33–77), the canonical trivial extremals are:

| Name | `(a_k, b_k)` (only non-zeros) | `N1` content | `N2` content | `Σ⁺_int(c)` | `Z_ρ` |
|---|---|---|---|---|---|
| **E0 (one-mode k=0, a-only)** | `a_0 = 1` | `{0}` | `{}` | `1·c²/1 = c²` | `0` |
| **E1 (one-mode k=1, b-only)** | `b_1 = 1` | `{0}` (with `coeffPlusGap_0 = 0`) | `{1}` | `0` | `1·ρ⁰ = 1` |
| **E2 (two-mode k=0/k=1)** | `a_0 = α, b_1 = β`, `α²+β²=1` | `{0}` | `{1}` | `α²·c²` | `β²` (constant in `ρ`) |
| **E3 (two-mode k=0/k=2)** | `a_0 = α, b_2 = β`, `α²+β²=1` | `{0}` | `{2}` | `α²·c²` | `β²·ρ²` |

These four families (with the optimal `(α, β)` pair for E2 and E3)
**exhaust** the bounded-support case of three or fewer modes. Higher-mode
extremals (e.g. `b_3` only, or `a_0/b_1/b_2`) reduce to the same RHS
shapes by the same algebra and are dominated.

Each family's kernel inequality is **a closed-form numerical inequality
in `(c, ρ₁, ρ₂, α)`** — no `(a, b)` adversary remains to optimise over,
because the family is fully specified and the `(α, β)` slider is the
only continuous parameter (which can be optimised analytically per
family).

### What the kernel says for each family

Plugging into `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³ · Z_ρ / Λ(c, ρ) dρ`:

* **E0 (a_0 = 1):** `c² ≤ ∫_{ρ₁..ρ₂} 0/Λ dρ = 0`. **Falsifies for every c > 0.**
  Trivially negative — the unit-mass-on-`a_0` family produces no
  `Z_ρ` and no annulus contribution. No headroom.
* **E1 (b_1 = 1):** `0 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ dρ`. Holds trivially for every
  `c`, but the LHS is degenerate (zero), so it does not certify any
  `c > 0`.  This is mathematically a void witness: a `Section2Assumptions`
  built from `b_1 = 1` only would have `circleGap = -ρ²·1 < 0`, so the
  `ValidKorenblumBound c` notion is actually about whether `circleGap ≥ 0`
  in the disk, which fails for E1; sprint 045's reducer cannot be
  invoked here.
* **E2 (a_0 = α, b_1 = β):** `α²·c² ≤ β² · ∫_{ρ₁..ρ₂} 2ρ³/Λ dρ`. With
  `α²+β² = 1` and `α² = 1 − t, β² = t`, this becomes
  `(1−t)c² ≤ t · J(c)` where `J(c) := ∫ 2ρ³/Λ`. Solving:
  `t ≥ c² / (c² + J(c))`. Maximum slider `t = 1` (β = 1, α = 0) gives
  `0 ≤ J(c)`, trivially holds — same void as E1. The interesting
  edge is `α = 1` (E0): falsifies. Worth checking the explicit
  `t = c² / (c² + J(c))` slider — at `c = 0.3554`,
  `J(c) ≈ 0.0163` (sprint 048's value), so `t ≈ 0.126/(0.126+0.0163) ≈ 0.886`,
  meaning `α² ≈ 0.114, β² ≈ 0.886`. The witness has 88.6% of its
  L²-mass on `b_1` and only 11.4% on `a_0`. **The script verifies
  whether this slider works at the seed, then sweeps `c` upward to
  find the largest `c` where the slider still yields a non-trivial
  witness.**
* **E3 (a_0 = α, b_2 = β):** `α²·c² ≤ β² · ∫_{ρ₁..ρ₂} 2ρ⁵/Λ dρ`. With
  `α²+β² = 1`, slider `t = α² ∈ [0, 1]`, and `J₅(c) := ∫ 2ρ⁵/Λ`,
  the same algebra gives `t ≥ c² / (c² + J₅(c))`. **The script
  verifies whether this slider works at the seed and sweeps upward.**

### Why this is concretely worth one session

Either:

* **Some E2 or E3 slider succeeds at the seed and can push `c > 0.3554`.**
  The script reports the largest `c` with positive margin under the
  optimal slider, and the next sprint ships a Lean candidate using
  sprint 045's reducer at that `(a, b, c)`. This *would* be the first
  workspace candidate to push `c_value` above `0.3554`. (Caveat: the
  `Section2Assumptions a b K c` premise must be discharged at the
  specific `(a, b)`. The `valid_of_eq15` route is dead per sprint 049,
  but `Section2Assumptions` is *not* `valid_of_eq15` — it is the
  bundle of axiom hypotheses `eq2`, `eq3`, `eq4`, `eq8`, `eq9`, …
  available as ordinary `paper.eq*` field projections from the
  paper-axiom side. For trivial-extremal `(a, b)`, these hypotheses
  may be discharged by direct computation in Lean rather than by
  invoking `(15)`. This is the central uncertainty for the follow-up
  sprint, not for this sprint.)
* **No E2 or E3 slider succeeds at any `c ≥ 0.3554`.** Then the
  workspace is exhaustively confirmed-blocked on every kernel reachable
  from `Reduction.lean` without a paper-side trust expansion. The
  natural escalation is `proposal_002`, narrowing `proposal_001` Shape
  B from "register `coeff_plus_gap_k_upper`" to a specific oracle
  signature `bound_sigma_plus_int_at_c(c) → Φ` certifying
  `sup_{a,b: ‖a‖²+‖b‖²=1} Σ⁺_int(c)(a,b) ≤ Φ(c)` along with the
  claim that the sup is attained on a finite-mode family (which the
  E0–E3 sweep informs). The next-sprint Planner files `proposal_002`
  with concrete numerical targets read off this sprint's table.

Either branch is an unambiguous outcome that closes the open question
left by sprint 050. The brief asks for "a *fourth* numerical kernel
candidate that hasn't been tested yet" or "a tighter `proposal_002`".
This sprint executes exactly the first option (a fourth, structurally-
distinct kernel family — sprint 045's per-`k` series under canonical
trivial extremals) and pre-stages the second (proposal_002) as the
fallback if the first yields negative.

### Planner ultrathink — three candidate sprint shapes considered

1. **C1 — Yet another Scratch sweep over a closed-form scalar kernel
   family.** Rejected: sprint 050's enumeration table is exhaustive.
   Every closed-form `(c, ρ)`-only kernel in `Reduction.lean` reduces
   to one of sprint 014's `c⁴`, sprint 017's `c⁴/2`, or sprint 049's
   literal `(15)`. All three are falsified at `mpmath dps=50`. There
   is genuinely no untested closed-form scalar kernel.
2. **C2 — File `proposal_002` immediately, narrowing `proposal_001`
   Shape B.** Rejected: `proposal_002` filed without per-`k` Scratch
   evidence would be no more concrete than `proposal_001`'s Shape B
   already is. The bulletin's "Scratch-first then Lean" rule extends
   to "Scratch-first then proposal" — without numerical evidence
   that *some* per-`k` route has any headroom, a proposal asking for
   an oracle to certify a per-`k` bound is filed in a vacuum.
3. **C3 (chosen) — Scratch sweep of sprint 045's per-`k` series kernel
   under canonical trivial extremals (E0–E3).** Bounded (4 extremal
   families × 1 c-grid × 2 integrals each = 16 numerical experiments),
   falsifiable (positive-margin or not), structurally novel (first
   workspace test of sprint 045's kernel at any explicit `(a, b)`),
   and produces the evidence needed for either the c-push (if
   positive) or `proposal_002` (if negative).

Strongest objection to C3: sprint 050 said this exceeds a single
Generator session. **Resolution:** sprint 050 was about *Hayman-extremal*
sequences, which require analytical optimisation over an infinite-
dimensional space. C3 is about *trivial* extremals — single-mode and
two-mode `(a, b)` with `≤ 3` non-zero coefficients, where the optimal
`(α, β)` slider is one analytical step (Lagrange multiplier on
`α²+β² = 1`) rather than a research-grade calculus-of-variations
problem. C3's Scratch script is `~120 lines` of mpmath, equivalent in
complexity to sprint 050's. Bounded.

## Concrete edits expected

This sprint produces **no Lean edits**. Deliverables:

- `ProofRefinement/Korenblum/Sprint_Contracts/sprint_051_scratch_per_k_series_kernel_canonical_extremals.md`:
  this contract (created by the Planner — already in place when this
  contract is materialised).
- `ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.py`:
  `mpmath`-based (`dps = 50`, `N_TRUNC = 200`) script that, for each
  of the four canonical trivial extremal families E0–E3:
  1. Computes the LHS `Σ⁺_int(c)(a, b)` (closed-form per family).
  2. Computes the RHS `∫_{c+ε..1−ε} 2ρ³ · Z_ρ(a, b, ρ) / Λ(c, ρ) dρ`
     via `mpmath.quad` (the same machinery sprint 050 uses).
  3. For families E2 and E3, sweeps the slider `α² ∈ [0, 1]` on a fine
     grid (e.g. step `0.01`) at each `c` and reports the optimum
     slider position and the resulting margin.
  4. Sweeps `c ∈ {0.3554, 0.36, 0.37, 0.38, 0.40, 0.42, 0.45, 0.50}`
     for each family, printing a table with columns
     `family, c, optimal_alpha_sq, LHS, RHS, gap = RHS − LHS`.
  5. Includes the same self-spot-check on `Λ(0.3554, 0.5)` and
     `Λ(0.4, 0.6)` that sprint 050 uses, to confirm `K`/`Λ`
     reproducibility.
  6. Prints a clearly-labelled bottom-line summary line of one of
     the two forms:
     - `RESULT: per-k kernel POSITIVE under family <E2/E3> at c = <value> with optimal α²=<value>, gap = <value>`
       (when at least one family/`c` pair clears the gap-target threshold);
     - `RESULT: per-k kernel NEGATIVE for all canonical trivial extremals at all c >= 0.3554 (max gap = <value> at family <name>, c = <value>, α² = <value>)`
       (otherwise).
  7. Caps `α² ∈ {0.0, 0.05, 0.1, 0.15, 0.2, 0.25, …, 1.0}` (21 grid points)
     to keep wall-clock bounded. The optimal slider position derivable
     analytically (`α² = c² / (c² + J(c))` per the "Why" section) should
     be added as an additional explicit grid point per `c`, to ensure
     the analytical optimum is captured.
- `ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`:
  captured stdout of the above script.
- `ProofRefinement/Korenblum/Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`:
  append to the `## Status log` section a new dated bullet summarising
  the canonical-trivial-extremal sweep outcome (no change to `Status:`
  field — stays `pending`). The bullet must be ≤ 12 lines and must
  state explicitly:
  - whether any `(family, c, α²)` point produced `gap ≥ 1e-3`,
  - the maximum gap observed,
  - one sentence on the implication for `proposal_001` Shape B
    (does the per-`k` route still have any numerical headroom under
    a finite-mode family?).
- `ProofRefinement/Korenblum/Experience.md`: append a new dated entry
  under `### 2026-05-02 sprint_051` summarising:
  - which extremal families were tested and the outcome per family,
  - the bottom-line result (positive or negative),
  - the next-sprint decision tree (per "If positive / if negative" in
    the Goal section),
  - the current obstacle to `c > 0.3554`,
  - what trust expansion would unblock a c-push faster (concrete
    answer based on the sweep result).
- **No changes to any `.lean` file** under `ProofRefinement/Korenblum/`
  or `KorenblumPaper/`.
- **No changes to `lemma.toml`.**
- **No new `Candidates/V*.lean` file.**
- **No new proposal file.** Specifically: this sprint does *not* file
  `proposal_002`. If the sweep result calls for `proposal_002`, the
  Generator notes this in the `Experience.md` entry as a directive for
  the next planner; the next sprint's Planner files it with concrete
  numerical targets read off this sprint's table.
- **No edits to `Bulletin.md`** beyond appending a new
  `sprint_051 BLOCKED_NEEDS_HUMAN: …` recent-events line.

## Acceptance criteria

1. `ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.py`
   exists and runs to completion as
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run --with mpmath python3 ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.py`
   with no uncaught exceptions.
2. `ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
   exists and contains the script's printed sweep table covering all
   four extremal families (E0–E3) at the standard `c` grid
   `{0.3554, 0.36, 0.37, 0.38, 0.40, 0.42, 0.45, 0.50}`. Each row
   shall include columns: `family`, `c`, `α²` (or `n/a` for one-mode
   families), `LHS = Σ⁺_int(c)`, `RHS = ∫ 2ρ³·Z_ρ/Λ`, `gap = RHS − LHS`.
3. The script's stdout shall contain the bottom-line summary line
   matching one of the two `RESULT: …` forms specified in
   "Concrete edits expected" item 6 above.
4. The `mpmath` script shall use `mp.mp.dps = 50` and `N_TRUNC = 200`
   (matching sprint 050's precision discipline).
5. The script shall include the self-spot-check at
   `(c, ρ) = (0.3554, 0.5)` and `(c, ρ) = (0.4, 0.6)` confirming
   `Λ(0.3554, 0.5) ≈ 3.475322e+01` and `Λ(0.4, 0.6) ≈ 5.596185e+01`
   to within relative tolerance `1e-12`.
6. After running the script, **append a new bullet to the `## Status
   log` section of `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`**
   summarising the outcome per "Concrete edits expected" item 4.
   The bullet shall not modify `proposal_001`'s `Status:` field.
7. **Append a new `### 2026-05-02 sprint_051` entry to
   `ProofRefinement/Korenblum/Experience.md`** per "Concrete edits
   expected" item 5 above.
8. **Append a new `sprint_051 BLOCKED_NEEDS_HUMAN: …` line to
   `ProofRefinement/Korenblum/Bulletin.md`'s recent-events block**,
   using the same one-line format as sprints 048/049/050.
9. **No new Lean theorems are added.** Greppable check: the diff for
   sprint 051 contains zero changes to any `.lean` file under
   `ProofRefinement/Korenblum/` or `KorenblumPaper/`.
10. **No edits to `lemma.toml`.** Greppable check: the diff contains
    zero changes to `ProofRefinement/Korenblum/lemma.toml`.
11. **No new `Candidates/V*.lean` file.** Greppable check: the diff
    contains no `Candidates/V51.lean` or any other new candidate file.
12. **No new proposal file.** Greppable check: the diff contains zero
    new files under `ProofRefinement/Korenblum/Proposals/` (only an
    in-place edit to the existing `proposal_001` is permitted).

## Out of scope

- Add any new Lean theorem, definition, or axiom.
- Edit `Reduction.lean`, `Main.lean`, `CandidateContract.lean`, or any
  other `.lean` file in the workspace or in `KorenblumPaper/`.
- Edit `lemma.toml` (no oracle registration; no seed-axiom expansion;
  no import-policy expansion).
- Create `Candidates/V51.lean` or any new candidate file.
- File `proposal_002` or any other new proposal — even if the per-`k`
  sweep result demands it, the *next* sprint's Planner files
  `proposal_002` after reading this sprint's `Experience.md` entry.
  This sprint's role is the evidence; the next sprint's role is the
  proposal (or the candidate, if positive).
- Modify `proposal_001`'s `Status:` field. Only the `## Status log`
  section is appended to.
- Test Hayman-extremal `(a, b)` sequences or any other infinite-mode
  extremal. Only the four canonical trivial extremals E0–E3 are in
  scope. If E0–E3 all fail, the *next* sprint's Planner decides
  whether to file a proposal for an extremal-aware oracle — this
  sprint does not.
- Construct `Section2Assumptions a b K c` for the witness `(a, b)` in
  Lean. That construction is a follow-up sprint task contingent on this
  sprint's outcome being positive.
- Implement an oracle wrapper in `Numerical_Library/`. The mpmath
  Scratch script is exploratory.
- Run the evaluator (`Evaluator.py`) — sprint 051 ships no candidate.
- Sweep `c < 0.3554` (regression-only).
- Cross-test sprint 040's `c²·Σ⁺(c) ≤ ∫ 2ρ³·Z_ρ/Λ` mixed kernel under
  the same extremals. (Reasonable, but the Planner judges that one
  per-`k` family per sprint is the right granularity. If this sprint
  yields positive, the next sprint ships the Lean candidate; if
  negative, the next sprint files `proposal_002`. Sprint 040 testing
  is queueable as a sibling Scratch sprint after this one if needed.)

## Time budget

≤ 60 minutes runtime. Breakdown:

- ~20 min: implement `sprint_051_per_k_series_kernel_canonical_extremals.py`
  (~150 lines — `mpmath`-based `K_truncated`, `Λ`, four extremal-family
  evaluators, slider sweep for E2/E3, table formatting, bottom-line
  summary). Reuse the kernel formulas from sprint 050's
  `sprint_050_mpmath_reverify.py` line-for-line; add the per-family
  `Σ⁺_int` and `Z_ρ` evaluators (each `~5 lines`).
- ~10 min: run it (`mpmath.quad` with 4 families × 8 c-values × ≤ 22
  slider positions = up to 700 integrations; budget ~5–10 min wall-clock).
- ~5 min: read the output, draft the `proposal_001` status-log bullet
  and the `Experience.md` entry.
- ~15 min: write the `Experience.md` entry (the planner brief instructs
  the Generator to be honest about dead ends — this sprint produces
  evidence, not Lean — so the entry must explicitly reflect "what
  was attempted, including dead ends, and what is the next move").
- ~10 min: buffer for `uv` environment setup and `mpmath.quad`
  precision adjustments.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
  (Note: there is no candidate to evaluate this sprint — the
  "READY_FOR_EVALUATION" marker is repurposed as "per-`k` Scratch
  evidence in place; workspace remains BLOCKED on `proposal_001` review
  until human action".)
- Some `(family, c, α²)` triple yields `gap ≥ 1e-3` at `c > 0.3554`:
  `STATUS=BLOCKED_NEEDS_HUMAN` with note in the refinement log that
  "per-`k` series kernel POSITIVE under canonical trivial extremal
  family `<name>` at `c = <value>`; next sprint ships Lean candidate
  using sprint 045's reducer (or files proposal_002 if Section2
  construction at the witness `(a, b)` requires further trust)".
- No `(family, c, α²)` triple yields a positive gap at any `c ≥
  0.3554`: `STATUS=BLOCKED_NEEDS_HUMAN` with note "per-`k` series
  kernel NEGATIVE under all canonical trivial extremals; next
  sprint files `proposal_002` narrowing `proposal_001` Shape B to a
  specific oracle signature for the per-`k` `(a, b)`-supremum bound".
- Script fails to reproduce sprint 050's `Λ` spot-check values:
  `STATUS=BLOCKED` (means the `K`/`Λ` reproduction in this script
  has a bug — investigate before continuing).

### Implementation skeleton

```python
# ProofRefinement/Korenblum/Scratch/sprint_051_per_k_series_kernel_canonical_extremals.py
import mpmath as mp

mp.mp.dps = 50
N_TRUNC = 200
EPS = mp.mpf("1e-3")
GAP_TARGET = mp.mpf("1e-3")

# --- Reuse paperFactor / K_truncated / Lambda from sprint_050_mpmath_reverify.py
def paperFactor(c, rho, n):
    rho2 = rho * rho
    cn   = c ** (2 * n)
    cnp1 = c ** (2 * n + 1)
    cnp2 = c ** (2 * n + 2)
    cnp3 = c ** (2 * n + 3)
    num = (mp.mpf(1) + rho2 * cnp1) * (mp.mpf(1) + cnp3 / rho2) * (mp.mpf(1) + cnp2) ** 2
    den = (mp.mpf(1) + rho2 * cn)   * (mp.mpf(1) + cnp2 / rho2) * (mp.mpf(1) + cnp1) ** 2
    return num / den

def K_truncated(c, rho, N=N_TRUNC):
    prod = mp.mpf(1)
    for n in range(N):
        prod *= paperFactor(c, rho, n)
    return mp.mpf(2) * rho * (mp.mpf(1) + c / (rho * rho)) * prod

def Lambda(c, rho, N=N_TRUNC):
    Kv = K_truncated(c, rho, N)
    Ksq = Kv * Kv
    if not (mp.mpf(0) < Ksq < mp.mpf(1)):
        return mp.inf
    return (mp.mpf(1) + mp.sqrt((mp.mpf(1) + 3 * Ksq) / (mp.mpf(1) - Ksq))) / 2

# --- Per-family LHS (Σ⁺_int(c)) and Z_ρ
# Family E0: a_0 = 1
def lhs_E0(c, alpha_sq=None):
    return c ** 2  # 1 * c^2 / (0+1)

def Z_rho_E0(rho):
    return mp.mpf(0)

# Family E1: b_1 = 1
def lhs_E1(c, alpha_sq=None):
    return mp.mpf(0)  # k=0 in N1 has coeffPlusGap_0 = 0; k=1 in N2 not in Σ⁺_int

def Z_rho_E1(rho):
    return mp.mpf(1)  # |b_1|^2 * rho^(2*1-2) = 1

# Family E2: a_0 = √α_sq, b_1 = √(1−α_sq)
def lhs_E2(c, alpha_sq):
    return alpha_sq * c ** 2

def Z_rho_E2_factory(alpha_sq):
    beta_sq = mp.mpf(1) - alpha_sq
    def Z_rho(rho):
        return beta_sq  # |b_1|^2 * rho^0 = beta_sq
    return Z_rho

# Family E3: a_0 = √α_sq, b_2 = √(1−α_sq)
def lhs_E3(c, alpha_sq):
    return alpha_sq * c ** 2

def Z_rho_E3_factory(alpha_sq):
    beta_sq = mp.mpf(1) - alpha_sq
    def Z_rho(rho):
        return beta_sq * rho ** 2  # |b_2|^2 * rho^(2*2-2) = beta_sq * rho^2
    return Z_rho

# --- RHS evaluator
def rhs_integral(c, Z_rho_fn, eps=EPS):
    rho1 = c + eps
    rho2 = mp.mpf(1) - eps
    integrand = lambda rho: 2 * rho ** 3 * Z_rho_fn(rho) / Lambda(c, rho)
    return mp.quad(integrand, [rho1, rho2])

# --- Spot checks
print("# Spot checks (mpmath dps=50, N_TRUNC=200)")
for (c0, rho0, expected) in [
    (mp.mpf("0.3554"), mp.mpf("0.5"), mp.mpf("3.475322e+01")),
    (mp.mpf("0.4"),    mp.mpf("0.6"), mp.mpf("5.596185e+01")),
]:
    L = Lambda(c0, rho0)
    rel_err = abs(L - expected) / expected
    status = "OK" if rel_err < mp.mpf("1e-7") else "FAIL"
    print(f"#   c={c0} rho={rho0} Lambda={mp.nstr(L, 12)} (sprint050={expected}, rel_err={mp.nstr(rel_err, 4)} -- {status})")
print()

# --- Sweep
cs = [mp.mpf("0.3554"), mp.mpf("0.36"), mp.mpf("0.37"), mp.mpf("0.38"),
      mp.mpf("0.40"),   mp.mpf("0.42"), mp.mpf("0.45"), mp.mpf("0.50")]

# Slider grid (E2, E3): coarse 21-point + analytical optimum per c
coarse_alpha_sq_grid = [mp.mpf(i) / 20 for i in range(21)]

best_overall_gap = mp.mpf("-inf")
best_overall_record = None  # (family, c, alpha_sq, lhs, rhs, gap)

for (fam_name, lhs_fn, Z_rho_factory_or_fn) in [
    ("E0 (a_0=1)",         lhs_E0, Z_rho_E0),
    ("E1 (b_1=1)",         lhs_E1, Z_rho_E1),
    ("E2 (a_0/b_1)",       lhs_E2, "factory"),
    ("E3 (a_0/b_2)",       lhs_E3, "factory"),
]:
    print(f"\n=== Family: {fam_name} ===")
    print(f"{'c':>10} {'alpha_sq':>12} {'LHS':>20} {'RHS':>20} {'gap':>20}")
    print("-" * 88)
    for c in cs:
        if Z_rho_factory_or_fn == "factory":
            # Sweep slider; include analytical optimum t* = c^2 / (c^2 + J(c))
            # where J(c) = ∫ 2ρ³ · (unit Z_ρ) / Λ — first pass at α²=0 to get J(c).
            if fam_name.startswith("E2"):
                Z_unit = Z_rho_E2_factory(mp.mpf(0))
            else:
                Z_unit = Z_rho_E3_factory(mp.mpf(0))
            J_c = rhs_integral(c, Z_unit)
            opt_t = c ** 2 / (c ** 2 + J_c)
            sliders = list(coarse_alpha_sq_grid) + [opt_t]
            best = (None, mp.mpf("-inf"))
            for alpha_sq in sliders:
                if alpha_sq < 0 or alpha_sq > 1:
                    continue
                if fam_name.startswith("E2"):
                    Z = Z_rho_E2_factory(alpha_sq)
                else:
                    Z = Z_rho_E3_factory(alpha_sq)
                lhs = lhs_fn(c, alpha_sq)
                rhs = rhs_integral(c, Z)
                gap = rhs - lhs
                if gap > best[1]:
                    best = (alpha_sq, gap, lhs, rhs)
            alpha_sq, gap, lhs, rhs = best
            print(f"{mp.nstr(c, 6):>10} {mp.nstr(alpha_sq, 6):>12} {mp.nstr(lhs, 12):>20} {mp.nstr(rhs, 12):>20} {mp.nstr(gap, 12):>20}")
        else:
            lhs = lhs_fn(c)
            rhs = rhs_integral(c, Z_rho_factory_or_fn)
            gap = rhs - lhs
            print(f"{mp.nstr(c, 6):>10} {'n/a':>12} {mp.nstr(lhs, 12):>20} {mp.nstr(rhs, 12):>20} {mp.nstr(gap, 12):>20}")
            alpha_sq = None
        if gap > best_overall_gap and c >= mp.mpf("0.3554") + mp.mpf("1e-9"):
            # Strictly above seed
            best_overall_gap = gap
            best_overall_record = (fam_name, c, alpha_sq, lhs, rhs, gap)

print()
print("# ===== Sprint 051 summary =====")
if best_overall_record is not None and best_overall_gap >= GAP_TARGET:
    fam, c, alpha_sq, lhs, rhs, gap = best_overall_record
    print(f"RESULT: per-k kernel POSITIVE under family {fam} at c = {c} with optimal α²={alpha_sq}, gap = {gap}")
elif best_overall_record is not None:
    fam, c, alpha_sq, lhs, rhs, gap = best_overall_record
    print(f"RESULT: per-k kernel NEGATIVE for all canonical trivial extremals at all c >= 0.3554 (max gap = {gap} at family {fam}, c = {c}, α²={alpha_sq})")
else:
    print("RESULT: per-k kernel NEGATIVE for all canonical trivial extremals at all c >= 0.3554 (no positive-gap point found)")
```

### Notes for the Generator

* **Why these four extremal families and not others.** The structural
  definitions of `N1` / `N2` / `coeffPlusGap` / `coeffMinusGap` /
  `sigmaZeroMinus` from `KorenblumPaper.PaperAxioms` (lines 33–77) imply:
  - `Σ⁺_int(c)` only sees `k ∈ N1` with `coeffPlusGap_k ≥ 0`. The
    `k = 0 ∈ N1` term contributes regardless of `‖a_0‖ vs ‖b_0‖`, but
    only its non-negative part `max(0, ‖a_0‖² − ‖b_0‖²)`. So setting
    `b_0 = 0` is WLOG for maximising the LHS contribution from `k = 0`.
  - `Z_ρ = sigmaZeroMinus = Σ_{k ∈ N2} coeffMinusGap_k · ρ^(2k−2)` only
    sees `k > 0` with `‖a_k‖ < ‖b_k‖`. Setting `a_k = 0` for `k > 0`
    is WLOG for maximising RHS contribution from each N2 mode.
  - The four canonical trivial extremals E0–E3 are then the
    finite-support `(a, b)` sequences with at most one N1-active
    mode (k=0) and at most one N2-active mode (k=1 for E1/E2; k=2 for
    E3), modulo the L²-normalisation slider.
  - Higher-mode N2 extremals (e.g. k=3, k=4) are dominated by E3 in
    the sense that they have lower RHS contribution per unit β² mass
    at every `ρ ∈ (c, 1)` (since `ρ^(2k-2)` decreases in `k` when
    `ρ < 1`). So E3 already captures the best two-mode `k=0/N2-only`
    option.

* **Why slider grid `α² ∈ {0, 0.05, …, 1}` plus analytical optimum.**
  The kernel `α²·c² ≤ (1−α²)·J(c)` is linear in `α²`, so the slider
  optimum is at the endpoints `α² = 0` (LHS = 0, trivially holds) or
  `α² = 1` (RHS = 0, trivially fails) — but the *interesting* threshold
  is `α²* = c²/(c² + J(c))`, the slider value where the kernel barely
  closes. Including `α²*` explicitly ensures the script reports the
  *largest non-trivial* slider position; sweeping the coarse grid
  ensures no surprises off the linear curve.

* **Why `gap ≥ 1e-3` rather than `gap > 0`.** Sprint 050 used the same
  `1e-3` margin for the literal `(15)` crossover. Consistency with
  sprint 050 ensures comparability of "positive" verdicts across
  sprints.

* **The "trivial fail at α² = 1" caveat.** For E2 and E3, `α² = 1`
  gives LHS = c² > 0 and RHS = 0 (because β² = 0 zeros out
  `sigmaZeroMinus`), reproducing E0's failure mode. The script
  must filter `α² < 1` for the optimum-slider report (or accept that
  `α² = 1 ⇒ gap < 0` is unsurprising).

* **The "trivial pass at α² = 0" caveat.** For E2 and E3, `α² = 0`
  gives LHS = 0 and RHS > 0, so `gap > 0` trivially holds — but the
  Lean candidate built from this would have `circleGap = -ρ²·sigmaZeroMinus
  < 0` everywhere (since the `a_0` mass that produces the positive
  `coeffPlusGap_0` is now zero), violating the `circleGap ≥ 0`
  precondition `Section2Assumptions` requires (per
  `KorenblumPaper.OneModePaperBridge`'s `circleGap_nonneg_of_eq8_eq9`).
  So a "trivial pass at α² = 0" is **not** a valid c-push witness.
  The script's `RESULT: POSITIVE` line should require both `gap ≥ 1e-3`
  AND the witness `α² ≥ 0.05` (i.e., the witness must have at least
  5% of its L²-mass on the `a_0` mode that produces non-trivial
  `circleGap`). Without this filter, the script will trivially
  declare "POSITIVE" via the void witness `α² = 0`, which is not
  actionable.

* **Generator-side safety: do NOT escalate the result to a Lean
  candidate or to `proposal_002` in this sprint.** The Generator's
  job is to produce the evidence, not act on it. The `Experience.md`
  entry must record the outcome and the directive for the next
  sprint, but the `proposal_002` itself (or the Lean candidate)
  is a future Planner's deliverable.

* **Bulletin update.** Append exactly one line to `Bulletin.md`'s
  "Recent events" block, format
  `sprint_051 BLOCKED_NEEDS_HUMAN: per-k Scratch sweep over canonical trivial extremals — <RESULT-summary>` —
  matching the one-line style of the existing sprint 048/049/050
  lines. Do not reflow or restructure the bulletin.

* **Confirmation that this sprint does NOT tie V0.** Per the
  2026-05-02 directive forbidding structural Lean lemmas that tie
  V0's `c = 0.3554`, this sprint ships zero Lean lemmas (greppable
  check #9) and therefore cannot tie V0. The "win" delivered is
  *evidence on a fourth, structurally-distinct kernel family that
  sprint 050 explicitly demoted out of testable scope* — the
  one remaining numerical-tractability gap.

* **Confirmation that there is no untested fifth numerical kernel
  candidate.** Per sprint 050's exhaustive enumeration table,
  combined with this sprint's coverage of sprint 045's per-`k`
  series kernel under canonical trivial extremals, the *complete*
  list of testable kernels reachable from existing `Reduction.lean`
  reducers without trust-base expansion is:
  - sprint 014's `c⁴` full-window (sprint 048: falsified)
  - sprint 017's `c⁴/2` branch-2 (sprint 048: falsified)
  - literal Wang `(15)` (sprint 049: falsified; sprint 050:
    crossover pinpointed)
  - sprint 045's per-`k` series under E0–E3 (this sprint)
  After sprint 051, **every closed-form or finite-mode-extremal
  kernel reachable without trust-base expansion has been
  numerically tested.** If sprint 051 returns NEGATIVE, the
  workspace is exhaustively confirmed-blocked and `proposal_002`
  becomes the only remaining route. If sprint 051 returns POSITIVE,
  the next sprint ships a Lean candidate. Either branch closes the
  open enumeration.
