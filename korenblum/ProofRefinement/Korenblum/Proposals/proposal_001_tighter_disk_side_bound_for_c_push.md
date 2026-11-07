# Proposal 001: Tighter disk-side bound to enable `c > 0.3554` push

**Created**: 2026-05-02 by Generator (sprint 048)
**Status**: rejected
**Type**: reformulation

## What's needed

- **File(s):** new lemma(s) in `KorenblumPaper/` exposing a tighter disk-side
  bound, plus a matching annulus-side reducer in
  `ProofRefinement/Korenblum/Proof/Reduction.lean`. Exact paths to be decided
  by the human; conservative placement is a new file
  `KorenblumPaper/WangDiskTighterBound.lean` (paper-side) plus an additive
  reducer in `Reduction.lean` named e.g.
  `valid_of_disk_tighter_annulus_eq8_eq9_branch2_window`.
- **Lean surface:** a paper-faithful disk-side bound *strictly tighter* than
  the `c^4/2 · Z_ρ` branch-2 estimate currently used by sprint 017. Two
  candidate Lean shapes are offered below; human chooses one (or proposes a
  third).
- **Config changes:** if the paper-side bound depends on a numerical
  truncation envelope, register the corresponding `[[oracles]]` entry in
  `lemma.toml`. No `[seed_axioms].allowed` expansion is required if the
  bound is fully derived inside `KorenblumPaper/`.

## Mathematical content

Sprint 048's two `Scratch/` numerical witnesses
(`Scratch/sprint_048_branch2_kernel.txt`,
`Scratch/sprint_048_full_window_kernel.txt`) establish that:

* the **branch-2 kernel inequality**
  `c^4/2 ≤ ∫_{branchSplit c + ε}^{1 − ε} 2ρ³/Λ(c, ρ) dρ` (sprint 017's reducer)
  has gap **`+1.72e-04` at the seed `c = 0.3554`** and turns *strictly negative*
  for every `c ∈ {0.36, 0.37, …, 0.50}`. The relative margin at the seed is
  only `+2.16 %` — so the closed-form bound is at the brink of failing.
* the **full-window kernel inequality** `c^4 ≤ ∫_{c+ε}^{1−ε} 2ρ³/Λ(c, ρ) dρ`
  (sprint 014's reducer) is **already negative at the seed** with margin
  `−48.6 %` and falls further with growing `c`. Doubling the LHS overpowers
  the modest window enlargement.

Both reducers reduce `ValidKorenblumBound c` to a single numerical inequality
of the form `(disk-side scalar) ≤ (annulus integral)`. The annulus integrand
`2ρ³/Λ(c, ρ)` is fixed by the paper's `Λ` definition and is essentially
optimal — `Λ` is already a `(1 + sqrt(...))/2` blow-up driven by `K`. The
*disk-side* scalar `c⁴/2` (or `c⁴`) is what is too large.

The paper's section 2 derives the `c⁴/2 · Z_ρ` branch-2 disk bound as
**`paper.eq6`**, by taking the `cos²θ + sin²θ`-style averaging of two
`c²/2 · Z_ρ` bounds (one per branch) and *dropping* the per-`k`
cross-coupling that would tighten the bound further. Sprint 044's
`Σ⁺_int(c)` shape (the `tsum_partition_drop_N2_annulus_eq8_eq9` reducer of
sprint 045) keeps the per-`k` series `Σ_{k≥0} (a_k² + b_k²) · …` intact but
relies on adversarial knowledge of `(a_k, b_k)` it cannot supply in
isolation.

The structural ingredient missing from the workspace is therefore:

> **A paper-faithful, computable upper bound on the per-`k` "disk-side
> contribution" `(c^(2k+2)/2) · ‖coeffPlusGap_k(c, ρ)‖²` (or the analogous
> sprint 044 shape) that is `o(c⁴)` for the leading `k = 0` term — i.e.
> a strict improvement over `paper.eq6`'s `c⁴/2 · Z_ρ` lump.**

Two concrete candidate shapes the human could authorise (pick one):

### Shape A — sharpened branch-2 lump using `paper.eq4` cross-coupling

In Wang 2025 (paper sketch in `KorenblumPaper/PaperEq4.lean`), `paper.eq4`
gives a coupling of the form `|a_k|² ≤ … · |b_{k+1}|²` (or similar shape)
that the current `paper.eq6` proof ignores. Re-derive a tighter branch-2
lump

> `(c^4 · η(c)) / 2 ≤ ∫_{branchSplit c + ε}^{1 − ε} 2ρ³/Λ(c, ρ) dρ`

where `η(c) ∈ (0, 1)` is a *paper-derivable* shrinkage factor coming from
the cross-coupling. Concretely, `η(c) → 1` as `c → 0` (so it does not
disturb the existing sprint 017 proof at small `c`) and `η(0.40) ≤ 0.7`,
say, would re-open the gap at `c = 0.40` where the current Scratch sweep
shows `gap = −0.00824` (about `−64 %`). A target `η` schedule:

| `c`    | needed `η` | current branch-2 RHS | LHS at `η(c) · c⁴/2` |
| ------ | ---------- | -------------------- | -------------------- |
| 0.3554 | ≥ 1.000    | 8.149e-03            | 7.977e-03 (gap ≈ +)  |
| 0.36   | ≥ 0.918    | 7.708e-03            | matched             |
| 0.37   | ≥ 0.727    | 6.808e-03            | matched             |
| 0.38   | ≥ 0.574    | 5.987e-03            | matched             |
| 0.40   | ≥ 0.357    | 4.564e-03            | matched             |

These required `η` values come straight from
`Scratch/sprint_048_branch2_kernel.txt`'s `gap` column. A paper-derivable
`η(c)` need not match these exactly — even `η(0.40) ≈ 0.4` would push
`c_value` from `0.3554` to `0.40`, a substantial jump.

### Shape B — fully numerical replacement of `paper.eq6` by `paper.eq4` series

Replace the disk-side `c⁴/2 · Z_ρ` lump entirely by a per-`k` summation

> `Σ_{k=0}^{∞} (c^(2k+2)/2) · |coeffPlusGap_k(c, ρ)|² ≤ ∫_{ρ₁}^{ρ₂} 2ρ³/Λ(c, ρ) dρ`

where `coeffPlusGap_k(c, ρ)` is the per-`k` paper coefficient already
defined in `KorenblumPaper.PaperEq4`. The RHS is unchanged; the LHS is
strictly smaller than `c⁴/2 · Z_ρ` because `Σ_{k≥1}` terms are dropped
from the bound, *not* added. This is the shape sprint 044/045 already
uses, but it requires an oracle to bound `coeffPlusGap_k(c, ρ)`
adversarially. The matching `[[oracles]]` entry would be
`coeff_plus_gap_k_upper` in `Numerical_Library/wang_box_math.py`.

Shape A is a *Lean theorem* request (no new oracle, no new `Numerical_Library`
function); Shape B is an *oracle* request and can be done inline by a
sprint 049 generator if the human approves the shape and the oracle entry.

## Win unlocked

Concrete numerical target: **`c_value ≥ 0.40 = 2/5`** under Shape A with a
modest paper-derived `η(0.40) ≈ 0.4`, or **`c_value ≥ 0.42 = 21/50`** under
Shape B with sharp adversarial bounds. Both are well above the seed
`1777/5000 = 0.3554` and would discharge the bulletin's primary directive
in a single follow-up sprint. Either shape removes the need for further
`Scratch/` numerical experiments on the existing four-reducer family.

## Risk / trust cost

* **Shape A**: zero new oracles. New trusted content: one paper-side lemma
  in `KorenblumPaper/`, derivable from `paper.eq4` (already imported) and
  the existing `paperLambda_*` infrastructure. Human review burden:
  verify the `η(c)` derivation against Wang 2025 section 2.
* **Shape B**: one new `[[oracles]]` entry. Trust cost is the same as
  any other oracle — bounded by the rigour of the `Numerical_Library`
  function's interval arithmetic. Human review burden: verify the
  oracle's interval-arithmetic implementation against the paper's
  per-`k` recursion.

Either way, no new free-floating axiom; both shapes are paper-faithful.

## Follow-up sprint outline

If approved (Shape A):

1. **Sprint 049 (planner)** — re-scope the bulletin's primary directive to
   "ship `Candidates/V49.lean` proving `ValidKorenblumBound c'` for the
   largest `c'` such that the new tighter disk-side bound's kernel
   inequality holds at `c'`", and identify the exact paper-side lemma
   shape.
2. **Sprint 049 (generator)** — implement the `KorenblumPaper/WangDiskTighterBound.lean`
   lemma, extend `Reduction.lean` with `valid_of_disk_tighter_annulus_eq8_eq9_branch2_window`,
   ship `Candidates/V49.lean` invoking the new reducer at the
   numerically-witnessed `c'`.
3. **Sprint 049 (evaluator)** — confirm `axioms_used` is the V0 set with no
   new entries (Shape A introduces no oracle).

If approved (Shape B):

1. **Sprint 049 (planner)** — same re-scope, but cite the new
   `coeff_plus_gap_k_upper` oracle.
2. **Sprint 049 (generator)** — implement the oracle in
   `Numerical_Library/wang_box_math.py`, register it in `lemma.toml`,
   ship `Candidates/V49.lean` invoking sprint 045's tsum-partition
   reducer with the oracle providing the per-`k` bound.

Both follow-ups respect the bulletin's "Scratch-first then Lean" rule —
sprint 048's `Scratch/` files already provide the numerical witness;
sprint 049 just needs the paper-side machinery to translate that witness
into a Lean proof.

## Status log

- 2026-05-02 created by Generator (sprint 048) after both kernel
  numerical witnesses falsified the simple-numerical-push hypothesis.
- 2026-05-02 third candidate kernel (paper eq15 direct) also falsified
  above seed; structural improvement per Shape A or Shape B is now the
  only remaining route. Sprint 049 numerically swept Wang's literal
  paper equation (15) -- LHS `1`, integrand `12rho^3(rho^2 - c^2)/(c^6 Lambda)`
  on `[c, branchSplit c]` plus `4rho^3/(c^4 Lambda)` on `[branchSplit c, 1]` --
  over `c in {0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.42, 0.45, 0.48, 0.50}`.
  The seed row reproduces a comfortable positive margin
  (`gap = +2.55e-02`, `+2.55%` rel.); every higher `c` row shows a
  *negative* gap, falling from `gap = -7.84e-02` at `c = 0.36` to
  `gap = -9.73e-01` at `c = 0.50`. Evidence file:
  `Scratch/sprint_049_paper_eq15_direct_kernel.txt`. Implication: the
  `valid_of_eq15` reducer cannot be c-pushed by simply approving a new
  `hEq15_seed_<c'>` axiom -- the underlying inequality at `c > 0.3554`
  is numerically false. All three currently-explored kernel shapes
  (sprint 048's `c^4` window, sprint 048's `c^4/2` branch-2 window,
  sprint 049's paper-eq15 direct) falsify above seed; the structural
  shapes A or B in this proposal remain the only known c-push route.
  `Status:` field unchanged (still `pending` -- awaiting human review).
- 2026-05-02 high-precision (`mpmath`, `dps=50`, `N_TRUNC=200`)
  re-verification of all three falsified kernels:
  - `c^4` full-window (sprint 014): sign agreement = AGREE
  - `c^4/2` branch-2 (sprint 017): sign agreement = AGREE
  - paper eq(15) literal (sprint 049): sign agreement = AGREE
  All three sprint 048/049 falsifications above the seed `c = 0.3554`
  are rigorous facts at `mpmath dps=50`/`N_TRUNC=200`, not
  `scipy.quad` / `N_TRUNC=50` artefacts; absolute mpmath-vs-scipy
  gap discrepancies are `<= 5e-8` per row, two-to-three orders of
  magnitude below the smallest |gap| observed (`1.72e-04` at the
  branch-2 seed). Evidence file:
  `Scratch/sprint_050_mpmath_reverify.txt`. Fine-grained crossover
  pinpoint for the literal Wang `(15)` kernel
  (`c in {0.3554, 0.3556, 0.3560, 0.3565, 0.3570, 0.3580, 0.3590, 0.3600}`):
  positive margin `gap >= 1e-3` holds up to `c = 0.3560`
  (`gap = +1.131e-02`) and fails at `c = 0.3565`
  (`gap = -3.598e-04`). The seed-to-failure window is `~0.0011`
  wide -- a narrow but non-zero "smooth shoulder", not a cliff at
  the seed. Evidence file:
  `Scratch/sprint_050_eq15_crossover_pinpoint.txt`. Implication for
  `proposal_001`: Shape A's required `eta(c)` shrinkage is
  *stronger* than the sprint-048 branch-2 table suggested, because
  the literal `(15)` kernel -- which dominates branch-2 in
  numerical content -- collapses inside `c in (0.3560, 0.3565)`,
  not slowly across `c in [0.36, 0.40]`; any `eta(c)` schedule must
  start biting before `c = 0.357` to keep a workable gap. Shape B
  (per-`k` series oracle) remains the only structurally distinct
  alternative route and is correspondingly more attractive given
  Shape A's now-tighter `eta(c)` requirement. `Status:` field
  unchanged (still `pending` -- awaiting human review).
- 2026-05-02 sprint 051 — Scratch sweep of sprint 045's per-`k`
  series kernel `Σ⁺_int(c) ≤ ∫ 2ρ³·Z_ρ/Λ` under the four canonical
  trivial extremal `(a, b)` families E0–E3 (`mpmath dps=50`,
  `N_TRUNC=200`). RESULT: **NEGATIVE** for every `(family, c, α²)`
  with `c > 0.3554` and `α² ≥ 0.05` (the floor required for
  `circleGap ≥ 0`); no triple yields `gap ≥ 1e-3`. The closest
  near-miss is family E2 (`a_0=√α², b_1=√(1-α²)`) at `c = 0.36`
  with `α² = 0.05`, gap = `+8.91e-4` (just below the 1e-3 target).
  At `c = 0.37` the floored gap is already `−3.28e-4`. Family E3
  (`a_0/b_2`) is uniformly negative even at the seed under the
  floor. Families E0/E1 are structurally void (E0 has no Z_ρ; E1
  has α²=0 which kills `circleGap`). Implication for `proposal_001`
  Shape B: the per-`k` route under canonical trivial extremals
  has **no headroom above the seed** at the 1e-3 margin level —
  the analytical break-even slider `α²* = c²/(c²+J(c))` is
  pushed to `≥ 0.94` at every above-seed `c`, meaning a "valid"
  c-push under E2/E3 needs `>94%` of L²-mass on `b_k`, which then
  reduces `Σ⁺_int(c)` back down to `≤ 6%·c²` and the kernel barely
  closes; the slider's "smooth shoulder" is `~0.0046` wide above
  the seed, comparable to (15)'s `~0.0011`. Shape B's narrowing
  to a per-`k` adversarial supremum oracle is therefore even
  more pointed than before — finite-mode extremals do not give
  the headroom; an honest `proposal_002` would need to either
  (a) license a Hayman-extremal-style infinite-mode oracle
  certifying `sup_{(a,b)} Σ⁺_int(c) / RHS(c, (a,b)) ≤ 1` at some
  `c > 0.3554`, or (b) license a paper-side analytical reduction
  trimming the LHS by an `o(1)` per-`k` factor analogous to
  Shape A's η(c). Evidence file:
  `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`.
  `Status:` field unchanged (still `pending` -- awaiting human
  review).
- 2026-05-02 **REJECTED by human (Alan)**. Status changed
  `pending → rejected`. Rejection rationale below applies
  to proposal_001 only; the sprint 048–051 numerical
  evidence (which is rigorous) is preserved as-is. A
  resubmission must be filed as a *new* proposal
  (`proposal_002_*` or later) addressing every point in
  §"Required to resubmit" below. **Do not re-open
  proposal_001 by editing its `Status:` field — file a new
  proposal instead.** Until a successor proposal is
  approved, no Lean sprint may consume Shape A or Shape B
  as described here.

  ### Why rejected

  **(R1) Shape A's central citation is false.** The proposal
  claims `paper.eq4` exposes a per-`k` cross-coupling of the
  form `|a_k|² ≤ … · |b_{k+1}|²`. It does not. The actual
  `Eq4SigmaPlusBound` in `KorenblumPaper/PaperAxioms.lean`
  (lines 132–137) is the bulk scalar conjunction
  `Σ⁺(r) ≤ Σ⁺(c) ∧ Σ⁺(c) ≤ Σ⁻(c) ∧ Σ⁻(c) = c²·Z_c`. There is
  no per-`k` coupling exposed. The cited paper-sketch file
  `KorenblumPaper/PaperEq4.lean` does not exist in the
  workspace (only `PaperEq15.lean` exists). Any
  Shape-A-style `η(c)` derivation would therefore need to
  *first* expand the paper surface — itself a separate
  trust-base expansion that this proposal does not request.

  **(R2) Shape B's mathematical statement is garbled.** The
  proposal writes the LHS as
  `Σ_k (c^(2k+2)/2) · |coeffPlusGap_k(c, ρ)|²`. Three
  errors:
  1. `coeffPlusGap_k` does not depend on `(c, ρ)`. Per
     `PaperAxioms.lean:42`, `coeffPlusGap a b k :=
     ‖a k‖² − ‖b k‖²` — it depends on the coefficient
     sequence `(a, b)`, not on radii.
  2. The `|·|²` is incompatible with the existing
     definition: `coeffPlusGap_k` is signed (positive on
     `N1`, negative on `N2`). Squaring it yields a different
     object.
  3. The `1/2` integration weight conflates Wang's eq6
     branch-2 averaging with the `1/(k+1)` weight from
     sprint 042/045's term-by-term integration. The actual
     sprint 045 kernel (`Reduction.lean:6953`) is
     `Σ⁺_int(c) := ∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1) ≤
     ∫ 2ρ³ · Σ⁻₀(a,b,ρ) / Λ(c,ρ) dρ`,
     not what the proposal writes.

  **(R3) Shape B is not specifiable as a verifiable
  numerical oracle.** Sprint 051's own canonical-extremals
  sweep (RESULT: NEGATIVE for every above-seed `c` at
  `α² ≥ 0.05`, near-miss of `+8.91e-4` < `1e-3` at
  `c = 0.36`, family E2) is consistent with: (a) the
  Korenblum kernel `Σ⁺_int(c) ≤ ∫ 2ρ³·Σ⁻₀/Λ dρ` is
  universally quantified over admissible `(a, b)` from
  `Section2Assumptions`; (b) both sides depend on
  `(a, b)`; (c) `Section2Assumptions` ships no
  per-coefficient bound `‖a_k‖² ≤ M_k`; (d) without such
  a bound, `Σ⁺_int(c)` is not bounded a priori uniformly
  in `(a, b)`, so an interval-arithmetic oracle in
  `Numerical_Library/wang_box_math.py` has no input
  range to compute over. An "oracle" here would either
  reduce to the closed-form sprint 045 kernel inequality
  itself (which is the Korenblum theorem at this `c`),
  or collapse to the trivial bound `0 ≤ Σ⁺_int(c)`
  (since individual `‖a_k‖²` are unbounded above without
  paper input). The proposal does not say which it
  intends, and neither alternative is a real oracle. The
  workspace policy (`feedback_no_heuristics`) forbids
  accepting an oracle entry whose numerical statement is
  not pinned down to a specific airtight bound at
  submission time.

  **(R4) Sprint 051 partially obviates the proposal.**
  Sprint 051 reports the per-`k` route under canonical
  trivial extremals E0–E3 has no `1e-3` margin above the
  seed at any `c`; the very fact the proposal
  acknowledges this (status log entry sprint 051,
  closing paragraph) means even Shape B's *target*
  `c_value ≥ 0.42` is empirically out of reach for
  finite-mode extremals. Any honest reformulation must
  state which infinite-mode adversary it intends to
  certify against, and that adversary's input data
  (e.g. a Hayman extremal generating function) needs
  to be a *paper-derivable* object, not a heuristic
  from `Numerical_Library/`.

  ### Required to resubmit (as a new proposal)

  Any successor `proposal_NNN_*.md` MUST address all of
  the following before being eligible for human review:

  1. **Cite paper.eq4 accurately.** State that the
     workspace surface exposes the bulk inequality
     `Σ⁺(c) ≤ Σ⁻(c)`, not a per-`k` coupling. If a
     per-`k` coupling is needed, file a *separate*
     paper-axiom-expansion proposal for it first; cite
     the explicit paper page/equation in Wang 2025
     (use the local PDF `Wang2025.pdf` /
     `Wang2025.txt`), and state the precise Lean
     surface the new axiom would have.
  2. **Write the kernel inequality literally.** Use the
     actual sprint 045 kernel
     `∑'_{N1} (‖a_k‖² − ‖b_k‖²) · c^(2k+2)/(k+1) ≤
     ∫_{ρ₁..ρ₂} 2ρ³ · Σ⁻₀(a,b,ρ)/Λ(c,ρ) dρ`
     (or whatever reducer the proposal targets) with
     `(a, b)` and `(c, ρ₁, ρ₂)` parameters explicit.
  3. **Specify the oracle's exact numerical statement.**
     If proposing an oracle, state:
     - the input bound on `‖a_k‖²` (or whichever
       per-`k` coefficient quantity is being bounded),
       *with the paper-side or new-axiom source for
       that bound named explicitly*;
     - the truncation point `K` and the closed-form
       analytic tail bound for `k > K`;
     - the interval-arithmetic library used for the
       head `k ≤ K` (e.g. `mpmath` with directed
       rounding, `python-flint`, or `intpakX`) and
       the precision/`dps` setting;
     - the proven inequality the oracle exports as a
       Lean axiom (verbatim Lean statement).
     **An oracle entry without all four is heuristic
     and will be rejected.**
  4. **Show pointwise feasibility before approval.** A
     `Scratch/` script must demonstrate the proposed
     bound holds at the target `(c, …)` against at
     least one infinite-mode adversary (e.g. a Hayman
     extremal) with margin `≥ 1e-3`, not just the
     four trivial finite-mode extremals E0–E3 sprint
     051 already swept. Without this, the proposal
     is speculative.
  5. **Decide between the routes openly.** State
     whether the proposal requests
     - a *new free-floating analytic axiom* (highest
       trust cost, requires the strongest paper
       justification), or
     - a *new oracle entry* (must satisfy point 3
       above), or
     - a *paper-axiom expansion* derived from
       existing Wang 2025 content (requires citing
       the page and sketching the derivation).
     The current proposal mixes Shape A
     (axiom-shaped) and Shape B (oracle-shaped)
     without committing, which is part of why it is
     not actionable.

  ### What the next Planner should do

  - Treat `proposal_001` as closed.
  - Do **not** queue any sprint that consumes Shape A
    or Shape B as currently described.
  - The bulletin's "Improve `c_value`" directive
    stands. Continued numerical / structural
    exploration is fine; new proposals are welcome
    under the criteria above.
  - Sprint 048–051's `Scratch/` artefacts remain
    authoritative as numerical evidence and may be
    cited in successor proposals.
