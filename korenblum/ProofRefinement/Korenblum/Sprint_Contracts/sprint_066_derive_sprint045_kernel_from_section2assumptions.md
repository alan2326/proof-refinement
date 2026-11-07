# Sprint 066: Attempt-first analytic Lean derivation — discharge sprint 045's per-`k` × integrated kernel `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ` from `Section2Assumptions` directly

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V52.lean` (current high-water mark, `c_value = 7129/20000 = 0.35645` via the literal-(15) HP oracle channel)
**Target file**: `Candidates/V53.lean` PLUS supporting per-candidate derived-theorem files under `Candidates/V53/`
**Direction**: section2-proof + analytic-Lean derivation (paper-axiom-light closing reducer, attempting a structurally novel discharge of sprint 045's witness kernel from `Section2Assumptions` instead of from a numerical extremal sweep)

## Goal

Attempt to prove, **as a Lean theorem** in a per-candidate derived-theorem file under `Candidates/V53/`, the witness kernel that sprint 045's
closing reducer `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window` takes as a hypothesis:

```lean
theorem sprint045_kernel_from_assumptions
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    -- (some choice of ρ₁, ρ₂ ∈ (c, 1) — see "Three Lean derivation directions" below)
    : (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
          else 0)
        ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
              / WangOuter.paperLambda K c ρ'
```

If the kernel is proved as a `Section2Assumptions` consequence at any `c`,
ship `Candidates/V53.lean` with `c_value` set to the largest such `c`
admissible by the proven kernel and the closing reducer's other premises
(integrability, summability cells). The closing reducer is already in
`Reduction.lean`; the new content is the per-candidate derivation file
discharging the kernel.

This sprint is **not** a numerical-extremal sweep. Sprint 051 already
ran that sweep on canonical extremals E0–E3 and found the kernel
falsifies for `c > 0.3554` on the canonical-extremal cone. The new and
strictly distinct question this sprint asks is whether the kernel is
derivable analytically **on the cone of `Section2Assumptions a b K c`
instances**, which is *strictly narrower* than the canonical-extremal
cone (E1's pure-`g` adversary `a ≡ 0, b_1 = 1` violates `eq9` because
`circleGap a b ρ = −ρ²` on E1, while `liftGap ρ ≥ 0` always, so
`liftGap ρ ≤ paperLambda · circleGap ρ` requires the RHS to be
non-negative — IMPOSSIBLE on E1 with the Lean-side
`circleGap = circleGapSeries = ∑' coeffPlusGap_k · r^(2k)` convention).
The numerical sweep tested the wrong cone for the Lean-derivability
question.

## Why

### Why this sprint, why now

Sprint 065 attempted to compose sprint 044's disk per-`k` upper bound
with sprint 047's annulus per-`k` × per-`k` series equality into a
brand-new closing reducer with paper-axiom signature `{}` AND
oracle-cell signature `{}`, and EXITED `BLOCKED` after numerically
falsifying the kernel `Σ⁺_int(c) ≤ Σ⁺_int_ann(c) − Σ⁻_int_ann(c)` on
the canonical-extremal cone E0–E3 — argmin family E1 with min admissible
gap ≈ −0.492 at every tested `c` ≥ 0.35645.

The obstruction note `Scratch/sprint_065_obstruction.md` recommended
three next moves; this planner has reviewed all three and rejected
each:

- **Move 1 (drop-N2 kernel `Σ⁺_int(c) ≤ Σ⁺_int_ann(c)`)**: explicit
  algebra shows this kernel — combined with sprint 044 + sprint 047
  upper-bound-only chain — gives the sufficient condition
  `Σ⁺_int(c) + Σ⁺_int_ann(c) ≤ 0` for `circleGap ≤ 0`, but
  `Σ⁺_int(c) + Σ⁺_int_ann(c) = ∑'_(k∈N1) coeffPlusGap_k / (k+1)` is
  non-negative and on E0 (the pure-`f` adversary `a_0 = 1, b ≡ 0`,
  which IS in the canonical-extremal cone) the LHS equals `1` while
  the RHS is `0`. **Move 1 is structurally dead at the candidate-contract
  level.**
- **Move 2 (sprint 044 + sprint 045 composition)**: this is *exactly*
  sprint 045's existing reducer; redundant. Has already been at V0
  with the kernel discharged by `eq15` oracle indirectly. Ties V52.
- **Move 3 (file `proposal_004`)**: gated on the four-condition guide
  in the planner agent rules, AND on Alan's queue progress on
  proposal_003 (currently `pending`). Not the right sprint shape this
  cycle — proposal-filing is not falsifiable in one Generator session
  the way an attempt sprint is.

What sprint 065's analysis **missed** — and what this sprint exploits
— is that the canonical-extremal cone E0–E3 used by sprints 048, 049,
050, 051, 060 Phase B, and 065 Phase A is **not** the cone that the
closing reducer needs to discharge. The closing reducer is parametric
over `Section2Assumptions a b K c` instances, and `Section2Assumptions`
imposes structural constraints (eq3, eq8, eq9 chains) that **rule out**
several canonical extremals. Specifically:

- **E0 (`a_0 = 1, b ≡ 0`)** fails admissibility (`|f| > |g|` strictly
  on `|z| = c`), so `paper.eq8`-`eq9` chains contradict at the
  outset — E0 does NOT instantiate `Section2Assumptions`.
- **E1 (`a ≡ 0, b_1 = 1`)**: `coeffPlusGap_1 = 0 − 1 = −1`, so
  `circleGap a b r = circleGapSeries a b r = −r²` on E1. Then
  `paper.eq9_liftGap_to_circleGap` requires `liftGap ρ ≤ paperLambda
  K c ρ · circleGap ρ` for `c < ρ < 1`, but the RHS is
  `(positive) · (negative) = negative` while `liftGap ≥ 0`. Direct
  contradiction. **E1 is NOT a `Section2Assumptions` instance.**
- **E2 (`a_0 = α, b_1 = √(1−α²)`, all others zero)**: needs case
  analysis — eq8/eq9 may or may not hold depending on `(α, c)`.
- **E3 (`a_0 = α, b_2 = √(1−α²)`)**: similar, needs analysis.

So sprint 065's E1-argmin "structural" falsification — the sole
load-bearing falsification at every tested `c` — is moot. **The
kernel sprint 045 needs may well be true on the
`Section2Assumptions`-cone**, and sprint 051's negative numerical
finding on E0–E3 doesn't disprove that.

This is genuinely new analytical territory for the workspace, not
covered by sprints 048–051 or sprint 065. **No prior sprint has
attempted to derive sprint 045's kernel directly from
`Section2Assumptions`.** The harness's existing infrastructure
(sprints 005–047) builds an extensive paper-axiom-free or
paper-axiom-light cone of intermediate identities, several of which
are direct candidates for the discharging chain (see "Three Lean
derivation directions" below).

### Why this is not a numerical-push sprint

Sprint 060 confirmed the HP `eq15`-oracle envelope is exhausted at
`c = 0.35645`. Sprint 065 confirmed the per-`k` × per-`k`
canonical-extremal numerical sweep gives no new c-push without
trust-base expansion. The bulletin's directive line 27–31 says
"sprints that tie V0's `c` are no longer wins; they are at best
preparatory and must explicitly justify why they cannot be folded into
a single c-pushing sprint."

This sprint **CAN c-push** — if the kernel discharge succeeds, it
unlocks sprint 045's full reducer and the candidate ships at the
largest `c` for which the chain admits (potentially `c` >> 0.35645,
since sprint 045's kernel is paper-axiom-light and not gated by the
literal-(15) crossover at ~0.35635). The two-outcome contract below
specifies the exact ship-vs-block decision tree.

### Generator capability check (per planner agent rules)

The planner agent rule reads: "If a planner cannot enumerate three
distinct Lean-derivation directions for an analytic claim, the
obstruction is structural, not capability — and that fact must be
demonstrated by an attempted generator sprint, not assumed."

Three distinct Lean derivation directions enumerated below.

### Why proposal-filing is not the right shape

Per the four-condition guide in the planner agent rules:

1. **Tried hard and failed**: this exact derivation has NEVER been
   attempted in Lean. Sprint 045 takes the kernel as a hypothesis;
   nobody has tried to prove it from `Section2Assumptions`. Condition
   not satisfied.
2. **Genuinely large derivation cost**: predicted body is in the
   range of 200–600 lines of Lean using existing Mathlib +
   workspace infrastructure (sprints 005, 011, 027, 028, 032, 042,
   043). Within generator scope.
3. **Strong reason to believe correct**: the chain via Direction 3
   (`eq3 + eq4 + eq5 + integration via sprint 042`) is essentially
   Wang's published proof structure. Mathematical truth not in
   doubt — the question is which Mathlib lemma family unlocks the
   shortest proof.
4. **Strong evidence improves `c_value`**: if the kernel is provable
   at ANY `c`, the closing reducer ships at that `c`. If provable at
   `c > 0.35645` (Direction 3 should give some c-headroom past V52),
   that's a concrete c-push; if provable only at `c ≤ 0.35645`, the
   sprint's outcome documents which paper-axiom is the bottleneck —
   strong attempt-first evidence for any future proposal_004.

So this is an attempt sprint, not a proposal sprint.

## Three Lean derivation directions

The generator should attempt these in order; success on any one yields
a passing V53.

### Direction A — eq3 + integration + eq4 + Z-monotonicity chain

**Sketch.** Use `paper.eq3_circleGap_decomposition`:
`circleGap r = sigmaPlus r − r²·sigmaZeroMinus r` for all `0 ≤ r < 1`.
Integrate over `[0, c]`:

- `diskExcess = ∫_0^c 2r·sigmaPlus r dr − ∫_0^c 2r·r²·sigmaZeroMinus r dr`.

Apply sprint 042's `tsum`-of-integrals machinery to convert each piece
to a `tsum`:

- `∫_0^c 2r·sigmaPlus r dr = ∑'_(k∈N1) coeffPlusGap_k · c^(2k+2)/(k+1) = Σ⁺_int(c)`.

This is sprint 040 / sprint 043's identity for the disk side.

For the RHS upper bound on `Σ⁺_int(c)`, use sprint 032's series-level
`sigmaPlus` monotonicity: `sigmaPlus r ≤ sigmaPlus c` for `r ≤ c`,
hence `∫_0^c 2r·sigmaPlus r dr ≤ c²·sigmaPlus c`. So
`Σ⁺_int(c) ≤ c²·Σ⁺(c)`. Apply `paper.eq4_sigmaPlus_bound`:
`Σ⁺(c) ≤ Σ⁻(c) = c²·sigmaZeroMinus c = c²·Z_c`. So
`Σ⁺_int(c) ≤ c⁴·Z_c`.

For the integrand RHS, apply sprint 011's series-monotonicity
`Z_ρ ≥ Z_c` for `ρ ≥ c` and pull `Z_c` out:
`∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ ≥ Z_c·∫_{ρ₁..ρ₂} 2ρ³/Λ dρ`.

Sufficient: `c⁴·Z_c ≤ Z_c·∫_{ρ₁..ρ₂} 2ρ³/Λ dρ`, i.e.
`c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ`.

**This is sprint 014's kernel** — and sprint 048's `Scratch/` evidence
shows it falsifies even at the seed `c = 0.3554`. So Direction A
cannot c-push past V52. **Document this dead end in the sprint
output**; the value of writing it down is making the gap explicit:
the bulk-`Σ⁺(c) ≤ Σ⁻(c)` step (eq4 second conjunct) is what loses
all per-`k` precision.

### Direction B — eq3 + integration + per-`k` upper bound on Σ⁺_int(c) via convexity (sprint 028, sprint 033)

**Sketch.** Same disk-side identity `Σ⁺_int(c) = ∑'_(k∈N1)
coeffPlusGap_k · c^(2k+2)/(k+1)`. Apply sprint 033's series-level
`sigmaPlus` cross-radius CONVEXITY upper bound (paper-axiom-free):
`sigmaPlus r ≤ μ_1 sigmaPlus s + μ_2 sigmaPlus t` at `r² = μ_1 s² +
μ_2 t²` with `s ≤ r ≤ t`. Choose `s = 0` and `t = ρ` to get
`sigmaPlus r ≤ (1 − r²/ρ²) sigmaPlus 0 + (r²/ρ²) sigmaPlus ρ`.

Integrating against `2r` from 0 to `c`:

- `Σ⁺_int(c) ≤ sigmaPlus 0 · ∫_0^c 2r·(1 − r²/ρ²) dr + sigmaPlus ρ · ∫_0^c 2r³/ρ² dr`
- `= sigmaPlus 0 · (c² − c⁴/(2ρ²)) + sigmaPlus ρ · c⁴/(2ρ²)`.

Now `sigmaPlus 0 = coeffPlusGap_0 = |a_0|² − |b_0|²`. By
`paper.eq4_sigmaPlus_bound` first conjunct AT `r = 0`:
`sigmaPlus 0 ≤ sigmaPlus c`, then via the second conjunct
`sigmaPlus c ≤ sigmaMinus c = c²·Z_c`. So `sigmaPlus 0 ≤ c²·Z_c`.

For `sigmaPlus ρ` with `ρ > c`: this is the sprint 033 cross-radius
upper bound applied at radius `ρ`, NOT covered by `paper.eq4` (which
is restricted to `r < c`). **This is the structural bottleneck for
Direction B.** Without an `eq4`-extension at radius `ρ > c`, we
cannot bound `sigmaPlus ρ` in terms of `Z`-quantities.

**One workaround**: use sprint 005's identity
`sigmaMinus ρ = ρ²·sigmaZeroMinus ρ = ρ²·Z_ρ`, and look for a relation
between `sigmaPlus ρ` and `sigmaMinus ρ` that holds at `ρ > c`.
`paper.eq4` does not provide one. **Workspace-derivable
alternative**: `sigmaPlus ρ ≤ ?` from `sigmaPlus_monotone_of_summable`
(sprint 032) at radius `ρ > c` would give `sigmaPlus ρ ≤ sigmaPlus 1`
which is divergent — useless. **Direction B is also blocked at the
`sigmaPlus ρ` cell.**

Document the dead end. The bottleneck is the missing
`sigmaPlus ρ ≤ φ(ρ) · Z_ρ`-shaped bound at `ρ > c` — exactly
proposal_003's territory.

### Direction C — eq5 (or eq6) + sprint 042 + eq8/eq9 chain bypassing bulk eq4

**Sketch.** This is the workspace-internal "branch-1 collapse" cone
(sprints 015, 022, 023, 024, 031, 045) but framed at the per-`k`
layer.

`paper.eq5_branch1_sigmaReduction`: `diskExcess ≤ branch1SigmaKernel(c, ρ)·sigmaMinus ρ` for `c < ρ < branchSplit c`. So
`Σ⁺_int(c) − Σ⁻_int(c) = diskExcess ≤ branch1SigmaKernel(c, ρ)·ρ²·Z_ρ` (via sprint 005).

Note: `Σ⁻_int(c) ≥ 0`, so `Σ⁺_int(c) ≤ Σ⁻_int(c) + branch1SigmaKernel(c, ρ)·ρ²·Z_ρ`.

For an upper bound on `Σ⁻_int(c)`: per-`k`,
`Σ⁻_int(c) = ∑'_(k∈N2) coeffMinusGap_k · c^(2k+2)/(k+1) ≤ c²·∑'_(k∈N2) coeffMinusGap_k · c^(2k)/(k+1)`. The RHS is essentially
`c²·Σ⁻(c)·(some 1/(k+1)-weighted average)`, which doesn't admit a
clean bound from existing `Section2Assumptions` fields without paper-side
trust expansion.

**Alternative path**: apply sprint 044 directly (`diskExcess ≤
Σ⁺_int(c)`), then use sprint 045's reducer with the kernel on the
RHS being `∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ` — to derive the kernel from
`Section2Assumptions`, we need to bound `Σ⁺_int(c)` from above by
`∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ` directly. This is what sprint 045's witness
existential takes as input.

Following sprint 045's structure: pick `ρ₁ ∈ (c, branchSplit c]`.
By `paper.eq5`: `diskExcess ≤ branch1SigmaKernel(c, ρ₁)·sigmaMinus ρ₁ = (c⁶/(6ρ₁²(ρ₁²−c²)))·ρ₁²·Z_{ρ₁} = (c⁶/(6(ρ₁²−c²)))·Z_{ρ₁}`. So
`diskExcess ≤ (c⁶/(6(ρ₁²−c²)))·Z_{ρ₁}`.

By sprint 044: `diskExcess ≤ Σ⁺_int(c)`. These are TWO upper bounds
on the same quantity. The minimum is the tighter one.

To get a chain `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ`, we need a
DIFFERENT chain from `Σ⁺_int(c)` upward, not downward to `diskExcess`.

**Try**: `Σ⁺_int(c) = ∫_0^c 2r·sigmaPlus r dr` (sprint 040's
intermediate). Use sprint 028's series-level `sigmaZeroMinus` cross-
radius lower bound (paper-axiom-free): `Z_r ≥ μ_1 Z_c − μ_2 Z_ρ` at
`c² = μ_1 r² + μ_2 ρ²` (with appropriate sign conventions). NOT directly
useful for bounding `sigmaPlus r`.

Use `paper.eq4` first conjunct: `sigmaPlus r ≤ sigmaPlus c` for
`r < c`. So `Σ⁺_int(c) ≤ sigmaPlus c · ∫_0^c 2r dr = c²·sigmaPlus c
≤ c²·sigmaMinus c = c⁴·Z_c` (using `paper.eq4` second + third
conjuncts).

Now: is `c⁴·Z_c ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ` derivable from
`Section2Assumptions`? Use sprint 011's `Z`-monotonicity `Z_ρ ≥ Z_c`
for `ρ ≥ c`:
`∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ dρ ≥ Z_c · ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ`. Sufficient
to show `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ` — sprint 014's kernel,
already known to falsify at the seed (Direction A again).

**So Direction C also reduces to sprint 014's kernel via the
bulk-`eq4` step, just like Direction A.** Direction C without the
bulk-`eq4` step requires a per-`k` analog of `Σ⁺(c) ≤ Σ⁻(c)` which
the `Section2Assumptions` bundle does not expose.

### Honest assessment — likely BLOCKED outcome

All three directions reduce to either sprint 014's kernel (which
falsifies above the seed `c = 0.3554`) or to a missing
`sigmaPlus ρ ≤ φ(ρ)·Z_ρ` bound at `ρ > c` (which is precisely
proposal_003's deferred trust-base expansion).

**However** — the planner-agent rule explicitly requires a generator
attempt before declaring structural blockage. The generator may find
a derivation chain through sprints 015/022/023/024/036/038/039 that
this planner has not enumerated; it may also find that the
sprints 005/027/028/032/033/042/043 series-internal infrastructure
is rich enough to bypass the bulk-`eq4` step in a way the planner
missed.

Two outcomes are both informative:

- **Outcome A (success at `c > 0.35645`)**: ship V53 with a
  paper-axiom-light, oracle-cell-free closing chain at the new c.
  Massive c-push.
- **Outcome A' (success at `c = 0.35645` only)**: ship V53 at the
  V52 c with strict trust-surface improvement (paper-axiom signature
  shrinks from `{eq15-oracle}` to `{eq2, eq3, eq4, eq5 (or eq6),
  eq8, eq9}` plus zero oracle cells). Score ties V52 — preparatory
  per bulletin Step 1, but the trust-surface reduction is concrete
  evidence that the existing oracle channel can be retired.
- **Outcome B (BLOCKED)**: write a precise obstruction note at
  `Scratch/sprint_066_obstruction.md` naming **which** paper-axiom
  step is the bottleneck and **why** the workspace's existing
  paper-axiom-free infrastructure (sprints 005/027/028/032/033) is
  insufficient to bridge it. This obstruction note is the
  attempt-first evidence the four-condition guide requires for any
  future `proposal_004`.

The **score-improvement direction** is real: Outcome A pushes c
materially. Outcome A' is the only "preparatory tie" outcome and
must be explicitly justified as the only c-tying option in the AC.
Outcome B is BLOCKED.

## Concrete edits expected

### Outcome A (kernel proves at `c > 0.35645`)

- `Candidates/V53/SprintZeroFourFiveKernel.lean`: per-candidate
  derived-theorem file with the proven kernel
  `sprint045_kernel_from_assumptions`. Body 200–600 lines using
  sprints 005, 011, 027, 028, 032, 040, 042, 043, 044 +
  `paper.eq3`, `paper.eq4`, `paper.eq5` (or `eq6`), `paper.eq8`,
  `paper.eq9`. NO new axioms, NO new `Section2Assumptions` fields.
- (optionally) `Candidates/V53/Witness.lean`: per-candidate
  derived-theorem file packaging the witness `(ρ₁, ρ₂)` choice and
  the `Summable` / `IntervalIntegrable` cells sprint 045's reducer
  needs.
- `Candidates/V53.lean`: new candidate at `c_value = ?/?` (some
  rational `> 7129/20000`), using
  `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
  with the kernel discharged by the per-candidate file. Sink theorem
  remains `korenblum_constant_search`.
- (no edits to `Reduction.lean`, `KorenblumPaper/`, `lemma.toml`,
  or `Numerical_Library/`).
- `Bulletin.md` `## Recent events` row.
- `Experience.md` entry per the bulletin's "Honesty in Experience.md"
  directive.
- `Refinement_Log/log.jsonl` row appended by the evaluator.

### Outcome A' (kernel proves only at `c = 7129/20000`)

Same as Outcome A except `Candidates/V53.lean` ships at
`c_value = 7129/20000` (V52 tie). The `Bulletin.md` and
`Experience.md` entries must explicitly justify the c-tie per
bulletin Step 1 — specifically, the strict trust-surface improvement
(paper-axiom signature shrinks to `{eq2..9 subset}`, zero oracle
cells) AND the structural prerequisite role for a future c-push that
*does* break past V52 once a proposal_003-style trust-base expansion
or a refinement of Direction A/B/C lands.

### Outcome B (kernel does NOT prove)

- `Scratch/sprint_066_obstruction.md`: precise obstruction note,
  naming which paper-axiom or workspace-internal lemma is the
  bottleneck, citing the line-level `BLOCKED` evidence from the
  Lean attempt. Style: match `Scratch/sprint_065_obstruction.md`.
- (NO `Candidates/V53.lean`, NO `Candidates/V53/`, NO
  `lemma.toml` edits, NO `Reduction.lean` edits, NO
  `KorenblumPaper/` edits, NO `Numerical_Library/` edits.)
- `Bulletin.md` `## Recent events` row (one line per the
  bulletin's format).
- `Experience.md` entry per the "Honesty in Experience.md" directive.
- `Refinement_Log/log.jsonl`: no new row (no candidate evaluated).

## Acceptance criteria

### Outcome A or A'

1. `lake build ProofRefinement.Korenblum.Candidates.V53` succeeds with
   no `sorry`, no new axioms beyond seed.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V53.lean` returns `pass: true`.
3. `axioms_used ⊆ {seed}` (i.e., NO oracle cells — the V53 chain is
   paper-axiom-derived without invoking `hEq15_oracle_certified_*` or
   any other registered oracle). This is the
   trust-surface-improvement check.
4. **Outcome A**: `c_value > 7129/20000` (strict c-push).
   **Outcome A'**: `c_value = 7129/20000` AND the sprint contract's
   acceptance test 5 below holds.
5. (Outcome A' only) `Bulletin.md` `## Recent events` row explicitly
   names the trust-surface improvement (paper-axiom signature, oracle-
   cell signature, both shrunk vs. V52) AND `Experience.md` entry
   names the *specific* further trust-base expansion (proposal_003 or
   alternative) that would unlock the next c-push.

### Outcome B

1. `Scratch/sprint_066_obstruction.md` exists with:
   - the *exact* Lean tactic chain attempted, line-by-line, for at
     least Direction A and at least one of Direction B / Direction C,
   - the *exact* paper-axiom or workspace lemma that is the
     bottleneck (named at the granularity of
     `paper.eq4_sigmaPlus_bound.2` or `sprint 032`'s
     `sigmaPlus_monotone_of_summable`),
   - a *closed-form algebraic identity* showing **why** the
     bottleneck is mathematical, not tactical (analogous to the
     "closed-form sanity for E1" section of
     `Scratch/sprint_065_obstruction.md`),
   - **no falsification claim** — Outcome B says only "this proof
     chain is blocked at this point," not "the kernel is false".
     Falsification is the wrong claim because the
     `Section2Assumptions`-cone is narrower than any extremal cone
     numerically tested to date.
2. NO `Candidates/V53.lean` exists.
3. NO new files under `Candidates/V53/`.
4. NO edits to `lemma.toml`, `Reduction.lean`, `KorenblumPaper/`,
   `Numerical_Library/`, or any prior `Candidates/V<N>.lean`.
5. STATUS=BLOCKED returned (NOT BLOCKED_NEEDS_HUMAN, NOT a halt
   sibling — the obstruction is tactical-Lean / proof-theoretic, not
   a trust-base expansion request).

## Out of scope

- Edit older candidates (V0–V52).
- Edit `Reduction.lean` (sprint 045's existing reducer is the
  closing-reducer to use as-is).
- Edit `KorenblumPaper/` (the trusted paper surface is read-only for
  the generator).
- Add a free-floating new axiom or new oracle entry.
- Modify any `Proposals/proposal_*.md` `Status:` field. proposal_001
  remains `rejected`, proposal_002 remains `pending` (deferred),
  proposal_003 remains `pending` (awaiting Alan).
- File a new proposal. If Outcome B obtains, the obstruction note is
  the deliverable; any successor proposal_004 is the *next planner's*
  deliverable per the harness attempt-first protocol, not this
  generator's.
- Write a halt-sibling sprint contract (per the harness policy in
  `sprint_064_canonical_halt_declaration_no_further_halt_siblings.md`).
- Edit `Numerical_Library/`. This sprint does NOT need a new
  oracle — the kernel discharge is purely Lean-side analytical work.
- Run a numerical extremal sweep. Sprints 048–051 already exhausted
  the canonical-extremal cone E0–E3; this sprint's question is
  Lean-derivability on the `Section2Assumptions`-cone, which is a
  strictly different question.

## Time budget

≤ 90 minutes runtime (200–600 line Lean derivation; if the chain
takes longer than that, exit Outcome B with the obstruction note —
generator should not loop indefinitely on a single tactic). Includes
the per-candidate file authorship, the V53 candidate file (Outcome A
or A'), and the Bulletin / Experience / log entries.

## Stop conditions

- **Outcome A**: `lake build` and Evaluator both pass; `c_value >
  7129/20000`; `axioms_used ⊆ {seed}`. Return `STATUS=READY_FOR_EVALUATION`.
- **Outcome A'**: same as A but `c_value = 7129/20000`. Return
  `STATUS=READY_FOR_EVALUATION` with explicit Bulletin/Experience
  c-tie justification.
- **Outcome B**: `Scratch/sprint_066_obstruction.md` written;
  no V53; STATUS=BLOCKED.
- Genuine trust-base ambiguity (e.g. the chain requires a paper
  axiom that doesn't exist and the planner missed it):
  STATUS=BLOCKED_NEEDS_HUMAN with a precise note. This is **rare**
  and should not be the first-resort exit.

## Reference: existing workspace assets

The generator should review (without re-deriving) these
paper-axiom-free / paper-axiom-light primitives before attempting
the chain:

- **Sprint 005**: `sigmaMinus ρ = ρ²·sigmaZeroMinus ρ`
  (paper-axiom-free identity).
- **Sprint 011**: `sigmaZeroMinus_monotone_of_summable` —
  `Z_s ≤ Z_t` for `s ≤ t` (paper-axiom-free).
- **Sprint 027**: `circleGap r = sigmaPlus r − r²·sigmaZeroMinus r`
  (paper-axiom-free derivation of `eq3` direction).
- **Sprint 028**: `sigmaZeroMinus_lower_via_series_convexity`
  (paper-axiom-free derivation of `eq2`-shape).
- **Sprint 032**: `sigmaPlus_monotone_of_summable` — analog of
  sprint 011 on N1 (paper-axiom-free).
- **Sprint 033**: `sigmaPlus_upper_via_series_convexity` —
  cross-radius `sigmaPlus` upper bound (paper-axiom-free).
- **Sprint 040**: `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
  — `diskExcess ≤ c²·Σ⁺(c)`, paper-axiom-free, oracle-cell-free.
- **Sprint 042**: `diskExcess_eq_tsum_via_termwise_integration` —
  `diskExcess = ∑' k coeffPlusGap_k · c^(2k+2)/(k+1)`.
- **Sprint 043**: `diskExcess_eq_tsum_partition_via_series` —
  `diskExcess = Σ⁺_int(c) − Σ⁻_int(c)`.
- **Sprint 044**: `diskExcess_upper_bound_via_tsum_partition_drop_N2`
  — `diskExcess ≤ Σ⁺_int(c)`, paper-axiom-free, oracle-cell-free.
- **Sprint 045**: the closing reducer this sprint targets.

The `paper.eq2` through `paper.eq9` fields are exposed on
`Section2Assumptions` and may be invoked as paper axioms when the
chain calls for them. Avoid `paper.eq10`, `paper.eq11`, `paper.eq12`,
`paper.eq13`, `paper.eq14`, `paper.eq15` — those are the
already-saturated `(15)` channel and contribute nothing new.

## A note on the proposal-003-shaped near-miss

If Direction B's `sigmaPlus ρ ≤ φ(ρ)·Z_ρ` bound at `ρ > c` is the
exact bottleneck (as the planner predicts in the "honest assessment"
section above), the obstruction note should state this precisely:

> The `Section2Assumptions` bundle exposes `paper.eq4`'s `Σ⁺(c) ≤ Σ⁻(c)`
> *only* at the bulk `r < c` regime. To close the chain, we need
> a `Σ⁺(ρ) ≤ φ(c, ρ)·Σ⁻(ρ)` (or stronger per-`k`) bound at
> `ρ > c`. None of the workspace's paper-axiom-free
> infrastructure (sprints 005/011/027/028/032/033/042/043/044)
> produces such a bound. This is exactly the open trust-base
> expansion proposal_003 is asking Alan to approve.

This explicit cross-reference to proposal_003 is what makes the
obstruction note useful as attempt-first evidence — it converts the
"vague structural blockage" of the obstruction into a "precise paper-
axiom-shape needed" specification that strengthens the case for
proposal_003 (or a future proposal_004 with a sharper shape).
