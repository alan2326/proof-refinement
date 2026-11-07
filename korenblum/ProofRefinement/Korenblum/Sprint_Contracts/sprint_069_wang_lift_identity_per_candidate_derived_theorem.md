# Sprint 069: Ship Wang's per-`k` lift identity `(1 − α²)·(‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²` as a per-candidate derived-theorem file `Candidates/V54/LiftIdentity.lean`, then ship V54 tied to V53 with the new building block exercised in a side lemma

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V53.lean` (current high-water mark, `c_value = 7129/20000 = 0.35645` via the literal-(15) HP oracle channel; first workspace per-candidate derived-theorem file `Candidates/V53/ThetaStep.lean` shipped sprint 068)
**Target file**: `Candidates/V54.lean` PLUS supporting per-candidate derived-theorem file `Candidates/V54/LiftIdentity.lean`
**Direction**: section2-proof + analytic-Lean derivation — the FIRST attempt to ship Wang's per-`k` lift identity as a Lean theorem (no prior sprint has touched this identity at the per-`k` level; the brief lines 137–141 of `AGENT_BRIEF.md` explicitly name it as a per-candidate derived-theorem candidate)

## Goal

Ship the complex-algebraic identity

```text
(1 − α²) · (‖b k‖² − ‖a k‖²)
   = ‖b k − (α : ℂ)·(a k)‖² − ‖a k − (α : ℂ)·(b k)‖²
                                          (LIFT_IDENTITY)
```

as a Lean `theorem` (not an `axiom`) in a per-candidate derived-theorem file
`Candidates/V54/LiftIdentity.lean`, valid for every `k : ℕ`, every
`a, b : ℕ → ℂ`, and every real scalar `α ∈ ℝ`. **No new axiom. No oracle.
No edit to `KorenblumPaper/`. No edit to `Reduction.lean`. No edit to
`lemma.toml`** beyond a one-line `[import_policy].allowed_exact` extension
mirroring sprint 068's pattern for the new module path.

This is a pure complex-algebraic identity: expand both sides via
`Complex.normSq` / `‖z‖² = z.re² + z.im²` (or via the polarization
`‖z‖² = (z * conj z).re`) and close by `ring` after rewriting in terms of
real and imaginary components. Per the brief lines 154–171, this is well
within scope (algebraic identity on complex sequences). The expected proof
body is **30–80 lines of Lean** plus standard imports.

Then ship `Candidates/V54.lean` as a V53-tied candidate (same
`c_value = 7129/20000`, same `valid_of_eq15`-via-`hEq15_oracle_certified_hp_35645`
discharge) that imports `Candidates/V54/LiftIdentity.lean` and exercises the
new theorem in a side lemma `v54_lift_identity_compiles_at_seed_witness`.
This forces the elaborator to verify the new theorem is non-vacuous and
reusable, and continues the sprint 068 institutional pattern that the
unstuck plan §5 / `AGENT_BRIEF.md` lines 154–204 establish.

The fixed quantitative target is `c_value = 7129/20000 = 0.35645` (V53's
ceiling). This sprint deliberately does NOT push `c`; it pursues the
**structural** advance of materializing the per-`k` cross-coupling identity
as a reusable Lean theorem. This is the second per-candidate derived-theorem
file in the workspace; the institutional pattern is now exercised twice.

## Why

The brief at `AGENT_BRIEF.md` lines 137–141 explicitly names three
un-numbered Wang intermediate algebraic steps as candidate per-candidate
derived-theorem files:

> - the lift identity `(1 − a²)(|b_k|² − |a_k|²) = |b_k − a·a_k|² − |a_k − a·b_k|²`,
> - per-`k` cross-coupling positivity from Wang's `|f| ≤ |g|` boundary hypothesis,
> - boundary L² comparison from `|f| ≤ |g|` via Wang Lemma 2.

Sprint 068 shipped THETA_STEP (`(1+Λ)·Σ⁻ ≤ Λ·Σ⁺`) as the first such file.
Sprint 068's Phase B falsified the `(a, b)`-independent closing-reducer
composition of THETA_STEP, confirming the bulletin's three-sprint exhaustion
finding (sprints 065/066/067) that closed-form `(a, b)`-independent kernels
cannot push `c` past the literal-(15) crossover at `c ≈ 0.35635`. The next
move per the brief's analytical-novelty disposition is to materialise the
**per-`k` cross-coupling content** as a Lean theorem — without expanding the
trust surface.

Why the lift identity is the right next building block:

1. **It is the per-`k` content that proposal_003 was about.** proposal_003
   (now `superseded`) requested a paper-side per-`k` cross-coupling
   enrichment of `Σ⁺(c) ≤ Σ⁻(c)` (Wang 2025 page 1211 eq (4)'s second
   conjunct sharpened by the per-`k` consequence of `|f(z)| ≤ |g(z)|` on
   `|z| = c`). The lift identity is the ALGEBRAIC step that the per-`k`
   consequence is BUILT FROM in Wang's published proof: combining the
   identity with Wang Lemma 2 gives the per-`k` boundary `L²` comparison
   `‖a k − α·b k‖² ≤ ‖b k − α·a k‖²` that yields per-`k` strict drop.
   Materialising the identity as a Lean theorem is therefore the FIRST
   structural step toward a paper-faithful Lean derivation of
   proposal_003's content **without** any axiom expansion.

2. **It is paper-axiom-free.** The identity holds for every `(a, b, α)`
   in `(ℕ → ℂ) × (ℕ → ℂ) × ℝ`. No `Section2Assumptions` field is needed.
   The proof is one or two lines of `ring`-arithmetic after expanding
   `‖·‖²` via `Complex.normSq` or the polarization
   `‖z‖² = (z * starRingEnd z).re`. This is strictly smaller than
   sprint 068's THETA_STEP (which needed `eq3 + eq8 + eq9` plus sprint 005),
   so it is a strictly smaller structural risk.

3. **It is reusable across many future candidates.** Any future closing
   reducer that wants per-`k` precision on the disk side (e.g. composing
   sprint 044's `diskExcess ≤ Σ⁺_int(c)` with a per-`k` strict drop on
   the annulus side) will need this identity. Shipping it now makes that
   reuse cheap (one import of `ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`
   per future consumer).

4. **It satisfies the brief lines 192–195 default disposition.** "If a
   derived theorem is genuinely useful across multiple future candidates,
   propose hoisting it." The brief explicitly normalises shipping the
   identity per-candidate first; hoisting is a future sprint.

5. **It is a sensible second exercise of the institutional pattern.** Sprint
   068 was the first per-candidate derived-theorem file. The pattern is
   now operationally validated. Shipping a SECOND per-candidate derived
   theorem in a structurally-distinct register (pure complex algebra on
   `ℕ → ℂ` sequences vs. THETA_STEP's chain of paper equations and series
   identities) confirms the pattern generalises and stress-tests the
   `[import_policy].allowed_exact` registration mechanism.

## Roadmap to `c > 0.3554`

> *(Bulletin Step 1 mandates this section even for c-tying sprints.)*

1. **Which existing closing reducer is the cheapest path to `c > 0.3554`?**
   None of the existing closing reducers in `Reduction.lean` admits a
   discharge above `c ≈ 0.35635` without a structural input that is not
   currently in `Section2Assumptions` (per sprints 048/050/051/065/066/067/068
   cumulative evidence). The cheapest path *through Lean* is now to keep
   accumulating per-candidate Lean theorems realizing Wang's un-numbered
   intermediate algebraic steps, until enough is accumulated to derive a
   per-`k` strict drop bound that the existing sprint 045 closing reducer
   can consume.

2. **What is the numerical kernel?** Phase A: there is no numerical kernel
   — the lift identity is an algebraic identity. Phase B (if reached): not
   applicable; the lift identity by itself does not compose into a closing
   reducer (it is one ingredient out of three named in the brief
   lines 137–141; the other two — per-`k` cross-coupling positivity and
   Wang Lemma 2 — are deferred to future sprints).

3. **Does the kernel hold with margin at some `c > 0.3554`?** N/A
   (algebraic identity, not a numerical kernel).

4. **What is the trust gap between the Scratch witness and a Lean proof?**
   Zero. The lift identity is a pure complex-algebraic identity that
   `ring` (after `‖·‖²` expansion) closes uniformly in `(a, b, α, k)`. No
   oracle, no `Numerical_Library`, no Scratch.

5. **Decide between two routes per gap, for each non-closed-form cell.**
   No cells: pure Lean theorem.

6. **What does the c-pushing candidate look like?** This sprint does NOT
   push `c`. V54 ships at `c_value = 7129/20000 = 0.35645` (ties V53). The
   c-pushing candidate beyond V53 remains deferred. This sprint contributes
   the second of three (per-brief-named) per-candidate Lean theorems that
   together with future composition work would unblock a paper-axiom-free
   per-`k` strict drop bound of the kind proposal_003 requested.

## Three candidate sprint shapes considered (per Planner ultrathink rule)

The Planner enumerated multiple structurally distinct sprint shapes before
choosing this one. Three of them, with strongest objections:

1. **Hoist `Candidates/V53/ThetaStep.lean` to `Proof/ThetaStep.lean`
   (shared module).** The brief lines 192–195 say this should be done in a
   sprint contract once a derived theorem is "genuinely useful across
   multiple future candidates." **Strongest objection**: only V53 currently
   uses THETA_STEP. No future sprint contract has yet been queued that
   composes THETA_STEP. Hoisting is premature; the brief's default is
   per-candidate-first. Demoted.

2. **Compose THETA_STEP with sprint 047's `annulusExcess` per-`k`
   partition equality to derive a per-`k` × per-`k` annulus lower bound
   `annulusExcess ≥ ∫_{c..1} 2ρ/(1+Λ)·Σ⁺(ρ) dρ` and attempt a closing
   reducer.** **Strongest objection**: the resulting kernel termwise-reduces
   at k=0 to KERNEL_68 = `c² ≤ ∫_{c..1} 2ρ/(1+Λ) dρ`, which sprint 068's
   Phase B numerically falsified at every probed `c ≥ 0.355` with margin
   ≈ −0.11. THETA_STEP composed with `Σ⁺` lower-monotonicity (which sprint
   032 does NOT supply — it goes the other direction) is precisely the
   chain that sprint 067/068 already exhausted. Re-attempting it without
   a stronger analytic input produces a fifth attempt-first BLOCKED row,
   not a c-push and not a structural advance. Demoted.

3. **Lift identity as a per-candidate derived theorem.** **Chosen.** The
   lift identity is brief-explicitly named (`AGENT_BRIEF.md` lines 137–138),
   structurally orthogonal to THETA_STEP (pure complex algebra on
   `ℕ → ℂ` sequences vs. paper-equation chain), paper-axiom-free, and
   the FIRST step toward a paper-faithful Lean realization of proposal_003's
   per-`k` cross-coupling content (with zero trust expansion). The proof
   is 30–80 lines (`Complex.normSq` expansion + `ring`); within
   generator-capability per brief lines 154–171. Shipping this confirms
   the institutional pattern from sprint 068 generalises to a structurally
   distinct register. Future sprints can compose this with Wang Lemma 2
   and the boundary `L²` identity to derive per-`k` strict drop
   inequalities — the ingredients proposal_003 was deferred for.

## Concrete edits expected

### Phase A (deliverable, must succeed)

1. **NEW**: `ProofRefinement/Korenblum/Candidates/V54/LiftIdentity.lean`.

   Contains theorems (no axioms, no new `Section2Assumptions` fields):

   a. The raw lift identity:
      ```lean
      theorem lift_identity_per_k
          (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
          (1 - α ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
            = ‖b k - (α : ℂ) * a k‖ ^ 2 - ‖a k - (α : ℂ) * b k‖ ^ 2 := by
        -- Expand via `Complex.normSq` or the polarization identity
        -- `‖z‖² = (z * conj z).re`, then close by `ring` /
        -- `nlinarith`-friendly real-component arithmetic.
        ...
      ```
      Proof sketch (30–80 lines):
      - Rewrite `‖z‖² = z.re ^ 2 + z.im ^ 2` (via `Complex.normSq_eq_abs` /
        `Complex.sq_abs` / `Complex.normSq` definitions, or via
        `@Complex.norm_def` and `Real.sq_sqrt`).
      - Alternatively, use `Complex.normSq_sub`,
        `Complex.normSq_mul`, `Complex.normSq_real_smul`, etc., to
        reduce both sides to polynomial expressions in
        `(a k).re, (a k).im, (b k).re, (b k).im, α`.
      - Close by `ring`.

      *Honest disclosure*: the precise Mathlib lemma names for the
      `‖·‖²` expansion may be `Complex.sq_abs` /
      `Complex.normSq_apply` / `RCLike.norm_sq_eq` — the generator
      should pick whichever is most ergonomic; the identity holds
      uniformly so any working route is acceptable.

   b. (OPTIONAL, if the proof of (a) extracts a useful intermediate)
      A real-valued component form expressing both sides in
      `(a k).re, (a k).im, (b k).re, (b k).im, α`:
      ```lean
      theorem lift_identity_per_k_re_im
          (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
          (1 - α ^ 2) *
              ( ((b k).re ^ 2 + (b k).im ^ 2)
              - ((a k).re ^ 2 + (a k).im ^ 2) )
            = ( ((b k).re - α * (a k).re) ^ 2
              + ((b k).im - α * (a k).im) ^ 2 )
            - ( ((a k).re - α * (b k).re) ^ 2
              + ((a k).im - α * (b k).im) ^ 2 ) := by
        ring
      ```
      This is the literal `ring`-form. If the generator wants
      `lift_identity_per_k` to factor through this real form, it
      can; otherwise this lemma can be omitted.

   c. (OPTIONAL, for downstream consumability) A pointwise rearrangement
      of (a):
      ```lean
      theorem lift_identity_per_k_rearranged
          (a b : ℕ → ℂ) (α : ℝ) (hα : α ^ 2 < 1) (k : ℕ) :
          ‖b k‖ ^ 2 - ‖a k‖ ^ 2 =
            (‖b k - (α : ℂ) * a k‖ ^ 2 -
             ‖a k - (α : ℂ) * b k‖ ^ 2) / (1 - α ^ 2) := by
        have h1 : 1 - α ^ 2 ≠ 0 := by nlinarith [hα]
        have hraw := lift_identity_per_k a b α k
        field_simp
        linarith [hraw]
      ```
      The `α^2 < 1` hypothesis matches Wang's regime (where `α(ρ)`
      is a contraction lift coefficient). This is optional: if (a) is
      enough, omit (c).

2. **NEW**: `ProofRefinement/Korenblum/Candidates/V54.lean`.

   Imports `ProofRefinement.Korenblum.Proof.Main` plus
   `ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`. Defines:

   - `c_value : ℝ := 35645 / 100000` (same as V53/V52).
   - `c_value_pos`, `c_value_lt_one`: identical to V53.
   - `eq15_lower_bound : ℝ := 1`: identical to V53.
   - `axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value`:
     identical to V53's. (This is the same axiom as V53's; the candidate
     namespace differs so the axiom is technically a fresh declaration in
     the V54 namespace, but its oracle wiring uses the same registered
     `eq15_certified_at_hp_35645` row in `lemma.toml`.)
   - A side lemma `v54_lift_identity_compiles_at_seed_witness` that
     instantiates `LiftIdentity.lift_identity_per_k` at concrete arguments
     to force elaboration:
     ```lean
     theorem v54_lift_identity_compiles_at_seed_witness
         (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
         (1 - α ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
           = ‖b k - (α : ℂ) * a k‖ ^ 2 - ‖a k - (α : ℂ) * b k‖ ^ 2 :=
       LiftIdentity.lift_identity_per_k a b α k
     ```
     This is a **statement-level** non-vacuity check, not a witness
     construction (sprint 068's pattern). The elaborator's acceptance
     of this lemma confirms `Candidates/V54/LiftIdentity.lean` is
     non-vacuous and reusable.
   - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
     proved via `valid_of_eq15 c_value_pos c_value_lt_one
     (fun {K} => hEq15_oracle_certified_hp_35645 K)`. Identical
     discharge to V53.

3. **`lemma.toml`**: ONE-LINE edit. Add
   `"ProofRefinement.Korenblum.Candidates.V54.LiftIdentity"` to
   `[import_policy].allowed_exact` (mirroring sprint 068's pattern for
   `Candidates.V53.ThetaStep`). Optionally also add
   `"ProofRefinement.Korenblum.Candidates.V54"` to the same list if the
   evaluator does not already permit candidate files via prefix match.
   **No new `[seed_axioms].allowed` entry.** **No new `[[oracles]]` entry.**
   The same `hEq15_oracle_certified_hp_35645` axiom V53 declares is
   re-declared in the V54 namespace; the existing
   `eq15_certified_at_hp_35645` oracle row in `[[oracles]]` covers both
   declarations (V53 and V54) by axiom-name pattern, mirroring the
   sprint 057/059/068 pattern.

   *Honest disclosure*: if the evaluator's `[[oracles]]` `axiom` field
   is namespace-qualified (e.g. literally
   `ProofRefinement.Korenblum.Candidates.V53.hEq15_oracle_certified_hp_35645`),
   the generator must add a sibling row for V54 with the V54-namespaced
   axiom name pointing at the same `oracle_fn`. If the field is bare
   (`hEq15_oracle_certified_hp_35645`), no edit is needed. The generator
   inspects `lemma.toml` to determine which case applies and edits
   accordingly. This is a **wiring-level edit** in either case (no new
   oracle, no new wrapper function); the generator records which case
   applied in `Experience.md`.

4. **`Bulletin.md`**: append one `## Recent events` row recording sprint
   069's outcome.

5. **`Experience.md`**: append one entry per the Bulletin honesty rules
   (lines 139–161): what was attempted, dead ends if any, current
   obstacle, next move, trust-surface accounting.

### No Phase B

Unlike sprint 068, sprint 069 has **no Phase B** (no closing-reducer
composition attempt). The lift identity by itself does not compose into a
closing reducer — Wang's published derivation needs the lift identity
**plus** the boundary `L²` comparison from `|f| ≤ |g|` plus Wang Lemma 2's
expansion. Those two are explicitly named in the brief lines 139–141 as
candidates for FUTURE per-candidate derived-theorem files; sprint 069
ships only the lift identity. Composing it into a closing reducer is
deferred to a future sprint that has all three building blocks.

This is intentional: the bulletin's three-sprint exhaustion synthesis
plus sprint 068's Phase B falsification settle that `(a, b)`-independent
closing-reducer composition is exhausted. Adding a fifth attempt-first
BLOCKED row is not a productive use of generator budget. The structural
advance of sprint 069 is the new reusable Lean theorem; that is enough
for one bounded sprint.

## Acceptance criteria

### Outcome A — Phase A succeeds, V54 ships at V53's c

1. `lake build ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`
   succeeds. The file contains `theorem lift_identity_per_k` (and
   optionally `theorem lift_identity_per_k_re_im` and/or
   `theorem lift_identity_per_k_rearranged`) as `theorem`s (no `axiom`s,
   no `sorry`s).
2. `lake build ProofRefinement.Korenblum.Candidates.V54` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V54.lean` succeeds with
   `pass: true`.
4. The evaluator's `axioms_used` for V54 is `⊆ {seed} ∪
   {hEq15_oracle_certified_hp_35645}`, byte-for-byte identical to V53's
   axiom envelope. **No new free-floating axioms.** **No new oracles.**
   The only `lemma.toml` edit is the import-policy line for the new
   `LiftIdentity` module path (and optionally a wiring sibling row in
   `[[oracles]]` for the V54-namespaced eq15 axiom if the evaluator's
   `axiom` field is namespace-qualified).
5. The evaluator's `score` is exactly `7129/20000` (NOT a c-push;
   acceptance under Outcome A requires the score-tie justification is
   the lift-identity advance, recorded in `Experience.md` per the
   Bulletin honesty rules).
6. The lift-identity theorems' axiom closures (verifiable separately
   via `#print axioms LiftIdentity.lift_identity_per_k` if needed) are
   `⊆ {seed}`. **No `eq15` oracle leakage** into the lift-identity
   theorem closure (the lift identity is paper-axiom-free of `eq15`,
   `eq8`, `eq9`, sprint 005, sprint 027 — a strictly smaller dependency
   set than THETA_STEP).
7. The side lemma `v54_lift_identity_compiles_at_seed_witness` in
   `Candidates/V54.lean` elaborates and confirms non-vacuity.

### Outcome B — Phase A blocks (lift identity cannot be derived in Lean)

If the generator cannot complete Phase A in a reasonable budget (e.g.
the Mathlib `‖·‖²` API does not expose a usable normalisation that
`ring` can close, or the `(α : ℂ)` coercion unifies in a way that breaks
the `ring`-arithmetic):

1. Write `Scratch/sprint_069_obstruction.md` documenting:
   - Which exact intermediate goal blocked the proof (e.g. "after
     rewriting `‖b k - (α : ℂ) * a k‖^2` via `Complex.normSq_sub` and
     `Complex.normSq_mul`, the residual `ring` goal contains
     `(α : ℂ).re * (a k).re + (α : ℂ).im * (a k).im` which `ring`
     cannot reduce to `α * (a k).re` because the `(α : ℂ).im = 0`
     side-condition is not in the goal context").
   - The Lean tactic transcript at the blocking goal (use `lean_goal`
     output or `#check`-traced state).
   - Whether the obstruction is missing-Mathlib-API (legitimate request
     for a successor sprint that imports a different Mathlib module
     family, e.g. `Mathlib.Analysis.RCLike.Basic`) or
     unfamiliar-tactic-chain (gap-in-attack — record as a request for
     a successor sprint to retry with a different proof strategy, e.g.
     polarization vs. real-component expansion).
   - A closed-form algebraic identity (verifiable by hand or by SymPy)
     confirming the obstruction is a tactic-level issue, NOT a
     mathematical issue. This is essential — the lift identity holds
     for every `(a, b, α, k)`, so the obstruction MUST be tactical.
   - A recommendation to the next planner: which Mathlib lemma family
     to try next (`Complex.normSq_apply`, `Complex.sq_abs`,
     `RCLike.normSq_apply`, `Complex.norm_eq_abs`, etc.).

2. Do NOT ship `Candidates/V54.lean`. Do NOT edit `lemma.toml`. Do NOT
   register any oracle. Do NOT modify `KorenblumPaper/`.

3. Append a Bulletin row recording the BLOCK and a forward-looking
   Experience.md entry naming the next sprint's recommended attack.

### Outcome C — Phase A succeeds with a strictly smaller theorem set

If the generator succeeds at `lift_identity_per_k` but the optional
companion lemmas (b, c) prove harder than budgeted, ship just (a) plus the
`Candidates/V54.lean` exercising it. Acceptance criteria 1–7 of Outcome A
apply with the smaller theorem set. The next planner can request the
companions in a successor sprint if needed.

## Out of scope

- Edit older candidates (`V0..V53`).
- Change the final theorem statement (`korenblum_constant_search :
  ValidKorenblumBound c_value`).
- Add a free-floating new axiom (the only axiom V54 declares is the same
  `hEq15_oracle_certified_hp_35645` shape V53 declares; this is permitted
  by the existing oracle registration, NOT a new axiom).
- Edit `KorenblumPaper/` (the paper surface is read-only for the
  generator).
- Hoist `Candidates/V53/ThetaStep.lean` to `Proof/`. The brief lines
  192–195 require a separate sprint contract for hoists.
- File a new `Proposals/proposal_004_*.md`. The four-condition guide in
  the planner agent definition is not satisfied: the lift identity is
  Lean-derivable in 30–80 lines (not "thousands of lines"), so the
  default disposition is "prove it in Lean," not "file a proposal."
  Sprint 069 IS the prove-it-in-Lean sprint.
- Compose the lift identity with Wang Lemma 2 or the boundary `L²`
  comparison. Those are FUTURE per-candidate derived-theorem files; sprint
  069 ships only the lift identity.
- Push `c` above `7129/20000`. This is a c-tying sprint by design (per the
  bulletin's three-sprint exhaustion synthesis plus sprint 068's Phase B
  falsification: the closed-form `(a, b)`-independent kernel space is
  exhausted; advancing `c` further requires per-`k` content that this
  sprint contributes a building block toward but does not by itself
  realize).

## Time budget

≤ 60 minutes runtime for Phase A.

The proof of `lift_identity_per_k` is a single complex-algebraic identity
that closes by `Complex.normSq`-expansion plus `ring`. Mathlib provides
multiple approachable APIs (`Complex.normSq_apply`, `Complex.sq_abs`,
`Complex.norm_def`, `RCLike.normSq_apply`, etc.); the generator picks
whichever is most ergonomic. If 30 minutes pass without a successful
closure on one attack, the generator pivots to a different Mathlib lemma
family rather than continuing to chip away — the identity is true and
provable, the question is which lemma family unlocks the shortest proof
(per brief lines 144–149).

## Stop conditions

- Acceptance criteria for Outcome A or Outcome C met: `STATUS=READY_FOR_EVALUATION`
- Acceptance criteria for Outcome B met (obstruction note shipped, no
  Lean candidate): `STATUS=BLOCKED`
- Generator cannot complete the obstruction note within the time budget:
  `STATUS=BLOCKED_NEEDS_HUMAN`
