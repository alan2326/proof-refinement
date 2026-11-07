# Sprint 073: Integrated lift identity over `[0, c]` shipping `(1−α²)·diskExcess` as a per-`k` series, plus a non-trivial closed-form upper bound on `diskExcess` at `α = c`, as a per-candidate derived-theorem file under `Candidates/V57/`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V56.lean` (high-water mark; `c_value = 7129/20000 = 0.35645`; per-mode τ-window closing reducer `valid_of_perMode_tau_window_eq8_eq9` shipped in `Proof/Reduction.lean` by sprint 071)
**Target file**: `Candidates/V57.lean` (V56-tied via `valid_of_eq15` discharged by `hEq15_oracle_certified_hp_35645`), plus `Candidates/V57/DiskExcessLiftIntegrated.lean` (new per-candidate derived-theorem file)
**Direction**: section2-proof + analytic-Lean derivation (per-candidate derived-theorem file in a structurally novel register: integrated lift identity over the disk, producing a per-`k` upper bound on `diskExcess`)

## Supersedes

This contract supersedes the previously-queued, never-executed
`sprint_072_multi_window_tau_partition_closing_reducer.md`. Sprint 072
proposed a multi-window τ-partition reducer composing sprint 071's
single-window per-mode worker `m` times. **Sprint 071's own Phase 0 data
forecast that any multi-window per-mode-via-eq8+eq9 chain has total mass
ε ≤ 0.015 across `j*=1..5` τ-windows at every probed `c ≥ 0.357`, three
orders of magnitude below the mass-1 target.** Sprint 072 would have
shipped a structural-plumbing reducer with zero numerical reach above
V56.

The substantive obstruction sprint 071 identified is structural: the
per-mode-via-eq8+eq9 axis introduces `paperLambda K c ρ` in the
denominator of every per-window scalar integrand, and `paperLambda` is
large on the entire annulus `(c, 1)` (Λ ≥ 35 throughout), which suppresses
every per-window mass below 1% of unity. Adding more windows does not
overcome a per-window kernel that is uniformly `O(10⁻³)`.

The structurally distinct response, taken in this sprint: route the
**disk side** through V54's lift identity + V55's series bridge instead
of through `eq3 + eq4`. The integrated lift identity over `[0, c]`
produces a `(1−α²)·diskExcess` formula that decomposes per-`k` and is
**Λ-free** — no `eq8`, no `eq9`, no `paperLambda` anywhere. The
resulting per-`k` upper bound is a structurally novel disk-side bound
that future closing-reducer sprints can compose with annulus-side
machinery on a different chain than the per-mode-via-eq8+eq9 chain
sprint 071 ships.

## Goal

Ship a per-candidate derived-theorem file
`Candidates/V57/DiskExcessLiftIntegrated.lean` with **two named Lean
theorems** (no `axiom`s, no `sorry`s), then ship `Candidates/V57.lean`
at `c_value = 7129/20000 = 0.35645` (V56-tied via the existing eq15
oracle):

### Theorem 1: `diskExcess_lift_identity_at_alpha`

The integrated lift identity over `[0, c]` at any `α ∈ ℝ` with
`α² < 1`. Schematically:

```text
(1 − α²) · diskExcess (circleGap a b) c
  = ∑' k : ℕ, ‖a k − (α : ℂ) · b k‖² · c^(2k+2) / (k + 1)
  − ∑' k : ℕ, ‖b k − (α : ℂ) · a k‖² · c^(2k+2) / (k + 1)
```

This composes V54's `lift_identity_per_k` (sprint 069) and V55's
`liftSeriesBridge_main` (sprint 070) with the polar-Jacobian
integration `∫_0^c 2r · r^(2k) dr = c^(2k+2)/(k+1)` and `tsum`–integral
interchange. Hypotheses: `α² < 1`, `0 ≤ c`, summability of the four
series under their disk weights `c^(2k+2)/(k+1)` (these are the natural
Bergman-disk summability hypotheses already used by
`OneModePaperBridge.sigmaReduction_of_series` and equivalent to
`diskWeightedSeq` summability for the relevant sequences).

### Theorem 2: `diskExcess_upper_bound_via_lift_at_alpha`

A non-trivial **closed-form upper bound** on `diskExcess` from
Theorem 1 by dropping the (non-negative) `‖b k − α·a k‖²` term:

```text
(1 − α²) · diskExcess (circleGap a b) c
  ≤ ∑' k : ℕ, ‖a k − (α : ℂ) · b k‖² · c^(2k+2) / (k + 1)
```

Hypotheses inherit from Theorem 1, plus `0 < 1 − α²` (i.e. `α² < 1`
strictly).

This is structurally novel: the workspace's existing disk-side bounds
in `OneModePaperBridge.innerSeriesExcess_le_supKernel_mul_sigmaMinus`
all multiply by `OneModeSup.supKernel c ρ * sigmaMinus a b ρ` (which is
not Λ-free once you compose with eq8+eq9 to convert `sigmaMinus(ρ)` to
a `circleGap` density). Theorem 2 produces a Λ-free disk-side bound
that pays per-`k`. The upper bound is a `tsum` over `k` of
`(‖a k − α·b k‖² · c^(2k+2)/(k+1))`, which **does not divide by Λ**.

### Optional Theorem 3 (nice-to-have, not required for STATUS=READY): `diskExcess_le_simple_at_alpha_eq_c`

Specialise Theorem 2 to `α = c` (so `α² = c² < 1` for `c ∈ (0, 1)`),
and apply the elementary triangle/Cauchy bound `‖a k − c·b k‖² ≤
2·(‖a k‖² + c²·‖b k‖²)` per-`k`, summed against `c^(2k+2)/(k+1)`:

```text
diskExcess (circleGap a b) c
  ≤ (2 / (1 − c²)) · ∑' k, (‖a k‖² + c² · ‖b k‖²) · c^(2k+2) / (k + 1)
  = (2 / (1 − c²)) · (diskWeightedSeq (fun k => ‖a k‖²) c
                     + c² · diskWeightedSeq (fun k => ‖b k‖²) c)
```

This is a closed-form upper bound on `diskExcess` purely in terms of
disk-weighted sums of `‖a k‖²` and `‖b k‖²` — i.e. in terms of
`Σ⁰⁺(c)`-style coefficient sums. It is the structural sibling of Wang's
eq (5)/(6) but routes through the lift identity at the `c=ρ` anchor
point rather than through Wang's eq (3)/(4) chain.

Theorem 3 is OPTIONAL — its proof requires an extra Cauchy/triangle
manipulation (`‖a − c·b‖² ≤ (‖a‖ + c·‖b‖)² ≤ 2(‖a‖² + c²·‖b‖²)`,
which is `nlinarith` / `polyrith` with `0 ≤ c < 1` and `‖·‖ ≥ 0`).
**Ship Theorem 3 if Phase A budget allows; if not, the sprint
succeeds with Theorems 1 + 2 alone.** Theorem 1 alone is the
core structural advance.

## Why

### Cumulative status of the 2026-05-04 priority directive

Sprints 065–068 falsified four closed-form `(a, b)`-independent scalar
kernels (`Σ⁺_int(c) ≤ Σ⁺_int_ann − Σ⁻_int_ann`, sprint 045's kernel,
THETA_STEP, THETA_STEP composed with sprint 040). Sprint 071 falsified
the per-mode τ-window kernel at single-window granularity. **Sprint
072's now-superseded contract acknowledges that multi-window won't
help** — its own Phase 0 forecast (Experience.md sprint 071, lines
2891–2913) computes total mass ≤ 0.015 at every `c ≥ 0.357`. The
per-mode-via-eq8+eq9 register is exhausted as a c-push channel.

Sprints 068/069/070 shipped three structurally novel per-candidate
derived-theorem files (V53/THETA_STEP, V54/LiftIdentity,
V55/LiftSeriesBridge), each in a distinct register (paper-equation
chain, complex algebra, `tsum`-level rearrangement). Sprint 071 shipped
the first per-mode τ-window closing reducer in `Reduction.lean`.

Sprint 073 ships the **fourth per-candidate derived-theorem file**, in
the structurally distinct register of **integrated lift identity over
the disk**. The novelty axis: existing per-candidate files V54/V55
operate at the per-`k` and series level; V57 operates at the
**integrated-over-the-disk** level, bridging V54+V55 to the
`AnnulusIntegralReduction.annulusSlice` representation already used
throughout `Reduction.lean`.

### Why this register is genuinely new

Every existing closing reducer in `Proof/Reduction.lean` produces a
disk-side bound of the form

```text
diskExcess ≤ K(c, ρ) · sigmaSomething(ρ)   (single ρ-anchor)
```

or

```text
mass · diskExcess ≤ annulusSlice circleGap ρ₁ ρ₂   (per-window mass-times-excess)
```

The anchor or window is a **radial parameter** ρ, and the bound is
read off `eq3+eq4` (sprint 014's branch), `eq5/eq6` (sprints 015/016's
chain), or `eq8+eq9` (sprint 045's chain). All of them divide by
`paperLambda` somewhere in the chain (because converting any
σ-density to circleGap via eq8+eq9 introduces Λ).

Theorem 2 of this sprint produces a disk-side upper bound that is
**Λ-free**. Its proof draws on V54's lift identity (a per-`k` complex
algebra identity, no paper axioms beyond `ℂ`-norm machinery) and V55's
series bridge (a `tsum`-level rearrangement, no paper axioms beyond
the `def`-level unfolding of `liftGapSeries` / `circleGapSeries`).
**Neither V54 nor V55 invokes `eq8`, `eq9`, or `paperLambda`.** So
Theorem 2's upper bound on `diskExcess` is the workspace's first
disk-side bound on `circleGap`-integrated-over-`[0, c]` that is
demonstrably Λ-free.

### Compositional value

The integrated lift identity is a **structural prerequisite** for the
per-`k` cross-coupling positivity argument that proposal_003 named
(`Σ⁻(c)/Σ⁺(c) ≤ θ(c) < 1` on canonical extremals — sprint 060 Phase B's
empirical witness θ_emp ≤ 0.857). The cross-coupling chain Wang uses
goes through **boundary L² Parseval at radius ρ** (which is "Wang
Lemma 2" proper) plus the lift identity at `α² < 1`. Theorem 2 ships
the lift-identity half of that chain, in integrated form. A future
sprint may attempt the boundary L² half, or use Theorem 2 directly
combined with V53's THETA_STEP and a per-`k` annulus-side bound to
close a `c > V52` reducer.

If Theorem 3 also ships, it produces the closed-form bound

```text
diskExcess ≤ (2/(1-c²)) · (diskWeightedSeq (‖a·‖²) c + c² · diskWeightedSeq (‖b·‖²) c)
```

which is in terms of `diskWeightedSeq (‖·‖²)` quantities — a smooth
`Σ⁰⁺`-style sum that admits straightforward annulus-side comparison
via the existing series identities (sprint 005's
`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` plus eq8/eq9 on the
annulus). The combination is a **future closing-reducer candidate**
that does not divide by `paperLambda` on the disk side — flipping the
constraint that has falsified every closed-form `(a, b)`-independent
kernel since sprint 048.

### Bounded Lean cost

The per-candidate file is forecast at **150–250 lines**, comparable to
V55's `liftSeriesBridge_main` (~80 lines) plus V54's
`lift_identity_per_k` (~10 lines) machinery. Specifically:

- Theorem 1 proof body: integrate the per-`k` identity termwise
  using `intervalIntegral.integral_tsum` (or the symmetric variant
  `MeasureTheory.tsum_integral`) under summability hypotheses; close
  the per-`k` factor `∫_0^c 2r · r^(2k) dr = c^(2k+2)/(k+1)` via
  `intervalIntegral.integral_pow` or direct `norm_num`/`ring`. Estimated
  **80–150 lines**.
- Theorem 2 proof body: from Theorem 1 by `tsum_nonneg` on
  `‖b k − α·a k‖² · c^(2k+2)/(k+1) ≥ 0` and `sub_le_self` /
  `tsum_sub_le_tsum_left`. Estimated **20–40 lines**.
- Theorem 3 (optional): `tsum_le_tsum` on the per-`k` Cauchy bound
  `‖a k − α·b k‖² ≤ 2(‖a k‖² + α²·‖b k‖²)` proved by `nlinarith`
  with `‖·‖ ≥ 0` and `0 ≤ α²`. Estimated **30–60 lines**.

Total ship target: **130–250 lines** for the per-candidate file, plus
~80 lines for V57.lean (V56-tied template) and the side lemma
`v57_lift_integrated_compiles_at_seed_witness` exercising Theorem 1's
signature (statement-level non-vacuity check, mirrors V55's pattern).

The proof is **bounded** — it composes V54+V55 plus a single
Mathlib theorem (`intervalIntegral.integral_tsum` or
`MeasureTheory.tsum_intervalIntegral_eq_intervalIntegral_tsum` —
the generator should grep for the exact name available in Mathlib
v4.28.0 and pick whichever variant is most ergonomic).

### Why no Phase 0

Theorems 1 and 2 are **identities and an algebraic upper bound**, not
numerical kernels. There is no integral-mass-≥-1 hypothesis to verify
numerically — Theorem 1 is `(1-α²)·diskExcess = (per-k expansion)` as
an equality, Theorem 2 is `(1-α²)·diskExcess ≤ (positive per-k sum)`
which is non-vacuously satisfied because the RHS is non-negative and
the LHS has no a-priori sign constraint. The compositional value is
*not* in any specific numerical witness — it is in the Λ-free per-`k`
structure that future sprints can attack.

V57 itself ties V56 via `valid_of_eq15` discharged by
`hEq15_oracle_certified_hp_35645` — byte-for-byte identical axiom
envelope to V56/V55/V54/V53/V52. **No new axioms, no new oracles,
no Phase 0 required.**

### Why this is not proposal_004 territory

Per the planner brief's four-condition guide:

1. **"Tried hard and failed"**: the integrated lift identity has not
   been attempted. Per the brief, queue the attempt sprint first; do
   not file a proposal for an unattempted derivation.
2. **"Genuinely large derivation cost"**: the proof is forecast 150–250
   lines, well within bounded-Generator-session capacity.
3. **"Strong reason to believe correct"**: the identity is a
   straightforward integration of V54's per-`k` identity termwise,
   composed with V55's series bridge. Both V54 and V55 are PASS-tied
   workspace theorems. The `tsum`–integral interchange is standard
   Mathlib (`intervalIntegral.integral_tsum`).
4. **"Strong evidence the result improves c_value"**: not directly —
   Theorem 2 is a structural prerequisite, not an immediate c-push.
   But the brief's default disposition is "ship structural prerequisites
   in per-candidate Lean files, not in proposals."

So the four-condition guide says: **attempt-first**, no proposal.

## Concrete edits expected

- `Candidates/V57/DiskExcessLiftIntegrated.lean` (NEW): contains
  Theorem 1 (`diskExcess_lift_identity_at_alpha`), Theorem 2
  (`diskExcess_upper_bound_via_lift_at_alpha`), and (if Phase A budget
  allows) Theorem 3 (`diskExcess_le_simple_at_alpha_eq_c`). All three
  are `theorem`s with no `axiom`s and no `sorry`s. The file imports
  only `Mathlib.MeasureTheory.Integral.IntervalIntegral`,
  `Mathlib.Topology.Algebra.InfiniteSum.*`, `KorenblumPaper.PaperAxioms`,
  `KorenblumPaper.AnnulusIntegralReduction`,
  `ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`,
  `ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`. The file
  declares no new `def`s and no new `axiom`s; only `theorem`s.

- `Candidates/V57.lean` (NEW): ships at `c_value = 7129/20000 =
  0.35645`, ties V56 via `valid_of_eq15` discharged by
  `hEq15_oracle_certified_hp_35645`, byte-for-byte axiom-envelope-
  identical to V56. Includes a side lemma
  `v57_lift_integrated_compiles_at_seed_witness` that re-states
  Theorem 1's signature against an arbitrary
  `(a, b : ℕ → ℂ)`, `α : ℝ`, `c : ℝ` triple and closes by direct
  application of the per-candidate theorem (statement-level non-vacuity
  check, mirrors V55's
  `v55_lift_series_bridge_compiles_at_seed_witness`).

- `lemma.toml`: extend `[import_policy].allowed_exact` with
  `ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated`
  (one-line addition; mirrors sprint 068's V53.ThetaStep, sprint 069's
  V54.LiftIdentity, and sprint 070's V55.LiftSeriesBridge registration
  pattern). **No new axioms registered, no new oracle wiring.**

- `Bulletin.md`: append one row under "Recent events":
  `sprint_073 PASS: <one-line summary>`. (Standard
  pattern from sprints 068/069/070.)

- `Experience.md`: append a sprint-073 section per the brief's
  "Honesty in Experience.md" rules — what was attempted, what was the
  obstacle (if any), what the structural advance is, what the next
  move is.

## Acceptance criteria

1. **Phase A Lean build succeeds.** `lake build
   ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated`
   succeeds; the file contains at least Theorem 1
   (`diskExcess_lift_identity_at_alpha`) and Theorem 2
   (`diskExcess_upper_bound_via_lift_at_alpha`) as `theorem`s with no
   `axiom`s and no `sorry`s. (Theorem 3 optional but encouraged.)

2. **Candidate Lean build succeeds.** `lake build
   ProofRefinement.Korenblum.Candidates.V57` succeeds with
   `Candidates/V57.lean` shipping at `c_value = 7129/20000 = 0.35645`,
   discharged via `valid_of_eq15` and
   `hEq15_oracle_certified_hp_35645`, plus the side lemma
   `v57_lift_integrated_compiles_at_seed_witness`.

3. **Evaluator passes.** `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V57.lean`
   reports `pass: true`. The score is **`7129/20000 = 0.35645`**
   (V56-tied). The `axioms_used` audit reports
   `axioms_used = {propext, Classical.choice, Quot.sound,
   hEq15_oracle_certified_hp_35645}` — byte-for-byte identical to
   V56's envelope. No new axiom names in the audit.

4. **Structural advance.** The new file
   `Candidates/V57/DiskExcessLiftIntegrated.lean` is the workspace's
   **first per-candidate derived-theorem file producing a Λ-free
   integrated-over-`[0, c]` upper bound on `diskExcess`**, and the
   workspace's first consumer of `intervalIntegral.integral_tsum` (or
   equivalent `tsum`–integral interchange lemma) on a polar-Jacobian
   integration. Theorems 1+2 (or 1+2+3) are operational and can be
   composed by future closing-reducer sprints.

5. **No edits to read-only surfaces.** No edits to
   `KorenblumPaper/*.lean`, no edits to `Proof/Reduction.lean`, no
   edits to `Numerical_Library/`, no edits to existing
   `Candidates/V<K>.lean` (`K ≤ 56`), no edits to `Candidates/V53/`,
   `Candidates/V54/`, or `Candidates/V55/`. The only edits are: new
   files under `Candidates/V57/` and `Candidates/V57.lean`, plus the
   one-line `lemma.toml` extension and one row each in `Bulletin.md`
   and `Experience.md`.

6. **No new paper axioms, no new oracles, no proposal filing.** No
   new entries in `[seed_axioms].allowed`. No new entries in
   `[[oracles]]`. No new `Proposals/proposal_<NNN>_*.md` files. The
   `Section2Assumptions` structure is not extended.

7. **Honesty in Experience.md.** The Experience.md sprint-073 section
   must explicitly state:
   - What numerical exploration was done (none, by design — Theorems
     1 and 2 are identities/algebraic bounds, no Phase 0).
   - The current obstacle to `c > 7129/20000` (the per-mode-via-eq8+eq9
     axis is exhausted at multi-window granularity per sprint 071's
     forecast; this sprint ships a Λ-free disk-side bound that may
     compose with future per-`k` annulus-side machinery).
   - The next move (concrete: e.g. attempt a closing reducer that
     composes Theorem 2 / Theorem 3 with sprint 005's
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` plus eq8/eq9 on the
     annulus side, possibly producing a per-`k` cross-coupling kernel
     for the next c-push attempt).

## Out of scope

- Edits to `Candidates/V<K>.lean` for `K ≤ 56`, or to derived-theorem
  files under `Candidates/V53/`, `Candidates/V54/`, `Candidates/V55/`.
- Edits to `KorenblumPaper/*.lean` (read-only paper surface).
- Edits to `Proof/Reduction.lean` — sprint 073 is a per-candidate
  derived-theorem sprint, not a closing-reducer sprint. No new
  reducer is shipped in `Reduction.lean` this sprint.
- Edits to `Numerical_Library/` — no oracle is registered.
- A multi-window τ-partition reducer (sprint 072's superseded
  deliverable). Sprint 072's structural advance is no longer the
  cheapest path; sprint 073 is.
- Wang Lemma 2's full boundary L² Parseval-at-radius-ρ formalisation.
  That is a **separate, larger sprint** (a Mathlib-API-heavy
  formalization that may need its own attempt-first sprint to scope
  out, possibly producing a proposal_004 if the Mathlib gap turns
  out to be substantial). Sprint 073 sidesteps that question by
  routing through V54's per-`k` lift identity directly, which uses
  only `Complex.normSq` and `tsum`-level Mathlib — both well-supported.
- A closing reducer composing Theorem 2 with annulus-side machinery
  to attempt a c-push. That is a **future sprint** (sprint 074 or
  later), gated by Theorem 2 shipping cleanly here.
- Phase 0 numerical witness — none required, by the structure of
  Theorems 1 and 2 (identities + algebraic upper bounds, not numerical
  kernels).
- `proposal_004` filing or any further `Proposals/` entry. Sprint 073
  is an attempt-first per-candidate-derivation sprint per the
  brief's default disposition.
- Hoisting V53/V54/V55/V57 derived theorems into a shared
  `Proof/PerCandidateDerived.lean` location. (A separate hoisting
  sprint can do this once 5+ per-candidate files exist; out of scope
  here.)

## Time budget

≤ 90 minutes runtime.

- Phase A Theorem 1 proof: 20–40 minutes (compose V54+V55+`integral_tsum`).
- Phase A Theorem 2 proof: 5–10 minutes (algebraic corollary).
- Phase A Theorem 3 proof (optional): 10–20 minutes (Cauchy bound +
  `tsum_le_tsum`).
- V57.lean side-lemma + ship: 10 minutes (V55-template).
- Bulletin / Experience / lemma.toml updates: 10 minutes.

Total fits comfortably within the 90-minute envelope. If Phase A
runs long on Theorem 1's `integral_tsum` machinery (Mathlib's
`integral_tsum` family has multiple variants — `integral_tsum`,
`hasSum_integral_of_dominated_convergence`, etc., and the choice
matters for hypothesis ergonomics), the generator should ship
Theorems 1+2 alone and defer Theorem 3 to a future sprint.

## Stop conditions

- **Theorems 1 + 2 (and optionally 3) ship + V57 ties V56**:
  `STATUS=READY_FOR_EVALUATION` (the standard PASS-tie-with-structural-
  advance Outcome).
- **Phase A blocks on a Mathlib lemma** (e.g. `integral_tsum`'s
  hypothesis envelope is unworkable, no `tsum`-of-disk-weighted
  variant exists in Mathlib v4.28.0): `STATUS=BLOCKED` with a
  concrete `Scratch/sprint_073_obstruction.md` documenting the
  exact Mathlib lemma signature mismatch and naming the workaround
  (likely: prove the special case `c ≥ 0`, `α² < 1`,
  `∑' k, ‖a k − α·b k‖² · c^(2k+2)/(k+1) < ∞` directly via
  `intervalIntegrable.tsum` + `MeasureTheory.lintegral_tsum`
  decomposition, or fall back to a finite-truncation + limit
  argument).
- **Phase A blocks on summability** (the four `tsum`-summability
  hypotheses required by Theorem 1 are awkward to discharge in
  the V57 side-lemma context): `STATUS=BLOCKED` with the obstruction
  note recommending that Theorem 1's signature take all four
  summability hypotheses as universal-`Summable` parameters (mirroring
  `OneModePaperBridge.sigmaReduction_of_series`'s six-Summable
  signature), and the V57 side-lemma exercises the signature against
  an `(a, b, α, c)` arbitrary input without instantiating the
  summability cells (statement-level non-vacuity check only —
  identical to V55's pattern).
- **Phase A requires a trust-base expansion** (e.g. a `KorenblumPaper/`
  edit, a new oracle, a new seed axiom): `STATUS=BLOCKED_NEEDS_HUMAN`
  with a concrete obstruction note. This is forecast extremely
  unlikely — V54 and V55 already ship without trust expansion, and
  the integrated lift identity is a straightforward composition
  with one Mathlib `tsum`–integral interchange lemma.

## Sprint sequencing note (for the evaluator and the next planner)

If sprint 073 ships cleanly, the **immediately next planner session**
has two natural successor moves:

1. **Sprint 074 — closing reducer composing sprint 073's Theorem 2
   with sprint 005's series identity + eq8/eq9 on the annulus side.**
   This is the structurally novel c-push attempt that the bulletin's
   2026-05-04 directive points toward (Λ-free disk-side bound + per-`k`
   annulus-side bound = a closing reducer that pays per-`k` rather than
   uniformly). Phase 0 mpmath sweep should test whether the resulting
   per-`k` kernel admits a witness `(c, [windows], [j*])` with total
   mass ≥ 1 above V52 — this is the first such kernel that does NOT
   divide by `paperLambda` on the disk side, so its mass bound is
   structurally distinct from sprints 048/065/066/067/068/071.

2. **Sprint 075 — Wang Lemma 2 boundary L² Parseval-at-radius-ρ as
   a per-candidate derived-theorem file.** This is the Mathlib-API-heavy
   sprint that the brief identifies as the substantial structural
   prerequisite for the cross-coupling positivity chain. It is
   forecast at 200–500 lines depending on Mathlib's existing API;
   the generator should attempt-first and BLOCKED-with-obstruction-note
   if Mathlib's gap is multi-thousand-line.

The next planner picks whichever has the higher expected analytical
novelty per Generator-session, with sprint 074 as the more
immediately c-push-relevant move. Sprint 073's structural advance
is what makes either successor possible.
