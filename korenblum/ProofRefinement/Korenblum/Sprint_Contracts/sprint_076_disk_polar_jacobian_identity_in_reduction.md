# Sprint 076: Disk-side polar-Jacobian termwise-integration identity in `Proof/Reduction.lean` — closing the V57/V58 asymmetry

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V58.lean` (high-water-tied; `c_value = 7129/20000 = 0.35645`)
**Target file**: `Candidates/V59.lean` (V58-tied, byte-for-byte axiom envelope identical) plus a new theorem in `Proof/Reduction.lean`
**Direction**: section2-proof + analytic-Lean derivation (new shared-trust-surface theorem in `Reduction.lean`; closes a known structural asymmetry between V57 and V58; sets up downstream c-push by giving V57.Theorem 1 a polar-Jacobian-hypothesis-free signature)

## Goal

Ship the **disk-side polar-Jacobian termwise-integration identity** in
`Proof/Reduction.lean`, mirroring sprint 046's existing
`annulusExcess_eq_tsum_via_termwise_integration` (lines 7016–7155 of
`Reduction.lean`):

```text
theorem diskExcess_eq_tsum_via_termwise_integration
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k
          * c ^ (2 * k + 2) / (k + 1)
```

This is the **disk-side sibling** of the existing annulus-side theorem.
The integration domain is `[0, c]` instead of `[c, 1]`; the per-`k`
weight is `c^(2k+2)/(k+1)` instead of `(1 − c^(2k+2))/(k+1)` (since
`∫_0^c 2ρ · ρ^(2k) dρ = c^(2k+2)/(k+1)` vs.
`∫_c^1 2ρ · ρ^(2k) dρ = (1 − c^(2k+2))/(k+1)`).

Then ship `Candidates/V59.lean` at `c_value = 7129/20000 = 0.35645`,
V58-tied via `valid_of_eq15` discharged by
`hEq15_oracle_certified_hp_35645`. V59's side-lemma
`v59_disk_polar_jacobian_compiles_at_witness` exercises the new
theorem's signature against arbitrary `(a, b : ℕ → ℂ)`, `c : ℝ`
input, mirroring V57's `v57_lift_integrated_compiles_at_seed_witness`
pattern (statement-level non-vacuity check).

## Why

### Structural state

V57 ships `Candidates/V57/DiskExcessLiftIntegrated.lean` Theorem 1
(`diskExcess_lift_identity_at_alpha`), the integrated lift identity
over `[0, c]`. V57.Theorem 1's signature **surfaces** the
polar-Jacobian disk-integral identity as a hypothesis:

```text
(hDiskJacobian :
  PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
    = ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c^(2*k+2) / (k+1))
```

(see `Candidates/V57/DiskExcessLiftIntegrated.lean` lines around the
Theorem 1 declaration; the contract for sprint 073 explicitly
acknowledged this hypothesis was surfaced "per the contract's
BLOCKED-on-summability stop-condition guidance" because the heavy
`intervalIntegral.integral_tsum`-machinery step was deferred.)

V58 ships `Candidates/V58/AnnulusExcessLiftIntegrated.lean` Theorem 1
(`annulusExcess_lift_identity_at_alpha`), the integrated lift identity
over `[c, 1]`. V58.Theorem 1's signature **discharges** the
polar-Jacobian annulus-integral step internally by invoking the
already-proved
`Reduction.annulusExcess_eq_tsum_via_termwise_integration`. V58 surfaces
only the single
`Summable (fun k => |coeffPlusGap a b k| * (1 − c^(2k+2)) / (k+1))`
hypothesis; the polar-Jacobian equation itself is dispatched.

This is the **structural asymmetry**: V58's clean signature relies on a
shared-trust-surface theorem that V57 does not have a sibling for.
Closing this asymmetry by proving the disk-side polar-Jacobian
identity in `Reduction.lean` gives a future sprint the freedom to
**re-state V57.Theorem 1 with the `hDiskJacobian` hypothesis dropped**
(the next planner queues that re-statement; this sprint produces only
the `Reduction.lean` theorem so the asymmetry is closed in shared
trust surface, and a V60 file shipping a polar-Jacobian-free
`diskExcess_lift_identity_at_alpha` becomes a one-line application).

### Why this register is genuinely new

The workspace currently has **one** polar-Jacobian termwise-integration
theorem (the annulus-side, sprint 046), and **zero** on the disk side.
Despite the proof being a near-mechanical transplant of sprint 046's
template (same `intervalIntegral.integral_tsum_of_summable_norm` /
`Summable.hasSum_iff` chain), the workspace has not had this theorem
since the harness was created. The reason is architectural: each prior
disk-side sprint either (a) routed through `eq3 + eq4 + eq8 + eq9`'s
`paperLambda`-anchored chain, or (b) surfaced the polar-Jacobian as a
hypothesis (V57's pattern), or (c) collapsed the disk integral to
zero on a degenerate window.

This sprint produces the **first shared-trust-surface theorem** that
gives `diskExcess` a closed-form per-`k` representation under the
single Bergman-disk summability hypothesis. The result is paper-axiom-
free (depends only on `Mathlib`, `KorenblumPaper.PaperAxioms`'s
def-level `diskExcess`/`coeffPlusGap`/`circleGap`, and the existing
`Reduction.lean` machinery sprint 046 already established).

### Compositional value

Once Sprint 076 ships, the next planner has a clear route to a
**Λ-free, hypothesis-light V60 closing reducer attempt** that does
NOT touch `Numerical_Library` and does NOT require Phase 0:

1. **V60.Th1** = V57.Theorem 1 with `hDiskJacobian` dropped (the
   hypothesis is now provided by Sprint 076's new
   `Reduction.diskExcess_eq_tsum_via_termwise_integration`).
2. **V60.Th2** = a clean closed-form expression for
   `(1 − α²) · (annulusExcess − diskExcess)(c)` at `α = c`,
   composing V58.Theorem 3's per-`k` representation with V60.Th1.
3. The next-after-V60 sprint then probes whether the per-`k` cross-
   coupling kernel admits a non-E1-falsifying witness above
   `c = 7129/20000`. **That probe is OUT OF SCOPE for Sprint 076.**
   This sprint just closes the structural asymmetry.

### Bounded Lean cost

The proof template is the existing
`annulusExcess_eq_tsum_via_termwise_integration` (`Reduction.lean`
lines 7016–7155, ≈140 lines). The disk version is a near-mechanical
transplant:

  * **Same proof structure**: define the per-`k` family
    `F k r = 2 · coeffPlusGap_k · r^(2k+1)`; show each `F k` is
    continuous and integrable on the compact integration domain;
    establish the per-`k` L¹-norm closed form
    `∫_0^c ‖F k r‖ dr = |coeffPlusGap_k| · c^(2k+2)/(k+1)` via
    `intervalIntegral.integral_pow`; invoke
    `intervalIntegral.integral_tsum_of_summable_norm` (or whichever
    of `tsum_intervalIntegral`, `MeasureTheory.integral_tsum`,
    `intervalIntegral.hasSum_integral_of_dominated_convergence` the
    annulus version actually uses — grep the existing proof to copy
    the exact API call) under the
    `∑' k, ∫_0^c ‖F k r‖ dr < ∞` hypothesis (which IS the
    `hSummable_int_norm` premise).
  * **Different integration domain**: replace every `Set.Ioc c 1`
    by `Set.Ioc 0 c`, every `intervalIntegral.integral … in c..(1:ℝ)`
    by `intervalIntegral.integral … in (0:ℝ)..c`, every
    `(1 - c^(2k+2))` factor in the closed-form result by
    `c^(2k+2)`, and every `Set.uIcc c (1:ℝ)` rewrite by
    `Set.uIcc 0 c` (using `Set.uIcc_of_le hc_nonneg`).
  * **Boundary case at ρ=0**: the disk version's lower endpoint is `0`,
    not `c`. The integrand `2ρ · circleGap(ρ)` evaluates to `0` at
    `ρ=0`, which is a clean boundary value — the existing annulus
    proof handles `ρ=c` symmetrically (via `‖F k c‖ ≤ continuity`
    on a compact interval), and the disk proof handles `ρ=0` the
    same way (via `‖F k 0‖ = 0` directly from `0^(2k+1) = 0` for
    `k ≥ 0`, which is `pow_zero`-discharged).

Estimated total proof body: **150–250 lines** in `Reduction.lean`,
plus a one-row entry in `Bulletin.md` and `Experience.md` per the
brief's documentation requirements, plus `Candidates/V59.lean`
(≈100 lines, V58-template). **No new files under `Candidates/V59/`
are required** — V59 just consumes the new shared-trust-surface
theorem in its side-lemma.

The proof is **bounded** — it is a direct transplant of an existing
in-workspace theorem. No new Mathlib API needs to be hunted for; the
existing sprint 046 proof already located the right Mathlib lemmas
(see `Reduction.lean` lines 7016–7155 for the exact API calls).

### Why no Phase 0

The new theorem is an **identity**, not a numerical kernel. There is
no integral-mass-≥-1 hypothesis to verify numerically. The identity
holds for every `(a, b : ℕ → ℂ)` satisfying the single summability
hypothesis. **Phase 0 is not required and is OUT OF SCOPE for this
sprint.**

V59 itself ties V58 via `valid_of_eq15` discharged by
`hEq15_oracle_certified_hp_35645` — byte-for-byte identical axiom
envelope to V58/V57/V56/V55/V54/V53/V52. **No new axioms, no new
oracles, no new proposals filed.**

### Why this is not proposal_004 territory

Per the planner brief's four-condition guide:

1. **"Tried hard and failed"**: the disk-side polar-Jacobian identity
   has not been attempted as its own sprint. Per the brief, queue the
   attempt sprint first; do not file a proposal for an unattempted
   derivation.
2. **"Genuinely large derivation cost"**: the proof is a near-mechanical
   transplant of an existing 140-line in-workspace theorem. Forecast
   150–250 lines, well within bounded-Generator-session capacity.
3. **"Strong reason to believe correct"**: the result is the disk-side
   counterpart of an already-proved theorem; the only changes are
   integration-domain endpoints and a sign flip in one factor. The
   mathematical content is identical termwise integration of a
   geometric polynomial sequence over a different interval.
4. **"Strong evidence the result improves c_value"**: not directly,
   but the result removes a hypothesis from V57.Theorem 1's signature,
   which is a strict prerequisite for the natural V60 closing-reducer
   probe (a future sprint, not this one).

So the four-condition guide says: **attempt-first**, no proposal.

## Read this before starting

1. `Proof/Reduction.lean` lines 7016–7155 —
   `annulusExcess_eq_tsum_via_termwise_integration`. **This is the
   proof template.** Copy its proof body and substitute the
   integration-domain endpoints + the per-`k` weight as detailed in
   "Concrete edits expected" below.
2. `KorenblumPaper/PaperAxioms.lean` — definitions of `diskExcess`,
   `annulusExcess`, `circleGap`, `coeffPlusGap`. Note that
   `diskExcess (circleGap a b) c = ∫ ρ in (0:ℝ)..c, 2*ρ * circleGap a b ρ`
   and `circleGap a b ρ = ∑' k, coeffPlusGap a b k * ρ^(2*k)` (the
   def-level expansion that the proof unfolds).
3. `Candidates/V57/DiskExcessLiftIntegrated.lean` — the existing V57
   Theorem 1 that surfaces the polar-Jacobian as a hypothesis. **Do
   not modify this file.** A future V60 sprint will produce a clean
   sibling that consumes Sprint 076's new shared-trust-surface
   theorem.
4. `Candidates/V58/AnnulusExcessLiftIntegrated.lean` — the existing V58
   Theorem 1 that consumes
   `Reduction.annulusExcess_eq_tsum_via_termwise_integration` (the
   sprint 046 result). **Do not modify this file.**

## Concrete edits expected

- `Proof/Reduction.lean` (one new theorem appended at end-of-file,
  before the closing `end ProofRefinement.Korenblum`; ≈150–250
  lines):
  - Theorem name: `diskExcess_eq_tsum_via_termwise_integration`.
  - Hypotheses: `(a b : ℕ → ℂ)`, `{c : ℝ}`, `(hc_nonneg : 0 ≤ c)`,
    `(hc_le_one : c ≤ 1)` [for parity with the annulus version's
    signature; the `c ≤ 1` is not strictly needed for the disk-side
    integration but matches the existing template], and the single
    Bergman-disk summability hypothesis
    `(hSummable_int_norm : Summable (fun k : ℕ => |coeffPlusGap a b k|
    * c^(2*k+2) / (k+1)))`.
  - Conclusion: `diskExcess (circleGap a b) c = ∑' k, coeffPlusGap a b
    k * c^(2*k+2) / (k+1)`.
  - Proof: transplant the body of
    `annulusExcess_eq_tsum_via_termwise_integration` line by line.
    Substitute:
    * every `Set.Ioc c 1` → `Set.Ioc 0 c`;
    * every `Set.uIcc c 1` → `Set.uIcc 0 c`, with the corresponding
      `Set.uIcc_of_le hc_le_one` rewrite swapped for
      `Set.uIcc_of_le hc_nonneg`;
    * every `intervalIntegral.integral … in c..(1:ℝ)` →
      `intervalIntegral.integral … in (0:ℝ)..c`;
    * every closed-form `(1 - c^(2*k+2))/(k+1)` factor in the
      per-`k` integral evaluation → `c^(2*k+2)/(k+1)` (the
      `1 -` term comes from the annulus version's
      `∫_c^1 ρ^(2k+1) dρ = (1 - c^(2k+2))/(2k+2)`; the disk version's
      `∫_0^c ρ^(2k+1) dρ = c^(2k+2)/(2k+2)` has no `1 -` factor);
    * every `hc_le_one` invocation that establishes the integration
      domain non-degeneracy → an analogous `hc_nonneg` invocation;
    * the boundary integrand value at `ρ = 0` (analogue of the
      annulus version's boundary at `ρ = c`): `‖F k 0‖ = 0` for all
      `k ≥ 0` since `0^(2k+1) = 0` (handled by `pow_zero` /
      `zero_pow` / `mul_zero`).
- `Candidates/V59.lean` (NEW, ≈100 lines): V58-tied at `c_value =
  7129/20000 = 0.35645` via `valid_of_eq15` discharged by
  `hEq15_oracle_certified_hp_35645`. Body identical to V58.lean
  except:
  * the namespace is `ProofRefinement.Korenblum.Candidates.V59`;
  * the parent is V58;
  * the side lemma is renamed
    `v59_disk_polar_jacobian_compiles_at_witness` and exercises the
    NEW `Reduction.diskExcess_eq_tsum_via_termwise_integration`'s
    signature against arbitrary `(a, b : ℕ → ℂ)`, `c : ℝ` input
    (statement-level non-vacuity check). A clean side-lemma body
    looks like:
    ```text
    theorem v59_disk_polar_jacobian_compiles_at_witness
        (a b : ℕ → ℂ) (c : ℝ)
        (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1)
        (hSum : Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| * c^(2*k+2) / (k+1))) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
          = ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c^(2*k+2) / (k+1) :=
      ProofRefinement.Korenblum.Proof.Reduction.diskExcess_eq_tsum_via_termwise_integration
        a b hc_nonneg hc_le_one hSum
    ```
    (adjust the namespace prefix to whatever the Reduction.lean
    namespace actually uses; sprint 046's existing theorem is named
    via `ProofRefinement.Korenblum.<...>` — grep
    `Reduction.lean::annulusExcess_eq_tsum_via_termwise_integration`
    to confirm the correct fully-qualified name.).
- **No edits to `lemma.toml`.** No new
  `[import_policy].allowed_exact` entry is needed because V59 does
  not introduce any new per-candidate file under `Candidates/V59/`.
  The new theorem lives in `Reduction.lean`, which is already
  available via the existing `ProofRefinement.Korenblum.Proof.Reduction`
  workspace import.
- **No edits to `KorenblumPaper/`** (read-only paper surface).
- **No edits to `Numerical_Library/`** — no oracle is registered.
- **No new `axiom`s** — no new entries in `[seed_axioms].allowed`,
  no new `[[oracles]]` rows, no `Section2Assumptions` field added.
- **No edits to existing `Candidates/V<K>.lean` for `K ≤ 58`**, no
  edits to per-candidate derived-theorem files under `Candidates/V53/`,
  `Candidates/V54/`, `Candidates/V55/`, `Candidates/V57/`,
  `Candidates/V58/`. The only file additions are the new theorem in
  `Reduction.lean` (appended) and `Candidates/V59.lean`.
- `Bulletin.md`: append one row under "Recent events":
  `sprint_076 PASS: <one-line summary>`.
- `Experience.md`: append a sprint-076 section per the brief's
  "Honesty in `Experience.md`" rules.

## Acceptance criteria

1. **Reduction.lean build succeeds.**
   `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
   The new theorem `diskExcess_eq_tsum_via_termwise_integration`
   appears in the file, is declared as a `theorem` (no `axiom`,
   no `sorry`, no `admit`).
2. **Candidate Lean build succeeds.**
   `lake build ProofRefinement.Korenblum.Candidates.V59` succeeds.
3. **Evaluator passes.**
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V59.lean`
   reports `pass: true`. The score is `7129/20000 = 0.35645`
   (V58-tied). The `axioms_used` audit reports
   `axioms_used = {propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V59.hEq15_oracle_certified_hp_35645}`
   — byte-for-byte identical to V58's envelope modulo the
   namespace-prefix on the oracle axiom.
4. **Structural advance.** `Reduction.lean` now contains BOTH
   `annulusExcess_eq_tsum_via_termwise_integration` (existing,
   sprint 046) AND
   `diskExcess_eq_tsum_via_termwise_integration` (new, sprint 076).
   The disk/annulus polar-Jacobian asymmetry between V57 and V58 is
   closed in shared trust surface.
5. **No edits to read-only / out-of-scope surfaces.** No edits to
   `KorenblumPaper/*.lean`, no edits to `Numerical_Library/`, no
   edits to existing `Candidates/V<K>.lean` (`K ≤ 58`), no edits to
   any per-candidate derived-theorem dir under `Candidates/V<N>/`
   for `N ≤ 58`, no edits to `Proof/CandidateContract.lean`,
   `Proof/Main.lean`, or any other `Proof/*.lean` file (only
   `Reduction.lean` is edited, and only by appending one new
   theorem before the closing `end`).
6. **No new paper axioms, no new oracles, no proposal filing.**
7. **Honesty in `Experience.md`.** The Experience.md sprint-076
   section must explicitly state:
   - **What was attempted.** The exact theorem signature shipped, and
     the proof-template-transplant strategy (cite sprint 046's
     existing theorem as the template).
   - **What numerical exploration was done.** None, by design — the
     theorem is an identity, no Phase 0 required. Confirm zero
     `Scratch/` files were added.
   - **The current obstacle to `c > 7129/20000`.** Specifically: the
     V58 Theorem 3 reduction
     `(1 − c²)·(annulusExcess − diskExcess)(c) = ∑' k, (1 − c²)·
     coeffPlusGap_k · (1 − 2c^(2k+2))/(k+1)` falsifies on E1 single-
     mode (`coeffPlusGap_1 = −1`, weight `(1 − 2c⁴)/2 > 0` at
     `c ≈ 0.36`). Sprint 076 ships a structural prerequisite for a
     future V60+ closing-reducer attempt that would need a per-`k`
     cross-coupling argument or per-`k` α-varying lift to break E1
     saturation; sprint 076 does NOT close any inequality on its own.
   - **What is the next move.** Concrete: V60 (sprint 077 or later)
     re-states V57.Theorem 1 with the `hDiskJacobian` hypothesis
     dropped (now discharged via the new sprint-076 shared-trust-
     surface theorem). The sprint after V60 may probe whether the
     per-`k` cross-coupling kernel admits a non-E1-falsifying witness
     above `c = 7129/20000`.
   - **What would unblock a c-push faster.** The per-`k` α-varying
     cross-coupling lift identity (a generalization of V54's per-`k`
     identity to `α : ℕ → ℝ` rather than `α : ℝ`) plus a Phase 0
     Scratch witness identifying an `α(k)` sequence under which the
     resulting per-`k` kernel is non-negative on a non-trivial
     `(c, [windows])`-envelope above `7129/20000`. Naming this
     does not file a proposal — it is forward direction for a
     future planner session.

## Out of scope

- Edits to `Candidates/V<K>.lean` for `K ≤ 58`, or to per-candidate
  derived-theorem files under `Candidates/V53/V54/V55/V57/V58/`.
- Edits to `KorenblumPaper/*.lean` (read-only paper surface).
- Edits to `Proof/CandidateContract.lean`, `Proof/Main.lean`, or any
  `Proof/*.lean` file other than `Reduction.lean`.
- Edits to `Numerical_Library/` — no oracle is registered.
- A V60 sprint that re-states V57.Theorem 1 with the `hDiskJacobian`
  hypothesis dropped. **That is the natural successor sprint, but
  is OUT OF SCOPE for sprint 076.** Sprint 076 ships only the
  shared-trust-surface theorem in `Reduction.lean`; the V57.Theorem
  1 cleanup is for the next planner.
- A closing-reducer composition of V57 + V58 + sprint 076 to attempt
  a c-push. **Out of scope.**
- Phase 0 numerical witness — the new theorem is an identity, not a
  numerical kernel. No Phase 0 required.
- `Proposals/` filings.
- Any change to `c_value` of V59 (V58-tied at `7129/20000`).
- Hoisting V53/V54/V55/V57/V58 derived theorems into a shared
  `Proof/PerCandidateDerived.lean` location. (A separate hoisting
  sprint can do this once the workspace stabilises; out of scope.)
- Reattempting sprint 072's multi-window τ-partition reducer.
- Wang Lemma 2 boundary L² Parseval-at-radius-ρ formalisation
  (deferred; a separate Mathlib-API-heavier sprint).
- Per-`k` α-varying lift identity (deferred to V61+ or beyond,
  pending Phase 0 Scratch witness).

## Time budget

≤ 75 minutes runtime.

- Phase A (`Reduction.lean` new theorem): 45–60 minutes
  (proof-template transplant from sprint 046; the bulk of the time
  is on careful endpoint substitution and the `ρ = 0` boundary case
  for `0^(2k+1)` evaluation).
- Phase B (`Candidates/V59.lean` shipping + side lemma):
  10–15 minutes (V58-template, byte-for-byte axiom envelope
  identical, side lemma is a one-line application of the new
  Reduction.lean theorem).
- `Bulletin.md` / `Experience.md` updates: 5 minutes.

If Phase A runs long because the
`intervalIntegral.integral_tsum_of_summable_norm` API call requires
a slightly different premise on the disk side than on the annulus
side (e.g. an extra `0 ≤ c` premise that the annulus version
implicitly absorbed via `c ≤ 1`), the generator should ship Phase A
alone (the new Reduction.lean theorem) and document the V59 build
status; Phase B can be deferred to a follow-up repair sprint.

## Stop conditions

- **Acceptance criteria 1–7 met (Phase A + Phase B both ship)**:
  `STATUS=READY_FOR_EVALUATION`. Standard PASS-tie-with-structural-
  advance outcome.
- **Phase A succeeds, Phase B fails to build for a reason unrelated
  to sprint 076's content** (e.g. a transitive dependency in
  `Reduction.lean` regresses): `STATUS=BLOCKED` with a precise
  obstruction note at `Scratch/sprint_076_obstruction.md` showing
  the failing build error, the goal state, and at least three
  attempted fixes. **Do not modify any candidate file other than
  V59.lean.**
- **Phase A blocks on the
  `intervalIntegral.integral_tsum_of_summable_norm` API call**
  (the API signature on the disk side does not directly accept the
  annulus version's hypothesis envelope): `STATUS=BLOCKED` with a
  concrete obstruction note documenting:
  1. the exact Mathlib API call sprint 046 uses (grep
     `Reduction.lean` lines 7016–7155 and quote the line),
  2. the exact API signature the disk version expects (search
     Mathlib's `intervalIntegral.integral_tsum_of_summable_norm`
     and quote the `theorem` signature),
  3. the disjointness between (1) and (2) and at least three
     attempted alternative tactics (e.g.
     `Summable.hasSum_iff` direct rewrite, `tsum_eq_sum_of_hasSum`,
     `MeasureTheory.lintegral_tsum` decomposition).
- **Phase A blocks on the `ρ = 0` boundary case** (`0^(2k+1)` not
  unfolding cleanly under the integrability premise of
  `intervalIntegral.integral_tsum_of_summable_norm`):
  `STATUS=BLOCKED` with a concrete obstruction note. Workaround
  candidates to attempt before exiting BLOCKED: `pow_zero`,
  `zero_pow (by omega : 2*k + 1 ≠ 0)`, `Nat.zero_pow`, manual
  `simp [pow_succ]` decomposition.
- **Phase A requires a trust-base expansion** (e.g. a `KorenblumPaper/`
  edit, a new oracle, a new seed axiom): `STATUS=BLOCKED_NEEDS_HUMAN`
  with a concrete obstruction note. **Forecast extremely unlikely**
  — sprint 046 already shipped without trust expansion using
  identical Mathlib API; the disk version is a transplant.

## Sprint sequencing note (for the next planner)

If sprint 076 ships cleanly, the **immediately next planner session**
has a clear successor:

**Sprint 077** — *Re-state V57.Theorem 1 with `hDiskJacobian` dropped*.
Ship `Candidates/V60/DiskExcessLiftIntegratedV2.lean` containing a
clean polar-Jacobian-hypothesis-free
`diskExcess_lift_identity_at_alpha_v2` theorem that consumes the new
sprint-076 `Reduction.diskExcess_eq_tsum_via_termwise_integration`
internally, mirroring V58's pattern of consuming the annulus-side
sprint-046 result. This is a small (≈80 line) sprint that finishes
closing the V57/V58 asymmetry on the candidate side. Then V60 ships
and ties V59.

The sprint after V60 may attempt the per-`k` cross-coupling closing
reducer, but **only with a Scratch numerical witness that the
resulting kernel does not falsify on E1**. The bulletin's repeated
warnings and V58.Theorem 3's explicit E1 falsification mean that any
such sprint must produce its Phase 0 mpmath sweep BEFORE writing any
Lean.
