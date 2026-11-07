# Sprint 075: integrated lift identity over `[c, 1]` per-candidate derived theorem (V58)

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V57.lean`
**Target file**: `Candidates/V58.lean`
**Direction**: section2-proof (structurally novel per-candidate derived theorem; V57-tied; sets up downstream c-push)

## Goal

Ship the workspace's first **Λ-free per-`k` annulus-side equality**:

    (1 − α²) · annulusExcess (circleGap a b) c
       = ∑' k, ‖a k − (α : ℂ)·b k‖² · (1 − c^(2k+2)) / (k + 1)
         − ∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k + 1)

as a Lean `theorem` in a per-candidate derived-theorem file
`Candidates/V58/AnnulusExcessLiftIntegrated.lean`. This is the
**structural sibling of V57's `diskExcess_lift_identity_at_alpha`**,
with the integration domain swapped from `[0, c]` to `[c, 1]` and the
weight `c^(2k+2)/(k+1)` swapped for `(1 − c^(2k+2))/(k+1)`. Together
with V57 Theorem 1, the workspace then has both halves of an
integrated, Λ-free, per-`k` representation of `annulusExcess −
diskExcess` on top of V54's per-`k` lift identity.

V58 ships at `c_value = 7129/20000 = 0.35645` with `valid_of_eq15`
discharged by `hEq15_oracle_certified_hp_35645`, byte-for-byte
identical to V57's axiom envelope. The structural advance is upstream
in the new derived-theorem file. **No c-push this sprint.**

## Why

Sprint 073 (V57) shipped the **disk-side** Λ-free integrated lift
identity. Its Experience.md retrospective (`Sprint 073` section, "What
the structural advance is") and the bulletin's recurring "Forward
direction" notes after sprint 073/074 both flag the **annulus-side
sibling** as the next composable building block: it is the missing
half that lets future sprints write a closing reducer whose RHS does
not divide by `paperLambda` on either side.

Concretely, this sprint is high-novelty per session because:

1. **The polar-Jacobian step on the annulus side is already proved.**
   `Proof/Reduction.lean::annulusExcess_eq_tsum_via_termwise_integration`
   (sprint 046, lines 7016–7155) gives, under a single
   `Summable (fun k => |coeffPlusGap a b k| * (1 − c^(2k+2)) / (k+1))`
   hypothesis, the closed form
   `annulusExcess (circleGap a b) c
      = ∑' k, coeffPlusGap a b k * (1 − c^(2k+2)) / (k + 1)`.
   So unlike V57's Theorem 1 — which had to surface the disk-side
   polar-Jacobian as a hypothesis — V58's Theorem 1 can **consume the
   existing sprint 046 result directly**, removing one hypothesis from
   the signature and yielding a strictly stronger derived theorem in
   the same proof-budget envelope.

2. **The proof is the V57 Theorem 1 proof with one weight swap.** The
   V57 proof body is ~80 lines (lines 124–216 of
   `Candidates/V57/DiskExcessLiftIntegrated.lean`). The annulus
   counterpart re-runs the same Steps 1–3 with `c^(2k+2)/(k+1)`
   replaced by `(1 − c^(2k+2))/(k+1)` and the polar-Jacobian
   hypothesis replaced by an invocation of the existing sprint 046
   theorem. Estimated 100–150 lines including the existing-theorem
   side conditions.

3. **Closes a known asymmetry.** V57 ships only the disk half. Every
   future closing reducer that wants to compose disk + annulus on
   the lift representation has to either re-derive the annulus piece
   inline or quote V58. Hoisting V58 to a per-candidate file follows
   the institutional pattern from V53/V54/V55/V57.

4. **Downstream composability.** Subtracting V57 Theorem 1 from V58
   Theorem 1 at `α = c` gives, on `c < 1`,

       (1 − c²) · (annulusExcess(c) − diskExcess(c))
          = ∑' k, (‖a k − c·b k‖² − ‖b k − c·a k‖²)
                   · (1 − 2c^(2k+2)) / (k + 1)

   which by V54 lift identity equals

       (1 − c²) · ∑' k, coeffPlusGap a b k · (1 − 2c^(2k+2)) / (k + 1).

   This is a closed-form per-`k` reduction of `annulusExcess ≥
   diskExcess` to a single `tsum` inequality on `coeffPlusGap`, with
   weights `(1 − 2c^(2k+2))/(k+1)` that are **strictly positive on
   `c² < 1/2`** (the Korenblum regime is `c² ≈ 0.126`, well inside
   that bound). V58 by itself does not close this inequality — but it
   is the equality that lets a future sprint state the inequality
   precisely and attempt a per-`k` closing argument.

5. **No Phase 0 numerical step required.** V58's deliverable is a
   closed-form **equality**, not an inequality. The sprint cannot
   numerically falsify on E1 / E2 etc. because it does not assert any
   sign-definite bound on its own; it is a per-`k` identity. The
   c-push question is deferred to the future closing-reducer sprint
   that consumes V58.

## Read this before starting

1. `Candidates/V57/DiskExcessLiftIntegrated.lean` — the disk-side
   sibling whose proof shape this sprint mirrors (~80 line proof of
   the analogous equality at lines 124–216).
2. `Candidates/V54/LiftIdentity.lean` — the per-`k` lift identity
   `(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²`
   shipped at `lift_identity_per_k`.
3. `Proof/Reduction.lean::annulusExcess_eq_tsum_via_termwise_integration`
   (lines 7016–7155). This is the polar-Jacobian step on the annulus
   side, already proved and built. Quote it; do not re-derive.
4. `KorenblumPaper/PaperAxioms.lean` — `annulusExcess` and
   `coeffPlusGap` definitions.

## Concrete edits expected

- `ProofRefinement/Korenblum/Candidates/V58/AnnulusExcessLiftIntegrated.lean`
  (new file; ≈100–150 lines): three `theorem`s, no `axiom`s, no
  `sorry`s.
  1. **`annulusExcess_lift_identity_at_alpha`** — the headline
     equality stated above. Hypotheses:
     - `(a b : ℕ → ℂ)`, `(α c : ℝ)`,
     - `0 ≤ c`, `c ≤ 1` (for sprint 046 invocation; **not** `α² < 1`,
       which is unused on the annulus side because `(1 − α²)` factors
       through cleanly even when `α² ≥ 1` — match V57 Theorem 1's
       hypothesis profile and require `α² < 1` only if the proof
       needs it),
     - the four annulus-weighted summability hypotheses
       `Summable (fun k => ‖_‖² · (1 − c^(2k+2)) / (k+1))` for each
       of `‖a k − α·b k‖`, `‖b k − α·a k‖`, `‖a k‖`, `‖b k‖`,
     - the **single** sprint-046 polar-Jacobian summability
       hypothesis
       `Summable (fun k => |coeffPlusGap a b k| · (1 − c^(2k+2)) / (k+1))`
       (so that
       `annulusExcess_eq_tsum_via_termwise_integration` can be
       applied; this hypothesis is implied by the four annulus-
       weighted hypotheses and the four `‖·‖² ≥ 0` plus `eq4`-shaped
       sums of which `coeffPlusGap_k = ‖a k‖² − ‖b k‖²` is a
       difference, but the simplest signature is to state it
       directly, exactly mirroring the existing sprint-046 theorem
       call site).
     - **No `hAnnulusJacobian` hypothesis.** Unlike V57's Theorem 1
       (which surfaces the disk-side polar-Jacobian as a hypothesis
       because Mathlib's `intervalIntegral.integral_tsum` machinery
       is heavy), V58's Theorem 1 invokes the already-proved
       `annulusExcess_eq_tsum_via_termwise_integration` from
       `Reduction.lean`. This is a strict structural improvement.
     Proof shape: identical to V57 Theorem 1 with `c^(2k+2)` swapped
     for `(1 − c^(2k+2))` and the `hDiskJacobian` rewrite swapped
     for an `annulusExcess_eq_tsum_via_termwise_integration`
     invocation. Step 1 rewrites `annulusExcess` as the `tsum`. Step
     2 pulls `(1 − α²)` inside via `← tsum_mul_left`. Step 3 invokes
     V54's `lift_identity_per_k` per-`k`, distributes
     `(1 − c^(2k+2))/(k+1)`, and splits the `tsum` of differences via
     `Summable.tsum_sub`.
  2. **`annulusExcess_lower_bound_via_lift_at_alpha`** — the immediate
     corollary obtained by dropping the **first** non-negative `tsum`
     (note: orientation is flipped versus V57 Theorem 2 because
     `annulusExcess` should be **lower-bounded** here, not upper-
     bounded; see "Sign / orientation convention" below):

         (1 − α²) · annulusExcess (circleGap a b) c
            ≥ − (∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k + 1))

     i.e.

         ∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k + 1)
            ≥ − (1 − α²) · annulusExcess (circleGap a b) c

     Hypotheses include `0 ≤ c`, `c ≤ 1`, and the four annulus-
     weighted summability hypotheses plus the sprint-046
     `Summable (fun k => |coeffPlusGap a b k| · (1 − c^(2k+2)) / (k+1))`
     hypothesis. Proof: apply Theorem 1 then drop the
     non-negative first `tsum` via `tsum_nonneg`. **The orientation
     of which term to drop is determined by which side of the
     annulus excess we want to bound; the sprint's reference
     orientation is the V57-mirroring "drop the first term, keep the
     second term", which keeps the signature symmetric with V57
     Theorem 2 modulo a final sign flip. The generator should pick
     whichever orientation makes the V58 → future-closing-reducer
     composition cleanest; both orientations are mechanical
     consequences of Theorem 1 and `tsum_nonneg`. If in doubt,
     ship both as Theorems 2a and 2b.**
  3. **`annulusMinusDiskExcess_per_k_at_alpha_eq_c`** (Optional,
     ship if budget allows) — the closed-form per-`k` representation
     of `annulusExcess − diskExcess` at `α = c`:

         (1 − c²) · (annulusExcess (circleGap a b) c
                       − diskExcess (circleGap a b) c)
            = ∑' k, coeffPlusGap a b k · (1 − 2 c^(2k+2)) / (k + 1)

     Proof: subtract V57 Theorem 1 (at α = c) from V58 Theorem 1 (at
     α = c), use V54's `lift_identity_per_k` per-`k` to convert
     `‖a k − c·b k‖² − ‖b k − c·a k‖²` into `(1 − c²) · coeffPlusGap`,
     and combine the two remaining `(1 − c^(2k+2))` and `c^(2k+2)`
     coefficients into `1 − 2 c^(2k+2)`. Hypotheses include both
     V57's disk hypotheses (the disk polar-Jacobian and four disk-
     weighted summability hypotheses) and V58's annulus hypotheses
     (the sprint-046 summability hypothesis and four annulus-weighted
     summability hypotheses). This theorem is the **direct
     reduction handle** for a future closing-reducer sprint; if
     ship-budget is tight, defer it to a follow-up sprint and ship
     only Theorems 1 and 2 in V58.

- `ProofRefinement/Korenblum/Candidates/V58.lean` (new file): V57-tied
  candidate. Identical body to V57.lean modulo the namespace and
  parent reference. Side lemma `v58_annulus_lift_integrated_compiles_at_seed_witness`
  exercises Theorem 1's signature against arbitrary input
  `(a, b, α, c)` (statement-level non-vacuity check, mirroring V57's
  `v57_lift_integrated_compiles_at_seed_witness`).

- `ProofRefinement/Korenblum/lemma.toml`: one-line addition to
  `[import_policy].allowed_exact` registering
  `ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated`,
  mirroring sprint 073's one-line edit for V57.

- No edits to `KorenblumPaper/`, `Proof/Reduction.lean`,
  `Numerical_Library/`, any other candidate file, or any other
  `lemma.toml` section.

## Sign / orientation convention

The V54 lift identity, as stated in `Candidates/V54/LiftIdentity.lean`,
is

    (1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²    (V54.fact)

Negating, since `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`,

    (1 − α²) · coeffPlusGap a b k = ‖a k − α·b k‖² − ‖b k − α·a k‖²    (V54.fact')

V57 Theorem 1 uses the (V54.fact') orientation, yielding

    (1 − α²) · diskExcess(c)
       = ∑' k, ‖a k − α·b k‖² · c^(2k+2)/(k+1)
         − ∑' k, ‖b k − α·a k‖² · c^(2k+2)/(k+1)

V58 Theorem 1 must use the **same** (V54.fact') orientation to keep
the disk and annulus halves additive. Concretely:

    (1 − α²) · annulusExcess(c)
       = ∑' k, ‖a k − α·b k‖² · (1 − c^(2k+2))/(k+1)
         − ∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2))/(k+1)

Adding V57 + V58 at α = c gives, on `c < 1`,

    (1 − c²) · (annulusExcess(c) + diskExcess(c))
       = ∑' k, ‖a k − c·b k‖² · 1 / (k + 1)
         − ∑' k, ‖b k − c·a k‖² · 1 / (k + 1)

since `c^(2k+2) + (1 − c^(2k+2)) = 1`. **Subtracting** V57 from V58 at
α = c gives the per-`k` weighting `(1 − 2 c^(2k+2))/(k+1)` that
Theorem 3 (Optional) consumes. Get the orientation right at
Theorem 1 — ALL three theorems flow from there.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated`
   succeeds with no `axiom`, no `sorry`, no `admit`.
2. `lake build ProofRefinement.Korenblum.Candidates.V58` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V58.lean`
   succeeds with `pass: true`, `score = 7129/20000`,
   `axioms_used = {propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V58.hEq15_oracle_certified_hp_35645}`
   (byte-for-byte identical to V57's evaluator envelope modulo the
   namespace-prefix on the oracle axiom).
4. `Candidates/V58/AnnulusExcessLiftIntegrated.lean` ships at minimum
   Theorems 1 (`annulusExcess_lift_identity_at_alpha`) and 2
   (`annulusExcess_lower_bound_via_lift_at_alpha`); Theorem 3
   (`annulusMinusDiskExcess_per_k_at_alpha_eq_c`) is optional.
5. The new file imports only:
   - `Mathlib.Topology.Algebra.InfiniteSum.{Basic, Group, Ring}`
     (mirroring V55/V57),
   - `KorenblumPaper.PaperAxioms` (for `annulusExcess`,
     `coeffPlusGap`, `circleGap`),
   - `ProofRefinement.Korenblum.Candidates.V54.LiftIdentity` (for
     `lift_identity_per_k`),
   - `ProofRefinement.Korenblum.Proof.Reduction` (for
     `annulusExcess_eq_tsum_via_termwise_integration`).
6. The new file uses zero `Section2Assumptions` fields directly
   (the sprint-046 theorem already encapsulates them). Mirrors
   V54/V55/V57's paper-axiom-light pattern.

## Out of scope

- Edits to `KorenblumPaper/`, `Proof/Reduction.lean`,
  `Numerical_Library/`, V0–V57 candidate files, or per-V<N> derived-
  theorem dirs other than the new `Candidates/V58/`.
- New `axiom`s, new oracles, new `[seed_axioms]` rows, new
  `[[oracles]]` rows.
- `Proposals/` filings.
- Any change to the final theorem statement or `c_value` of V58
  beyond V57's envelope.
- Any closing-reducer composition of V57 + V58 (deferred to the
  next sprint).
- Reattempting sprint 072's multi-window τ-partition reducer
  (deferred; the bulletin and sprint 074 retrospective give precise
  guidance for whoever picks that thread up later, and the per-mode
  τ-window structural NO-GO from sprint 071 means a multi-window
  reattempt without Wang-(5) fallback windows still cannot push c).

## Stop conditions

- Acceptance criteria 1–5 met (Theorems 1+2 ship): `STATUS=READY_FOR_EVALUATION`.
- Acceptance criteria 1–5 met **and** Theorem 3 also ships:
  `STATUS=READY_FOR_EVALUATION` (preferred outcome).
- Theorem 1 fails to build because `tsum_mul_left` does not directly
  apply (a Mathlib API edge case; V57 Theorem 1 hit and resolved this
  with `← tsum_mul_left` — same trick should work):
  `STATUS=BLOCKED` with a precise obstruction note at
  `Scratch/sprint_075_obstruction.md` showing the failing rewrite,
  the goal state, and at least three attempted alternative tactics
  (e.g. `Summable.tsum_mul_left`, `tsum_eq_tsum_of_ne_zero_bij`,
  manual `Summable` extraction). Do not exit BLOCKED before
  attempting all three.
- Theorem 1 fails to build because `annulusExcess_eq_tsum_via_termwise_integration`'s
  hypothesis envelope does not match what's exported (e.g. it
  requires a stronger summability premise than what V58 surfaces):
  `STATUS=BLOCKED` with a precise obstruction note at
  `Scratch/sprint_075_obstruction.md` listing the existing theorem's
  signature line by line and the hypothesis mismatch.
- Working-tree breakage of `Proof/Reduction.lean` (which the contract
  excludes from edits) prevents the new file from building:
  `STATUS=BLOCKED` with a precise obstruction note. **Do not edit
  `Proof/Reduction.lean`.** A separate repair sprint (per sprint 074
  precedent) is the right response.

## Time budget

≤ 90 minutes runtime. The proof is structurally V57 Theorem 1 with
one weight swap and one polar-Jacobian invocation swapped from "given
as hypothesis" to "quoted from existing theorem"; estimated 100–150
lines of Lean. V57 Theorem 1 was ~80 lines proven inside the V57
60-minute budget; the annulus version inherits its proof skeleton
plus the marginal cost of the existing-theorem invocation. If the
generator hits an unexpected Mathlib API edge, escalate to
`STATUS=BLOCKED` rather than overrun.

## Honesty in `Experience.md`

The next `Experience.md` entry must report:

- **What V58 ships.** The exact theorem signatures and proof line
  counts.
- **The polar-Jacobian invocation site.** Cite the existing sprint-046
  theorem name, line range in `Reduction.lean`, and the hypothesis
  that V58 Theorem 1 surfaces to consume it.
- **The orientation choice for Theorem 2.** Which `tsum` was dropped
  and why, with reference to the "Sign / orientation convention"
  section above.
- **Phase 0 status.** Explicitly: V58 is an equality, no Phase 0
  numerical sweep is required, and the sprint deliberately defers the
  closing-reducer composition to a future sprint. (No celebratory
  "first workspace lemma to" framing.)
- **Current obstacle to `c > 7129/20000`.** Specifically: a closing
  reducer composing V57 + V58 needs a per-`k` non-negativity
  argument, and the natural candidate
  `coeffPlusGap_k · (1 − 2 c^(2k+2)) ≥ 0` falsifies on the E1
  adversary (single-mode `b_1 = 1`, `coeffPlusGap_1 = −1`, weight
  `1 − 2c⁴ > 0` at `c ≈ 0.36`, so per-term contribution `−(1 − 2c⁴) <
  0`). Cite this so the next planner does not accidentally queue an
  E1-falsifying naive composition.
- **Numerical exploration.** None required this sprint (Theorem 1 is
  an equality). Confirm zero `Scratch/` files were added.
- **What is the next move.** Concrete: a future sprint composes
  V57 + V58 + a per-`k` cross-coupling argument that isolates the
  `coeffPlusGap_k < 0` modes and compensates them via a per-mode
  Cauchy-Schwarz / lift-at-different-α strategy (the analytical
  structure that V38's seven-window hybrid exploits). State this as
  a forward direction, not as a deliverable for this sprint.
- **What would unblock a c-push faster.** Even if not filed, name
  the specific structural piece that the next sprint will need
  (e.g. "a per-`k` lift identity with α varying per mode", or
  "Wang Lemma 2 expansion as a derived theorem") so the next
  planner has a concrete next-step.
