# Sprint 081: V63 Summability transfer kit — H²-to-six-shapes per-candidate file

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V63.lean`
**Target file**: `Candidates/V63.lean` (rev) + `Candidates/V63/Summability.lean` (new)
**Direction**: section2-proof (per-candidate analytic Lean derivation that
unblocks the V64+ c-push by reducing the universal-`(a, b)` summability
obstruction to a single H²-shaped input cell)

## Goal

Ship `Candidates/V63/Summability.lean`: a per-candidate derived-theorem
file containing **six summability transfer theorems**, each taking as
input a Wang H²-style hypothesis on `(a, b)` (concretely
`Summable (fun n => ‖a n‖^2)` and `Summable (fun n => ‖b n‖^2)`) and
producing one of the six summability shapes the
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's
`h_witness` predicate requires.

V63 ships as a **V62-tie** at `c_value = 35645/100000`, byte-for-byte
identical axiom envelope to V62. The kit is independently useful: a
future V64+ c-push sprint that constructs `h_witness` only needs a
single H² hypothesis per `(a, b)` plus this kit, instead of six
separate per-shape derivations.

## Why

### Structural blocker the kit removes

Sprint 080 shipped `Candidates/V63/Integrability.lean` (315 lines, two
theorems) but explicitly deferred `circleGap_two_rho_intervalIntegrable_on_unit`
on the grounds that **`Section2Assumptions` does not carry continuity
or measurability of `circleGap`**, so that integrability cannot be
derived for arbitrary `(a, b)`.

The same structural issue — and a stronger version of it — applies to
the **six summability hypotheses** inside the reducer's `h_witness`
predicate (signature at `Proof/Reduction.lean:7770-7829`). Concretely,
`h_witness` is universally quantified over `(a, b, K)`:

```
h_witness :
  ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c),
    ∃ (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ) (j₁ j₂ : ℕ),
      ... ∧ Summable (fun n => plusSeq a b n * c^(2n+2) / (n+1))
        ∧ Summable (fun n => plusSeq a b n * c^(2n))
        ∧ Summable (fun n => minusSeq a b n * c^(2n+2) / (n+1))
        ∧ Summable (fun n => minusSeq a b n * c^(2n))
        ∧ Summable (fun n => minusSeq a b n * OneModeKernel.weight c n)
        ∧ (∀ ⦃ρ⦄, c < ρ → ρ < 1 →
            Summable (fun n => minusSeq a b n * ρ^(2n)))
        ∧ ...
```

The summability hypotheses are **not derivable from `paper`** for
arbitrary `(a, b)`. They are not in fact true for arbitrary `(a, b)` —
they hold under Wang's H² boundary-norm finiteness hypothesis on the
underlying boundary functions `f, g` (i.e. `Summable (‖a n‖²)` and
`Summable (‖b n‖²)`), which is implicit in Wang's Section 2 setup but
**not encoded** in `Section2Assumptions`.

Sprint 079's obstruction note (`Scratch/sprint_079_obstruction.md`)
estimated 6 transfer theorems × ~200 lines = ~1200 lines, treating the
shapes as substantial Lean derivations. **That estimate assumed the
obstruction was an `ρ`-monotonicity transfer from `ρ = 1` summability
back to `ρ = c`.** The actual transfer — once the H² hypothesis is
made explicit as an *input* to the kit — is short:

  * `‖a n‖² + ‖b n‖²` summable (H² hypothesis, two summands) ⟹
    `coeffPlusGap a b n = ‖a n‖² − ‖b n‖²` summable (linear combination),
  * `plusSeq a b n` summable (indicator restriction is summable when
    base is),
  * `plusSeq a b n * c^(2n)` summable for `0 ≤ c < 1` (geometric
    domination by `‖a n‖² + ‖b n‖²`),
  * `plusSeq a b n * c^(2n+2)/(n+1)` summable (multiply by `c²/(n+1) ≤ c²`),
  * the `(c, 1)`-uniform shape `∀ ρ ∈ (c, 1), Summable (… * ρ^(2n))`
    follows from H² + geometric tail at any `ρ < 1`,
  * `OneModeKernel.weight c n = c^(2n+2)·(n/(n+1))` summable shape
    matches the `c^(2n+2)/(n+1)` shape modulo a bounded factor.

Each shape is `Summable.of_nonneg_of_le` plus a few-line per-`n`
inequality. Total estimated kit size: **~400-600 lines**, not
~1200.

### Why this sprint is well-shaped

1. **Independently useful.** The kit is *the* missing component for
   V64+ to construct `h_witness`. Once shipped, the only remaining
   obstacles to a V52-beating c-push are (a) candidate-side
   `circleGap` integrability (sprint 080's deferred theorem 3,
   surfaced as a candidate-side hypothesis the same way), (b) the
   `diskExcess ≤ innerSeriesExcess` composition, (c) a candidate-side
   H² hypothesis (free axiom or proposal-level trust expansion —
   distinct sprint), and (d) the windowed endpoint construction
   (route A from sprint 079's obstruction note: `Real.sqrt`-based
   endpoints).

2. **Re-frames the obstruction note's pessimistic estimate.** Sprint
   079's 1200-line estimate built in an `ρ`-monotonicity transfer
   from `ρ = 1` that this sprint **bypasses** by taking H² directly
   as an input cell. The transfer-from-H² shape is a much shorter
   derivation per shape (Mathlib's `Summable.of_nonneg_of_le` is the
   key lemma), reducing the per-shape count from ~200 lines to
   ~50-80 lines.

3. **Strict structural advance over V63.** V64 (a future sprint) can
   `import ProofRefinement.Korenblum.Candidates.V63.Summability` (or
   the hoisted version) to discharge six of the ten non-numerical
   `h_witness` cells in a single theorem invocation per cell.

4. **Distinct from sprint 080's Integrability.lean.** Sprint 080
   shipped two integrability theorems on closed-form integrands that
   ARE derivable from `Section2Assumptions` (modulo the deferred
   `circleGap` integrability). This sprint ships transfer theorems
   that are derivable *given an explicit H² hypothesis*. Different
   chain: integrability (closed-form analyticity on a bounded
   interval) vs. summability (geometric/factorial decay of an
   underlying H² coefficient sequence).

### Why this is the highest-novelty bounded sprint

Per the planner brief's "ultrathink" gate, the alternative candidate
sprint shapes considered were:

  * **Ship Summability.lean as `Section2Assumptions`-only theorems**
    (the literal-reading of sprint 080's forward direction): this is
    **structurally impossible**, the universal-`(a, b)` summability
    is not derivable from `paper` alone. Demoted.
  * **File proposal_004 to add H² fields to `Section2Assumptions`**:
    the genuine structural blocker, but a proposal-only sprint
    without immediate Lean work fails the planner brief's
    "runnable immediately" requirement. The kit shipped here is the
    *upstream* deliverable that proposal_004 would consume — better
    to ship the kit first, then file the proposal in a future
    planner session if/when the candidate-side H² hypothesis route
    proves blocking.
  * **Hoist V53/V54/V55/V57/V58/V60 derived theorems into `Proof/`**:
    structural cleanup, low novelty, demoted per Bulletin priority
    block.
  * **Pivot to a different reducer family** (e.g. extend sprint 014's
    `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` for a
    c-push): same universal-`(a, b)` summability blocker (sprint
    014's `h_witness` carries the same shapes); kit is needed there
    too.

The H²-to-six-shapes kit is the smallest, most novel, most reusable
deliverable that materially advances all four chains above.

## Concrete edits expected

### `Candidates/V63/Summability.lean` (new file, ~400-600 lines)

Six transfer theorems plus a small consolidation theorem, all in the
`ProofRefinement.Korenblum.Candidates.V63.Summability` namespace.

Each transfer theorem takes as input:

```
{a b : ℕ → ℂ}
(hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
(hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
{c : ℝ}
(hc_nonneg : 0 ≤ c)
(hc_lt_one : c < 1)
```

and produces one target summability shape. The recommended order is
the six shapes pinned in `Proof/Reduction.lean:7787-7803`:

1. `summable_plus_disk_weight`:
   ```
   theorem summable_plus_disk_weight (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ))
   ```

2. `summable_plus_sigma_at_c`:
   ```
   theorem summable_plus_sigma_at_c (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.plusSeq a b n * c ^ (2 * n))
   ```

3. `summable_minus_disk_weight`:
   ```
   theorem summable_minus_disk_weight (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ))
   ```

4. `summable_minus_sigma_at_c`:
   ```
   theorem summable_minus_sigma_at_c (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * c ^ (2 * n))
   ```

5. `summable_minus_kernel_weight` — the `OneModeKernel.weight c n` shape:
   ```
   theorem summable_minus_kernel_weight (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n)
   ```
   `OneModeKernel.weight c n = c^(2n+2) · (n/(n+1))` (or whatever its
   definition is in `KorenblumPaper/OneModeKernel.lean` — re-read
   the definition; the bound `OneModeKernel.weight c n ≤ c^(2n+2)`
   should be a one-liner from `n/(n+1) ≤ 1`).

6. `summable_minus_sigma_uniform_on_open`:
   ```
   theorem summable_minus_sigma_uniform_on_open (...) :
     ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
       Summable (fun n : ℕ =>
         OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))
   ```
   This is the `ρ`-uniform shape — for any `ρ < 1` the geometric
   domination by `‖a n‖² + ‖b n‖²` still holds.

7. **Consolidation theorem** `six_summability_shapes_from_h2`:
   ```
   theorem six_summability_shapes_from_h2 (...) :
     Summable (fun n : ℕ =>
       OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
     Summable (fun n : ℕ =>
       OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
     Summable (fun n : ℕ =>
       OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) ∧
     (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
       Summable (fun n : ℕ =>
         OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
   ```
   Six direct invocations of theorems 1-6. This packages the kit
   into the exact shape the V64+ c-push sprint will need.

### Proof strategy per transfer theorem

The canonical proof template is:

1. **Bound the base coefficient by the H²-summable envelope.** From
   `hH2_a : Summable (fun n => ‖a n‖²)` and `hH2_b`,
   `Summable (fun n => ‖a n‖² + ‖b n‖²)` by `Summable.add`. Then
   `|coeffPlusGap a b n| = |‖a n‖² − ‖b n‖²| ≤ ‖a n‖² + ‖b n‖²` for
   each `n`. Hence `Summable (fun n => |coeffPlusGap a b n|)` by
   `Summable.of_nonneg_of_le`.

2. **Lift to `plusSeq`.** `plusSeq a b n = if n1Pred a b n then
   coeffPlusGap a b n else 0`, so `|plusSeq a b n| ≤ |coeffPlusGap a b n|`,
   so `Summable (fun n => |plusSeq a b n|)` from step 1, hence
   `Summable plusSeq` by `summable_iff_summable_abs`-style lemma (or
   directly via `Summable.of_nonneg_of_le` since `plusSeq` is
   nonneg by `OneModePaperBridge.plusSeq_nonneg_of_pos`).

3. **Apply the geometric/factorial weighting.** For shape
   `* c^(2n)`: `plusSeq a b n * c^(2n) ≤ plusSeq a b n` (since
   `c^(2n) ≤ 1` for `c ≤ 1`), or alternatively (tighter) bound by
   `(‖a n‖² + ‖b n‖²) * 1` which is the H² envelope. For shape
   `* c^(2n+2)/(n+1)`: bound by `* c²` (since `c^(2n)/(n+1) ≤ c^(2n)
   ≤ 1` and `c^(2n+2) = c² · c^(2n)`). For `OneModeKernel.weight c n
   = c^(2n+2) · (n/(n+1))`: same as above plus `n/(n+1) ≤ 1`. For
   the `ρ`-uniform shape: `ρ^(2n) ≤ 1` for `ρ ≤ 1` (since `0 ≤ ρ`,
   from `c < ρ` and `0 < c`).

4. **Close via `Summable.of_nonneg_of_le`.** The target shape's
   per-`n` term is bounded by a constant multiple of the H²-envelope
   per-`n` term, all nonneg. Hence summable.

The proof body per theorem should be ~30-80 lines including
boilerplate. Six theorems plus the consolidation should fit
comfortably in 400-600 total Lean lines.

### `Candidates/V63.lean` (revised)

Extend the existing V63 candidate file (236 lines, V62-tied via
`valid_of_eq15` + `hEq15_oracle_certified_hp_35645`) with one
additional side lemma exercising the new kit:

```
lemma v63_summability_kit_compiles_at_witness :
    ∀ (a b : ℕ → ℂ)
      (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
      (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
      {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1),
      ... ∧ ... ∧ ... :=
  Candidates.V63.Summability.six_summability_shapes_from_h2
```

Direct invocation, confirms Lean syntax acceptance, preserves the
theorem statements for V64+.

V63's `valid_of_eq15` discharge stays unchanged. `axioms_used`
stays byte-for-byte identical to V62 (V61-tie envelope).

### `lemma.toml`

Add `ProofRefinement.Korenblum.Candidates.V63.Summability` to
`[import_policy].allowed_exact` — same one-line institutional
pattern as sprint 080's `V63.Integrability` registration. **No new
axioms, no new oracles, no `[seed_axioms]` changes, no
`[workspace_import_policy]` changes.**

### NO edits to

- `KorenblumPaper/` (read-only paper surface)
- `Numerical_Library/`
- `Proof/CandidateContract.lean`, `Proof/Main.lean`, `Proof/Reduction.lean`
- Any V0–V62 candidate file
- Any per-candidate derived-theorem file under `Candidates/V<N>/` for
  `N ≤ 62` (including `Candidates/V63/Integrability.lean` from sprint
  080)
- `Proposals/` (no proposal filed this sprint)

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V63.Summability`
   succeeds.
2. `lake build ProofRefinement.Korenblum.Candidates.V63` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V63.lean` reports
   `status: PASS` with `score (maximize): 7129/20000` (V62-tie).
4. V63's `axioms_used` is byte-for-byte identical to V62's V61-tie
   envelope: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V63.hEq15_oracle_certified_hp_35645}`
   (with the Lean compiler axioms in the seed set as usual).
5. The new file `Candidates/V63/Summability.lean` contains **only
   `theorem`s and `lemma`s** — no new `axiom` declarations, no
   `sorry`, no `Section2Assumptions` field extensions.
6. The six target summability shapes (theorems 1-6) plus the
   consolidation theorem (`six_summability_shapes_from_h2`) compile
   against the existing `[workspace_import_policy]` allowlist (no
   new imports outside `KorenblumPaper.*`,
   `ProofRefinement.Korenblum.*`, `Mathlib.*`).
7. The consolidation theorem's signature **byte-exactly matches the
   six summability shapes** required by
   `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
   predicate at `Proof/Reduction.lean:7787-7803`. (This is a
   structural commitment: V64+ should be able to compose the kit's
   output with the reducer without adapter shims.)
8. `Bulletin.md` and `Experience.md` each gain one row documenting:
   - which six summability shapes were proved,
   - the line count of `Candidates/V63/Summability.lean`,
   - the H² hypothesis shape consumed (`Summable (‖a n‖²)` plus
     `Summable (‖b n‖²)`),
   - confirmation that the kit's output signature matches the
     reducer's `h_witness` predicate byte-exactly,
   - the next-sprint forward direction (sprint 082 should ship
     `Candidates/V63/DiskInnerSeriesBridge.lean` to discharge the
     `diskExcess ≤ innerSeriesExcess` cell, OR file proposal_004 to
     add H² fields to `Section2Assumptions` if the candidate-side
     H² hypothesis route is preferred).

## Out of scope

- **Do not** push `c_value` past `35645/100000` in this sprint. V63
  must tie V62 at the V61-tie envelope. Pushing c requires also
  shipping the DiskInnerSeriesBridge.lean kit (sprint 082+) AND
  resolving the candidate-side H² hypothesis question (proposal_004
  or candidate-side hypothesis carry); that is multi-sprint work and
  this sprint is the structurally-load-bearing intermediate piece.
- **Do not** modify `Section2Assumptions` or any field on it. The
  H² hypothesis stays as a *hypothesis on the kit's theorems*, not
  a paper-axiom field. Adding it to the structure is a
  proposal-level trust expansion (proposal_004), filed by a future
  planner session if needed.
- **Do not** edit `Proof/Reduction.lean`, `KorenblumPaper/`,
  `Numerical_Library/`, or any V0–V62 candidate file or
  `Candidates/V63/Integrability.lean`.
- **Do not** ship a Phase 0 numerical script for this sprint. The
  deliverable is purely Lean (the consolidation theorem's truth is
  pure analytic — no numerical witness is needed).
- **Do not** file a `Proposals/` entry. Even though the
  candidate-side H² hypothesis route may eventually want
  proposal_004, this sprint is the *upstream* deliverable. The
  proposal-filing decision belongs to a future planner session
  after the kit ships and the V64+ candidate-side construction is
  attempted.
- **Do not** prove the kit's transfer theorems via `axiom` even if
  the proof body is hard. If a transfer turns out structurally
  harder than ~80 lines and the budget runs out, ship fewer
  shapes — partial delivery is acceptable per Stop conditions.
  Never substitute an `axiom` for a derivable theorem.
- **Do not** change the `ValidKorenblumBound` final theorem
  statement or the `c_value` def name.
- **Do not** introduce `Real.sqrt`-based endpoints in V63. Endpoint
  selection (route A in sprint 079's obstruction note) is part of
  the V64+ candidate-side `h_witness` construction, not part of
  this Summability sprint.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- **Acceptance criteria 1–8 met**: `STATUS=READY_FOR_EVALUATION`.
  V63 ships V62-tied with the new `Candidates/V63/Summability.lean`
  containing six transfer theorems plus consolidation.

- **Acceptance criteria 1, 2, 3, 4, 5 met but the consolidation
  theorem signature does not byte-exactly match the reducer's
  `h_witness` predicate (criterion 7)**: ship the partial result
  with the discrepancy documented at
  `Scratch/sprint_081_obstruction.md` (e.g., `OneModeKernel.weight`
  has a different shape than expected, or one of the six shapes
  uses `(n + 1 : ℝ)` vs. `((n : ℝ) + 1)` non-uniformly), and
  `STATUS=READY_FOR_EVALUATION`. The obstruction note must
  enumerate what shape adjustment the V64+ sprint needs to bridge
  the kit's output to the reducer's input.

- **Acceptance criterion 6 fails because a Mathlib summability
  lemma family is needed that the workspace hasn't yet imported**:
  add the import to the new `Candidates/V63/Summability.lean` file
  only — do **not** edit `lemma.toml`'s
  `[workspace_import_policy]`. Document the new Mathlib subpath at
  `Scratch/sprint_081_imports.md` so future sprints can confirm
  the addition fits within `Mathlib.*` allowance.

- **A transfer theorem turns out structurally harder than ~80
  lines** (e.g., `OneModeKernel.weight` has a non-trivial shape
  that requires a `tsum_le_tsum`-flavoured bound rather than a
  per-`n` `Summable.of_nonneg_of_le`): ship the other five shapes
  plus the consolidation theorem with a `sorry`-free placeholder
  for the harder shape (e.g., the consolidation theorem returns
  five-of-six shapes plus a hypothesis on the sixth). Document at
  `Scratch/sprint_081_obstruction.md` and
  `STATUS=READY_FOR_EVALUATION` with the partial delivery flagged.
  The V64+ sprint then has a smaller residual to discharge.

- **A new free-floating axiom or trust-base expansion would be
  required** (e.g., the kit needs a Mathlib lemma not in the
  current allowlist, or the H² hypothesis shape shipped in the kit
  doesn't match what V64+ can produce): do not ship it. Document
  at `Scratch/sprint_081_obstruction.md` and
  `STATUS=BLOCKED_NEEDS_HUMAN`.

- **The Generator decides the kit is already supplied by an
  existing workspace theorem** (e.g., a workspace lemma in
  `KorenblumPaper.OneModePaperBridge` already does the H²-to-six-
  shapes transfer): document the existing theorem at
  `Scratch/sprint_081_already_exists.md`, ship V63 as a V62-tie
  with **only** a side lemma exercising the existing theorem (no
  new derived-theorem file), and `STATUS=READY_FOR_EVALUATION`.
  The side lemma's role is then to surface the existing theorem's
  signature for the V64+ sprint, the same way sprint 080 did with
  `Candidates/V63/Integrability.lean` for `paperScalarIntegrand{1,2}_intervalIntegrable`.

## Notes for the generator

- **Read first**: `Candidates/V63/Integrability.lean` (sprint 080's
  per-candidate file pattern), `Proof/Reduction.lean:7770-7829`
  (the m=2 reducer signature with the six summability shapes inline),
  `KorenblumPaper/OneModePaperBridge.lean:11-50` (`plusSeq` /
  `minusSeq` definitions, `plusSeq_nonneg_of_pos`,
  `minusSeq_nonneg`), `KorenblumPaper/PaperAxioms.lean:38-50`
  (`coeffPlusGap`, `coeffMinusGap`, `n1Pred`, `n2Pred`),
  `KorenblumPaper/OneModeKernel.lean` (definition of
  `OneModeKernel.weight`).

- **The H² hypothesis shape**. Use `Summable (fun n => ‖a n‖^2)`
  and `Summable (fun n => ‖b n‖^2)` separately, not bundled. This
  matches the natural Mathlib shape (`Complex.norm`-squared
  summability for the Hardy space `H²`). The kit's transfer
  theorems should accept these two hypotheses as separate
  arguments.

- **Indicator restriction lemma**. The transition from
  `Summable (fun n => coeffPlusGap a b n)` (or its absolute value)
  to `Summable (fun n => plusSeq a b n)` uses `Summable.indicator`
  or a direct `Summable.of_nonneg_of_le` with the bound
  `|plusSeq a b n| ≤ |coeffPlusGap a b n|` per `n`. Mathlib's
  `Set.indicator` API may be useful; alternatively, since
  `plusSeq` is already defined via an `if-then-else`, a per-`n`
  case split on the indicator predicate suffices.

- **Geometric envelope**. For `c^(2n) ≤ 1` use `pow_le_one` (with
  `0 ≤ c` and `c ≤ 1`). For `c^(2n+2)/(n+1) ≤ c²` (when `c ≤ 1`)
  use the same plus the bound `1/(n+1) ≤ 1`. For
  `OneModeKernel.weight c n ≤ c^(2n+2)` use the literal
  `n/(n+1) ≤ 1`. All bounds are `≤ 1`-style; the kit's
  per-shape proofs should converge on a consistent template.

- **The `ρ`-uniform shape** (theorem 6) takes `ρ` as universally
  quantified inside the conclusion. Its proof is just theorem 4
  (`* c^(2n)`-shape) generalized to arbitrary `ρ < 1`: the
  geometric domination by H² holds at any `0 ≤ ρ ≤ 1`, so the same
  `Summable.of_nonneg_of_le` argument works with `c` replaced by
  `ρ`. Don't over-engineer this — it's the same proof body, not a
  separate transfer.

- **The consolidation theorem's signature** must literally match the
  six conjuncts inside `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s
  `h_witness` predicate. **Read those six conjuncts byte-by-byte
  from `Proof/Reduction.lean:7787-7803` before starting**, and
  arrange the consolidation theorem's `And` chain in the same
  order. This is criterion 7 — the V64+ sprint's `obtain` pattern
  should be able to consume the kit's output without re-ordering.

- **The kit does not ship a candidate-side H² hypothesis source**.
  V64+ will need to either (a) carry H² as a candidate-side
  hypothesis (free axiom, but the seed envelope grows by two
  axioms), or (b) file proposal_004 to add H² fields to
  `Section2Assumptions` (cleaner trust surface, but proposal-
  level). This sprint **does not decide between (a) and (b)** —
  the kit's signature is shape-agnostic to the H² source.

- **Sprint 080's pattern**. The file structure should follow sprint
  080's `Candidates/V63/Integrability.lean`: ~50-line module
  docstring at the top documenting the kit's purpose, signature,
  and provenance (which Mathlib lemmas + which `KorenblumPaper`
  modules); each transfer theorem with its own short docstring;
  the consolidation theorem at the end with explicit reference to
  `Proof/Reduction.lean:7787-7803`'s six-conjunct shape.

- **No Phase 0 needed**. Sprint 081 is a pure Lean-engineering
  sprint. The mathematical content (H²-to-six-shapes transfer) is
  unconditionally true under the stated hypotheses; no numerical
  margin sweep is required.

- **V63's docstring** (the existing 236-line file) should be
  extended with one paragraph noting that V63 now ships TWO
  per-candidate derived-theorem files (`Integrability.lean` from
  sprint 080, `Summability.lean` from sprint 081), reducing the
  V64+ residual `h_witness` budget from ~10 cells to ~3 cells
  (`circleGap` integrability, `diskExcess ≤ innerSeriesExcess`,
  candidate-side H² source).
