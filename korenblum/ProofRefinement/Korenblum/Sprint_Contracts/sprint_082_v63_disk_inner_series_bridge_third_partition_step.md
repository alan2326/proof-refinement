# Sprint 082: V63 DiskInnerSeriesBridge — third partition step toward V63 c-push

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V63.lean`
**Target file**: `Candidates/V63.lean` (rev) + `Candidates/V63/DiskInnerSeriesBridge.lean` (new)
**Direction**: section2-proof (per-candidate analytic Lean derivation that
unblocks the V64+ c-push by discharging the `diskExcess ≤ innerSeriesExcess`
cell of the reducer's `h_witness` predicate)

## Goal

Ship `Candidates/V63/DiskInnerSeriesBridge.lean`: a per-candidate
derived-theorem file containing **the workspace's first paper-axiom-free
`diskExcess (circleGap a b) c = innerSeriesExcess a b c` equality**, plus
its `≤` corollary in the exact shape consumed by the
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's `h_witness`
predicate at `Proof/Reduction.lean:7820-7821`.

This is the **third and final per-candidate partition step** identified by
sprint 079's obstruction note (`Scratch/sprint_079_obstruction.md`,
estimated ~700 Lean lines under the original "summability transfer +
diskWeightedSeq composition" framing). With sprint 080's
`Candidates/V63/Integrability.lean` and sprint 081's
`Candidates/V63/Summability.lean` already shipped, this sprint completes
the structural prerequisites for the V64+ c-push to `c = 35646/100000`.

V63 ships unchanged as a **V62-tie** at `c_value = 35645/100000`, with
one new non-vacuity side lemma exercising the new bridge theorem.

## Why

### What the bridge accomplishes

The `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's
`h_witness` predicate at `Proof/Reduction.lean:7819-7821` requires:

```
PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
  OneModePaperBridge.innerSeriesExcess a b c
```

Sprint 042 already shipped the upstream identity
`diskExcess_eq_tsum_via_termwise_integration` at
`Proof/Reduction.lean:6473`:

```
PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
  ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c^(2k+2) / (k+1)
```

`innerSeriesExcess` is defined at `KorenblumPaper/OneModePaperBridge.lean:106`:

```
def innerSeriesExcess (a b : ℕ → ℂ) (c : ℝ) : ℝ :=
  OneModeSeries.diskWeightedSeq (plusSeq a b) c -
    OneModeSeries.diskWeightedSeq (minusSeq a b) c
```

with `diskWeightedSeq u c = ∑' n, u n * c^(2n+2) / (n+1)` from
`KorenblumPaper/OneModeSeries.lean:19-20`.

The bridge is therefore the per-`k` algebraic identity

```
coeffPlusGap a b k = plusSeq a b k - minusSeq a b k       (∀ k : ℕ)
```

lifted past two `tsum`'s via `tsum_sub` (under summability of the two
component series, supplied by sprint 081's H²-summability kit).

### Why the per-`k` identity holds

From `KorenblumPaper/PaperAxioms.lean:34-47`:

```
n1Pred a b k := k = 0 ∨ ‖a k‖ ≥ ‖b k‖
n2Pred a b k := 0 < k ∧ ‖a k‖ < ‖b k‖
coeffPlusGap a b k := ‖a k‖² - ‖b k‖²
coeffMinusGap a b k := ‖b k‖² - ‖a k‖² = -coeffPlusGap a b k
```

and from `KorenblumPaper/OneModePaperBridge.lean:11-17`:

```
plusSeq a b k := if n1Pred a b k then coeffPlusGap a b k else 0
minusSeq a b k := if n2Pred a b k then coeffMinusGap a b k else 0
```

For each `k`, exactly one of three cases holds:

  * **`k = 0`**: `n1Pred` holds (left disjunct), `n2Pred` fails (`0 < k`
    is false). So `plusSeq a b 0 = coeffPlusGap a b 0` and
    `minusSeq a b 0 = 0`. Identity:
    `coeffPlusGap a b 0 = plusSeq a b 0 - 0 = plusSeq a b 0 - minusSeq a b 0`. ✓
  * **`k ≥ 1` and `‖a k‖ ≥ ‖b k‖`**: `n1Pred` holds (right disjunct),
    `n2Pred` fails (`‖a k‖ < ‖b k‖` is false). So `plusSeq a b k =
    coeffPlusGap a b k` and `minusSeq a b k = 0`. Identity:
    `coeffPlusGap a b k = plusSeq a b k - 0`. ✓
  * **`k ≥ 1` and `‖a k‖ < ‖b k‖`**: `n1Pred` fails (`k ≠ 0` and
    `‖a k‖ < ‖b k‖` strictly), `n2Pred` holds. So `plusSeq a b k = 0`
    and `minusSeq a b k = coeffMinusGap a b k = -coeffPlusGap a b k`.
    Identity: `coeffPlusGap a b k = 0 - (-coeffPlusGap a b k) =
    plusSeq a b k - minusSeq a b k`. ✓

This is a `by_cases` + `unfold` + `nlinarith`/`linarith` per-`k` proof,
~30-50 lines.

### Why the `tsum`-level lift is clean

Once the per-`k` identity is proved, the bridge theorem is:

```
diskExcess (circleGap a b) c
  = ∑' k, coeffPlusGap a b k * c^(2k+2) / (k+1)        [sprint 042]
  = ∑' k, (plusSeq - minusSeq) * c^(2k+2) / (k+1)       [per-k identity]
  = ∑' k, plusSeq * c^(2k+2) / (k+1) -
    ∑' k, minusSeq * c^(2k+2) / (k+1)                   [tsum_sub]
  = diskWeightedSeq (plusSeq a b) c -
    diskWeightedSeq (minusSeq a b) c
  = innerSeriesExcess a b c                              [unfold]
```

The `tsum_sub` step requires summability of both `fun k => plusSeq a b k *
c^(2k+2) / (k+1)` and `fun k => minusSeq a b k * c^(2k+2) / (k+1)`,
which are exactly the first and third shapes shipped by sprint 081's
`six_summability_shapes_from_h2` consolidation theorem. The bridge
takes them as ordinary hypotheses; how the V64+ candidate produces
them (via H²) is sprint 081's concern, not this sprint's.

The `tsum` of `coeffPlusGap` itself is also summable: `coeffPlusGap =
plusSeq - minusSeq` per the per-`k` identity, and `Summable (plusSeq * w) +
Summable (minusSeq * w) ⇒ Summable ((plusSeq - minusSeq) * w) = Summable
(coeffPlusGap * w)`. This summability cell is also a sprint-082
deliverable (a small lemma derivable from the per-`k` identity plus
`Summable.sub`).

The result is a clean **equality** `diskExcess = innerSeriesExcess`,
strictly more informative than the ≤ the reducer needs. The ≤ corollary
is a one-liner.

### Why this is the highest-novelty bounded sprint

Per the planner brief's "ultrathink" gate, the alternative candidate
sprint shapes considered were:

  * **Skip ahead to a partial V64 c-push with `diskExcess ≤
    innerSeriesExcess` carried as a candidate-side free axiom**:
    structurally feasible at `c = 35646/100000` but trust-surface
    expanding for a result that is straightforwardly Lean-derivable.
    The per-`k` identity + `tsum_sub` chain is exactly the kind of
    "few hundred lines of `nlinarith`/`tsum_sub`/`unfold` work" that
    the planner brief's proposal-filing gate explicitly classifies as
    "the generator's job, not a proposal target." Demoted.

  * **File proposal_004 to add H² fields to `Section2Assumptions`**:
    the eventual structural fix for the V64 candidate-side H² source,
    but proposal-only sprints fail the planner brief's "runnable
    immediately" requirement. More importantly, **even after H² is
    added, the diskExcess ≤ innerSeriesExcess derivation still has
    to happen** — H² is an upstream summability source, not a
    downstream identity. This sprint's deliverable is *necessary*
    regardless of the H² source decision. Demoted.

  * **Hoist V53/V54/V55/V57/V58/V60 derived theorems into Proof/**:
    structural cleanup, low novelty per Bulletin priority block,
    does not advance the V63 c-push partition. Demoted.

  * **Re-derive paper.eq3 from eq2 + eq3 components**: orthogonal to
    the V63 c-push partition. The eq3 derivation does not feed into
    `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` (which uses
    eq8 + eq9 only — the eq4 hypothesis is on `sigmaPlus ≤
    sigmaMinus`, discharged by `paper.eq4_sigmaPlus_bound` directly).
    Demoted.

The DiskInnerSeriesBridge is the structurally load-bearing piece that
unblocks the V64+ c-push, paper-axiom-free, ~600-800 Lean lines of
clean `tsum`-level composition. **It is the only path to V52-beating
`c_value` that the partition has been incrementally building toward
since sprint 071** — the first c-push past V52's high-water mark in
22 sprints. Sprints 080 and 081 shipped two of the three required
derived-theorem files; this sprint ships the third.

After this sprint, V64+ can construct `h_witness` with all 10
non-numerical cells discharged via per-candidate kit theorems
(modulo a candidate-side H² source decision that V64 itself makes).

## Concrete edits expected

### `Candidates/V63/DiskInnerSeriesBridge.lean` (new file, ~600-800 lines)

Three theorems plus one summability corollary, all in the
`ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`
namespace.

#### Theorem 1: per-`k` algebraic identity

```
theorem coeffPlusGap_eq_plusSeq_sub_minusSeq
    (a b : ℕ → ℂ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k =
      OneModePaperBridge.plusSeq a b k -
        OneModePaperBridge.minusSeq a b k
```

Three-case `by_cases`:
  * `k = 0`: `n1Pred` holds via left disjunct, `n2Pred` fails. `simp` +
    `if_pos`/`if_neg` cleanup, `coeffMinusGap = 0` is irrelevant.
  * `k ≥ 1, ‖a k‖ ≥ ‖b k‖`: `n1Pred` holds via right disjunct, `n2Pred`
    fails (`‖a k‖ < ‖b k‖` is false). `simp` + `if_pos`/`if_neg`.
  * `k ≥ 1, ‖a k‖ < ‖b k‖`: `n1Pred` fails (both disjuncts fail),
    `n2Pred` holds. `simp` + `if_neg`/`if_pos`. The arithmetic step
    `coeffPlusGap = -coeffMinusGap` follows from `unfold coeffPlusGap
    coeffMinusGap; ring` (or `nlinarith` / `linarith`).

Estimated proof body: ~50-80 lines.

#### Theorem 2: termwise weighted identity (preparatory)

```
theorem coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted
    (a b : ℕ → ℂ) (c : ℝ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1) =
      OneModePaperBridge.plusSeq a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1) -
        OneModePaperBridge.minusSeq a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1)
```

Direct multiplication of theorem 1 by the weight `c^(2k+2) / (k+1)`,
then `ring` or `linear_combination`. ~10-15 lines.

#### Theorem 3 (summability corollary): summability of the gap-weighted series

```
theorem summable_coeffPlusGap_weighted_of_summable_components
    {a b : ℕ → ℂ} {c : ℝ}
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    Summable (fun k : ℕ =>
      PaperAxioms.coeffPlusGap a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1))
```

Apply `Summable.sub` to `hPlusDisk` and `hMinusDisk`, then `Summable.congr`
with theorem 2 to switch the per-`k` shape from `plusSeq * w − minusSeq * w`
to `coeffPlusGap * w`. ~30-50 lines.

`Summable` of `|coeffPlusGap a b k| * c^(2k+2) / (k+1)` (the absolute-
value variant required by sprint 042's `diskExcess_eq_tsum_via_termwise_integration`)
follows from the same components plus `|coeffPlusGap| ≤ |plusSeq| + |minusSeq|`
(or via `Summable.abs`). Document in the file whether the absolute-
value variant is also needed; if so, ship a parallel theorem
`summable_abs_coeffPlusGap_weighted_of_summable_components`. (The
sprint 042 theorem signature uses the absolute-value variant — see
`Proof/Reduction.lean:6477-6478`.)

#### Theorem 4 (the bridge): the equality

```
theorem diskExcess_eq_innerSeriesExcess
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      OneModePaperBridge.innerSeriesExcess a b c
```

Composition:
  1. Rewrite LHS via `diskExcess_eq_tsum_via_termwise_integration` (with
     `hAbsSummable` discharging its `Summable_int_norm` hypothesis), yielding
     `∑' k, coeffPlusGap * c^(2k+2) / (k+1)`.
  2. Rewrite the per-`k` body via theorem 2, yielding
     `∑' k, plusSeq * w - minusSeq * w`.
  3. Apply `tsum_sub` (with `hPlusDisk` and `hMinusDisk`), yielding
     `∑' k, plusSeq * w - ∑' k, minusSeq * w`.
  4. Unfold `diskWeightedSeq` to identify each `tsum` with a
     `diskWeightedSeq` invocation. The shape difference between
     Mathlib's `* c^(2k+2) / (k+1)` and `OneModeSeries.diskWeightedSeq`
     should be a `rfl` (definitional unfold).
  5. Unfold `innerSeriesExcess` to close.

Estimated proof body: ~80-150 lines depending on `tsum_sub`
side-condition shapes. The cleanest formulation may apply
`tsum_congr` after `tsum_sub` to absorb the per-`k` rewrite step.

#### Theorem 5 (the corollary): the ≤ shape consumed by the reducer

```
theorem diskExcess_le_innerSeriesExcess
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      OneModePaperBridge.innerSeriesExcess a b c :=
  le_of_eq (diskExcess_eq_innerSeriesExcess hc_nonneg hPlusDisk hMinusDisk hAbsSummable)
```

One-line corollary. Signature **byte-exactly matches** the
`PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
OneModePaperBridge.innerSeriesExcess a b c` cell in
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
predicate at `Proof/Reduction.lean:7820-7821`.

### `Candidates/V63.lean` (revised, +~30 lines)

Add one new side lemma exercising the new bridge theorem, parallel to
sprint 080's and sprint 081's non-vacuity checks:

```
lemma v63_diskExcess_le_innerSeriesExcess_compiles_at_witness
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk : Summable (fun k : ℕ =>
      OneModePaperBridge.plusSeq a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk : Summable (fun k : ℕ =>
      OneModePaperBridge.minusSeq a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable : Summable (fun k : ℕ =>
      |PaperAxioms.coeffPlusGap a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      OneModePaperBridge.innerSeriesExcess a b c :=
  ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
    hc_nonneg hPlusDisk hMinusDisk hAbsSummable
```

V63's `valid_of_eq15` discharge stays unchanged. `axioms_used` stays
byte-for-byte identical to V62 (V61-tie envelope).

The V63 docstring should be extended with a paragraph noting that V63
now ships THREE per-candidate derived-theorem files
(Integrability.lean, Summability.lean, DiskInnerSeriesBridge.lean),
reducing the V64+ residual `h_witness` budget to **two cells**:
  * the τ-window endpoint construction (Real.sqrt-based per route A
    of sprint 079's obstruction note), and
  * the candidate-side H² source decision (free axiom vs.
    proposal_004 — left to sprint 083+).

### `lemma.toml`

Add `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge` to
`[import_policy].allowed_exact` — same one-line institutional pattern
as sprint 080's `V63.Integrability` and sprint 081's `V63.Summability`
registrations. **No new axioms, no new oracles, no `[seed_axioms]`
changes, no `[workspace_import_policy]` changes.**

### NO edits to

- `KorenblumPaper/` (read-only paper surface).
- `Numerical_Library/`.
- `Proof/CandidateContract.lean`, `Proof/Main.lean`, `Proof/Reduction.lean`.
- Any V0–V62 candidate file.
- Any per-candidate derived-theorem file under `Candidates/V<N>/` for
  `N ≤ 62`, or `Candidates/V63/Integrability.lean` (sprint 080's
  shipped artifact), or `Candidates/V63/Summability.lean` (sprint 081's
  shipped artifact).
- `Proposals/` (no proposal filed this sprint — see Why §"the
  alternatives considered" above).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`
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
5. The new file `Candidates/V63/DiskInnerSeriesBridge.lean` contains
   **only `theorem`s and `lemma`s** — no new `axiom` declarations, no
   `sorry`, no `Section2Assumptions` field extensions.
6. The five target theorems
   (`coeffPlusGap_eq_plusSeq_sub_minusSeq`,
   `coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted`,
   `summable_coeffPlusGap_weighted_of_summable_components`,
   `diskExcess_eq_innerSeriesExcess`,
   `diskExcess_le_innerSeriesExcess`) compile against the existing
   `[workspace_import_policy]` allowlist (no new imports outside
   `KorenblumPaper.*`, `ProofRefinement.Korenblum.*`, `Mathlib.*`).
7. The `diskExcess_le_innerSeriesExcess` corollary's signature
   **byte-exactly matches** the `diskExcess ≤ innerSeriesExcess` cell
   inside `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s
   `h_witness` predicate at `Proof/Reduction.lean:7820-7821`. The V64+
   sprint's `obtain` pattern should be able to consume the bridge's
   output without adapter shims.
8. `Bulletin.md` and `Experience.md` each gain one row documenting:
   - the per-`k` identity proved,
   - the `tsum`-level composition (`tsum_sub` + sprint 042 + theorem 2
     unfold),
   - the line count of `Candidates/V63/DiskInnerSeriesBridge.lean`,
   - confirmation that the bridge's output signature matches the
     reducer's `h_witness` cell byte-exactly,
   - the next-sprint forward direction (sprint 083 should construct
     V64 at `c = 35646/100000` composing all three V63 derived-theorem
     files into `h_witness`, OR file proposal_004 to add H² fields
     to `Section2Assumptions` if the candidate-side H² source decision
     blocks).

## Out of scope

- **Do not** push `c_value` past `35645/100000` in this sprint. V63
  must tie V62 at the V61-tie envelope. Pushing c is sprint 083+'s
  job and requires composing all three V63 derived-theorem files
  with the τ-window endpoint construction and a candidate-side H²
  source.
- **Do not** modify `Section2Assumptions` or any field on it. The
  summability hypotheses stay as ordinary hypotheses on the bridge's
  theorems, exactly as they do for sprint 081's transfer kit.
- **Do not** edit `Proof/Reduction.lean`, `KorenblumPaper/`,
  `Numerical_Library/`, or any V0–V62 candidate file or
  `Candidates/V63/Integrability.lean` (sprint 080's artifact) or
  `Candidates/V63/Summability.lean` (sprint 081's artifact).
- **Do not** ship a Phase 0 numerical script for this sprint. The
  deliverable is purely Lean (the bridge's truth is pure analytic —
  per-`k` identity + `tsum_sub`; no numerical witness is needed).
- **Do not** file a `Proposals/` entry. Even though the V64+ candidate-
  side H² hypothesis route may eventually want proposal_004, this
  sprint is structurally upstream of that decision. Proposal-filing
  belongs to sprint 083+ after the V64 candidate-side construction is
  attempted.
- **Do not** prove the bridge via a free `axiom` even if the
  `tsum_sub` composition turns out structurally harder than
  expected. If the bridge's full equality form (theorem 4) hits a
  Mathlib-API obstruction, ship the per-`k` identity (theorem 1) +
  the weighted variant (theorem 2) + the summability corollary
  (theorem 3) and document the residual at
  `Scratch/sprint_082_obstruction.md`. Never substitute an `axiom`
  for a derivable theorem.
- **Do not** change the `ValidKorenblumBound` final theorem
  statement or the `c_value` def name.
- **Do not** introduce `Real.sqrt`-based endpoints in V63. Endpoint
  selection (route A in sprint 079's obstruction note) is part of
  V64+'s `h_witness` construction, not part of this DiskInnerSeriesBridge
  sprint.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- **Acceptance criteria 1–8 met**: `STATUS=READY_FOR_EVALUATION`. V63
  ships V62-tied with the new `Candidates/V63/DiskInnerSeriesBridge.lean`
  containing the five target theorems.

- **Acceptance criteria 1, 2, 3, 4, 5 met but theorem 4
  (`diskExcess_eq_innerSeriesExcess`) does not compile because of a
  `tsum_sub` API mismatch or a `tsum_congr`-shape problem**: ship the
  partial result (theorems 1, 2, 3) plus a partial theorem 4 with a
  `sorry`-free placeholder (e.g., the bridge concludes only the per-`k`
  identity at the `tsum`-level, without the final `diskWeightedSeq`
  unfold), document the discrepancy at
  `Scratch/sprint_082_obstruction.md`, and `STATUS=READY_FOR_EVALUATION`.
  The obstruction note must enumerate which Mathlib `tsum` lemma
  family was needed.

- **Acceptance criterion 6 fails because a Mathlib `tsum` or
  `Summable` lemma family is needed that the workspace hasn't yet
  imported** (e.g., `tsum_sub_of_summable` lives in a Mathlib subpath
  that is not currently transitively imported): add the import to the
  new `Candidates/V63/DiskInnerSeriesBridge.lean` file only — do
  **not** edit `lemma.toml`'s `[workspace_import_policy]`. Document
  the new Mathlib subpath at `Scratch/sprint_082_imports.md`.

- **The per-`k` identity (theorem 1) turns out structurally harder
  than ~80 lines** (e.g., the three-case `by_cases` does not
  cleanly cover the `coeffPlusGap = -coeffMinusGap` step): ship the
  proof at the cost of more lines — do not punt to a free axiom.
  The identity is unconditionally true and a `nlinarith`-level
  derivation; if the generator hits 200 lines, that is acceptable.

- **A new free-floating axiom or trust-base expansion would be
  required**: do not ship it. Document at
  `Scratch/sprint_082_obstruction.md` and `STATUS=BLOCKED_NEEDS_HUMAN`.

- **The Generator decides the bridge is already supplied by an
  existing workspace theorem**: document the existing theorem at
  `Scratch/sprint_082_already_exists.md`, ship V63 as a V62-tie with
  **only** a side lemma exercising the existing theorem (no new
  derived-theorem file), and `STATUS=READY_FOR_EVALUATION`. The side
  lemma's role is then to surface the existing theorem's signature
  for the V64+ sprint at the exact `h_witness` shape.

## Notes for the generator

- **Read first**: `Proof/Reduction.lean:6473-6685` (sprint 042's
  `diskExcess_eq_tsum_via_termwise_integration` — the upstream identity
  this bridge composes with), `Proof/Reduction.lean:7820-7821` (the
  exact `h_witness` cell shape this bridge discharges),
  `KorenblumPaper/PaperAxioms.lean:34-47` (`n1Pred`, `n2Pred`,
  `coeffPlusGap`, `coeffMinusGap` definitions),
  `KorenblumPaper/OneModePaperBridge.lean:11-44` (`plusSeq`, `minusSeq`,
  `plusSeq_nonneg_of_pos`, `minusSeq_nonneg`, `minusSeq_mode`),
  `KorenblumPaper/OneModePaperBridge.lean:106-108`
  (`innerSeriesExcess` definition),
  `KorenblumPaper/OneModeSeries.lean:19-20` (`diskWeightedSeq`
  definition), `Candidates/V63/Summability.lean` (sprint 081's six-shape
  consolidation theorem — produces the summability hypotheses this
  bridge consumes), `Candidates/V63/Integrability.lean` (sprint 080's
  per-candidate file pattern — module structure to mirror).

- **The per-`k` identity proof template**. The cleanest structure is:
  ```
  theorem coeffPlusGap_eq_plusSeq_sub_minusSeq (a b : ℕ → ℂ) (k : ℕ) :
      coeffPlusGap a b k = plusSeq a b k - minusSeq a b k := by
    classical
    by_cases hk0 : k = 0
    · subst hk0
      have hN1 : n1Pred a b 0 := Or.inl rfl
      have hN2_neg : ¬ n2Pred a b 0 := by
        intro ⟨h, _⟩; exact absurd h (lt_irrefl 0)
      simp [plusSeq, minusSeq, if_pos hN1, if_neg hN2_neg]
    · push_neg at hk0
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      by_cases hba : ‖b k‖ ≤ ‖a k‖
      · -- n1Pred holds via right disjunct, n2Pred fails
        have hN1 : n1Pred a b k := Or.inr hba
        have hN2_neg : ¬ n2Pred a b k := fun ⟨_, hlt⟩ => not_lt.mpr hba hlt
        simp [plusSeq, minusSeq, if_pos hN1, if_neg hN2_neg]
      · -- n1Pred fails, n2Pred holds
        push_neg at hba
        have hN1_neg : ¬ n1Pred a b k := by
          rintro (h | h)
          · exact hk0 h
          · exact not_lt.mpr h hba
        have hN2 : n2Pred a b k := ⟨hk_pos, hba⟩
        simp [plusSeq, minusSeq, if_neg hN1_neg, if_pos hN2]
        unfold coeffPlusGap coeffMinusGap
        ring
  ```
  The last `ring` step closes via
  `‖a k‖² - ‖b k‖² = -(‖b k‖² - ‖a k‖²)`, equivalent to
  `0 - (‖b k‖² - ‖a k‖²) = ‖a k‖² - ‖b k‖²`. Use `linarith` or `ring`
  as appropriate.

- **The `tsum_sub` step**. Mathlib provides `Summable.tsum_sub` (or
  `tsum_sub` directly) that takes two summable hypotheses and yields
  `∑' k, (f k - g k) = ∑' k, f k - ∑' k, g k`. After theorem 2's
  per-`k` rewrite, `tsum_sub` discharges the bridge's composition
  step.

- **The `tsum_congr` rewrite step**. After theorem 2 establishes the
  per-`k` equality, the rewrite from
  `∑' k, coeffPlusGap a b k * c^(2k+2) / (k+1)` to
  `∑' k, (plusSeq * w - minusSeq * w)` is a `tsum_congr`. The
  cleanest formulation may be:
  ```
  have h_tsum_eq : ∑' k, coeffPlusGap a b k * c^(2k+2) / (k+1) =
                   ∑' k, (plusSeq a b k * c^(2k+2) / (k+1) -
                          minusSeq a b k * c^(2k+2) / (k+1)) :=
    tsum_congr (fun k => coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted a b c k)
  ```
  then apply `tsum_sub` to the RHS.

- **`diskWeightedSeq` unfold**. `diskWeightedSeq u c = ∑' n, u n *
  c^(2n+2) / (n+1)` is *definitional* (see
  `KorenblumPaper/OneModeSeries.lean:19-20`), so `unfold
  diskWeightedSeq` (or `show`/`change`) suffices to identify the two
  `tsum`'s with the corresponding `diskWeightedSeq` invocations. The
  shape between Mathlib's `((k : ℝ) + 1)` and the file's `(k + 1 : ℝ)`
  cast is byte-for-byte the same once `push_cast` normalizes; if a
  cast mismatch arises, `push_cast` or a one-line `show` discharges.

- **The `hAbsSummable` cell of theorem 4**. Sprint 042's
  `diskExcess_eq_tsum_via_termwise_integration` requires
  `Summable (fun k => |coeffPlusGap a b k| * c^(2k+2) / (k+1))` (the
  absolute-value variant). This is **not** identical to the two
  summability hypotheses sprint 081 ships (those bound the
  non-absolute-value `plusSeq * w` and `minusSeq * w`). However, since
  `|coeffPlusGap| ≤ |plusSeq| + |minusSeq| = plusSeq + minusSeq` (both
  nonneg by `plusSeq_nonneg_of_pos` and `minusSeq_nonneg`), the
  absolute-value summability follows from the two non-abs summabilities
  via `Summable.of_nonneg_of_le`. Ship this as a small auxiliary lemma
  inside the file (or as theorem 3's "absolute-value variant"); the
  V64+ candidate then has a single H²-derivable summability hypothesis
  to discharge per shape.

- **The `≤` corollary** is one line:
  `le_of_eq (diskExcess_eq_innerSeriesExcess ...)`. Don't over-engineer
  it; the equality's `le_of_eq` form is the exact shape the reducer
  needs.

- **No Phase 0 needed**. Sprint 082 is a pure Lean-engineering
  sprint. The mathematical content (per-`k` algebraic identity +
  `tsum_sub` lift) is unconditionally true under the stated hypotheses;
  no numerical margin sweep is required. Sprint 081's pattern
  (Lean-only deliverable) is the model.

- **The file structure** should follow sprint 080's
  `Candidates/V63/Integrability.lean` and sprint 081's
  `Candidates/V63/Summability.lean`: ~50-line module docstring at the
  top documenting the bridge's purpose, signature, and provenance
  (sprint 042 + sprint 081 + per-`k` algebraic identity); each theorem
  with its own short docstring; the corollary at the end with explicit
  reference to `Proof/Reduction.lean:7820-7821`'s `h_witness` cell.

- **V63's docstring** (the existing 306-line file) should be extended
  with one paragraph noting that V63 now ships THREE per-candidate
  derived-theorem files (Integrability.lean from sprint 080,
  Summability.lean from sprint 081, DiskInnerSeriesBridge.lean from
  sprint 082), reducing the V64+ residual `h_witness` budget to two
  cells (τ-window endpoint construction via `Real.sqrt`, candidate-
  side H² source decision).
