# Verdict: sprint_096_hoist_disk_inner_series_bridge_to_proof

**Contract path**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_096_hoist_disk_inner_series_bridge_to_proof.md`

**Candidate path**: `korenblum/ProofRefinement/Korenblum/Candidates/V68.lean`

**Target file (new shared module)**: `korenblum/ProofRefinement/Korenblum/Proof/DiskInnerSeriesBridge.lean`

**Outcome**: PASS

**Failing gate**: None

---

## Gate results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V68`

PASS. Build completed successfully (8055 jobs). Warnings only (style lints on
`show` vs `change` and unused variables); no errors.

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V68
```

### Gate 2 — `grep -n 'sorry' Candidates/V68.lean`

PASS. No `sorry` occurrences in V68.lean.

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean
```

### Gate 3 — Evaluator run

PASS.

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```

Post-hoist evaluator result (log entry timestamp `2026-05-05T14:05:09`):
- `pass: true`
- `score: "71313/200000"`
- `candidate: "Candidates/V68.lean"`
- `sha256: 85a54edad20cec07f8469a7b1e03252baacd668e472ebe07e3fa10b75812c87a`
- `imports` includes `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge` (allowed)

### Gate 4 — Score comparison (score-neutral hoist)

PASS. Score is exactly equal pre-hoist vs post-hoist: `71313/200000 = 71313/200000`.

The contract specifies a score-neutral hoist; strict improvement is NOT required.
The score is unchanged at `71313/200000`.

**Pre-hoist axioms_used** (log timestamp `2026-05-05T09:51:31`):
- propext
- Classical.choice
- Quot.sound
- ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10
- ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68
- ProofRefinement.Korenblum.Candidates.V68.hH2_v68

**Post-hoist axioms_used** (log timestamp `2026-05-05T14:05:09`):
- propext
- Classical.choice
- Quot.sound
- ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10
- ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68
- ProofRefinement.Korenblum.Candidates.V68.hH2_v68

The two sets are **identical** (set-theoretically). No axioms added or removed.

---

## Additional structural checks

**New shared module** `Proof/DiskInnerSeriesBridge.lean`:
- Contains exactly five theorems (`coeffPlusGap_eq_plusSeq_sub_minusSeq`,
  `coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted`,
  `summable_coeffPlusGap_weighted_of_summable_components`,
  `summable_abs_coeffPlusGap_weighted_of_summable_components`,
  `diskExcess_eq_innerSeriesExcess`, `diskExcess_le_innerSeriesExcess`)
  plus one `private lemma`. No `axiom`s. No `sorry`s in proof terms.
- Namespace: `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge` (correct).

**V63 shim** `Candidates/V63/DiskInnerSeriesBridge.lean`:
- Reduced to a thin re-export shim importing from `Proof.DiskInnerSeriesBridge`
  and re-exporting all five theorems under the original per-candidate namespace.

**Consumer import updates** (all six updated to import from `Proof.DiskInnerSeriesBridge`):
- V62.lean: line 6 imports `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`
- V64.lean: line 6 imports `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`
- V65.lean: verified (same pattern)
- V66.lean: verified (same pattern)
- V67.lean: verified (same pattern)
- V68.lean: line 6 imports `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`

Note: V62 had no `DiskInnerSeriesBridge` references in the pre-hoist state
(contract overstated by one), but the generator updated V62 correctly regardless.

The per-candidate-scope rule violation (six consumers importing from a
per-candidate `Candidates/V63/` file) is remediated. The hoisted module
lives under `ProofRefinement.Korenblum.Proof`, covered by the existing
`allowed_prefixes` entry in `lemma.toml`.
