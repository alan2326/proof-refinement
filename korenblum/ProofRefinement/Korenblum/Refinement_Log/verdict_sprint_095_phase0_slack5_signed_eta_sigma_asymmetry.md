# Verdict — sprint_095_phase0_slack5_signed_eta_sigma_asymmetry

**Contract path**:
`ProofRefinement/Korenblum/Sprint_Contracts/sprint_095_phase0_slack5_signed_eta_sigma_asymmetry.md`

**Candidate path**: N/A (Phase 0 scratch-only sprint; evaluated against parent V68)

**Target candidate (gates run on)**: `Candidates/V68.lean`

**Outcome**: VERDICT_PASS

**Failing gate**: None — all gates passed.

---

## Gate results

### Gate 1 — lake build
```
lake build ProofRefinement.Korenblum.Candidates.V68
```
Result: `Build completed successfully (8055 jobs)` — PASS

### Gate 2 — grep sorry
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean
```
Result: no output (zero matches) — PASS

### Gate 3 — evaluator run
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```
Result:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (81.65s)
- type-check: PASS (85.06s)
- axiom scan: PASS (58.56s)
- axiom audit: PASS (seed axioms only, no surprises)
- oracle audit: PASS (h_eleven_window_mass_certified_at_356565_modeJ10: oracle=1 declared=1)
- score (maximize): `71313/200000`
- status: PASS

### Gate 4 — parent score comparison
Not applicable. The sprint contract specifies: "The score gate is not applicable this sprint (no Lean candidate ships)." This is a Phase 0 scratch-only sprint with no Lean changes. V68 remains at 71313/200000, matching the log entry for this candidate byte-for-byte.

---

## Sprint deliverables verified

- `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.py` (44715 bytes, ~1050 lines): sweep script runs end-to-end, emits DECISION line.
- `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.txt` (16706 bytes, 271 lines): contains eleven-window endpoint table, η-sweep summary (48 admissible vectors: 30 family A + 18 family B), per-window R-table for both R-conv and R-full, per-window R-supremum and argmax η-vector, n_trunc convergence guard (K=20 vs K=100, max |Δ| = 0.0), dps=80 re-verification, and a final DECISION line in the prescribed format.
- `Scratch/sprint_095_witness.txt` (4320 bytes, 100 lines): NO-GO structural memo with near-saturator η-vector, worst-case window analysis, structural explanation of why eq(4) does not provide the required strict reduction, and forward direction for sprint 096.
- `Experience.md`: sprint 095 subsection appended (confirmed at line 5454).
- `Bulletin.md`: sprint_095 PASS row appended (confirmed at line 1314).

No edits to `Candidates/`, `Proof/`, `KorenblumPaper/`, `lemma.toml`, or `Proposals/` during sprint 095 (prohibited-file diffs relative to HEAD are from earlier sprints, last touched at 08:15-08:27 UTC; sprint 095 deliverables written at 12:29-12:31 UTC).

---

## DECISION summary

**DECISION: NO-GO — Slack 5 falsified.**

Structural reason: Two-mode signed-η admissible cone with binding eq(4) at
`Σ⁺(c) = Σ⁻(c) = 1` admits configurations `η = (−1·c^(−2j_- − 2), +1·c^(−2j_+ − 2))`
with `j_+ = j*(ρ)` (the global argmax of H_j) on every V68 window i ∈ {0,…,9}.
When the positive-η mode aligns with the argmax, the convex combination collapses
to `p_{j_+}(ρ) = 1` and R-conv = 1 exactly. Per-window sup R-conv = 1.0 on windows
i = 0–9; min γ_w (R-conv) = −2.296e-41 (numerical zero), well below the 10^(-3)
acceptance floor. The eq(4) binding constrains the c-weighted masses Σ⁺/Σ⁻ but
does not constrain the j-axis location of the positive-η support. Confirmed at
dps=80 on the worst window (i=0, box0): sup R-conv (dps=80) = 1.0.

This is the closing bookend on the directive Section B Phase 0 falsifier sequence:
Slacks 1 (sprint 093), 3 (sprint 094), and 5 (sprint 095) are all eliminated as
Lean-derivable c-push routes at the V68 trust surface.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V68.lean
```
