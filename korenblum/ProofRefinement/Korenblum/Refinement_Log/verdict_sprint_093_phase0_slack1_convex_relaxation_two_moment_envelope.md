# Verdict: sprint_093_phase0_slack1_convex_relaxation_two_moment_envelope

**Contract**:
`ProofRefinement/Korenblum/Sprint_Contracts/sprint_093_phase0_slack1_convex_relaxation_two_moment_envelope.md`

**Candidate (parent)**:
`ProofRefinement/Korenblum/Candidates/V68.lean`

**Scratch deliverables**:
- `ProofRefinement/Korenblum/Scratch/sprint_093_slack1_two_moment_envelope.py` (707 lines)
- `ProofRefinement/Korenblum/Scratch/sprint_093_slack1_two_moment_envelope.txt` (213 lines)
- `ProofRefinement/Korenblum/Scratch/sprint_093_witness.txt` (52 lines, NO-GO structural memo)

---

## Outcome: PASS

**Sprint type**: Phase 0 Scratch-only probe (no Lean candidate shipped).

**DECISION from sweep**: NO-GO — Slack 1 falsified, structural reason: eq(4) admissibility
cone contains single-mode-at-argmax positive excitations η_j = δ_{j,j*(ρ)} which saturate
sup_j H_j exactly (R = 1, |1 − R| < 1e-12) at every V68 ρ-window.

Per the contract: "The sprint is PASS in either DECISION outcome — both the GO and NO-GO
branches discharge the contract."

---

## Candidate-side gates on V68

This sprint has no new Lean candidate. The contract requires V68 to build and pass
byte-for-byte at score 71313/200000. Gates were run on V68 per the human directive.

### Gate 1 — `lake build`
```
lake build ProofRefinement.Korenblum.Candidates.V68
```
Result: **PASS** — "Build completed successfully (8055 jobs)."

### Gate 2 — `grep -n 'sorry'`
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean
```
Result: **PASS** — no output (zero occurrences).

### Gate 3 — Full evaluator run
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```
Result: **PASS**
```
compile:       PASS (83.72s)
type-check:    PASS (76.58s)
axiom scan:    PASS (107.70s)
axiom audit:   PASS
oracle audit:  PASS
score (maximize): 71313/200000
status: PASS
```

### Gate 4 — Score comparison
No new candidate shipped this sprint; score gate is not applicable per contract §Acceptance
criteria ("The score gate is not applicable this sprint (no Lean candidate ships)").

---

## Acceptance criteria check

1. `sprint_093_slack1_two_moment_envelope.py` runs end-to-end at dps=40/80: PASS (file present,
   stdout log confirms both sweep phases completed without errors).
2. Captured stdout `.txt` contains:
   - Non-empty per-family rejection-rate table: PASS (11 families × 3 J-grids, all shown).
   - Per-window inf-ratio table over eleven V68 windows: PASS (table present).
   - NO-GO branch: single-mode test case with R = 1.0 and |1 − R| = 0.0 ≤ 1e-12 at all eleven
     windows, at both dps=40 and dps=80: PASS.
   - Final DECISION line in prescribed NO-GO format: PASS.
3. `witness.txt` content matches DECISION (NO-GO structural memo): PASS.
4. `Experience.md` gains sprint_093 subsection (line 5380+): PASS.
   `Bulletin.md` gains sprint_093 row (line 1312): PASS.
5. No edits to `Candidates/`, `Proof/`, `KorenblumPaper/`, `Numerical_Library/`,
   `lemma.toml`, or `Proposals/`: PASS (confirmed by file timestamps — only Scratch
   files and log/bulletin/experience files modified).

---

## Failing gate

None — all gates passed.

---

## Reproduction commands

```bash
# Gate 1: lake build
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2: sorry check
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3: evaluator
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean

# Scratch sweep (verification only, not a gate):
uv run ProofRefinement/Korenblum/Scratch/sprint_093_slack1_two_moment_envelope.py
```
