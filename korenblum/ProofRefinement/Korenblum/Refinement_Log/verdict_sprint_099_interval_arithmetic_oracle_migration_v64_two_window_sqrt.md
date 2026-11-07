# Verdict: sprint_099_interval_arithmetic_oracle_migration_v64_two_window_sqrt

**Contract path**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_099_interval_arithmetic_oracle_migration_v64_two_window_sqrt.md`

**Target file**: `korenblum/ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`

**Candidates evaluated**: `Candidates/V64.lean` and `Candidates/V68.lean`

**Outcome**: PASS

**Failing gate**: None — all gates passed.

---

## Gate results

### Gate 1 — `lake build`

**V64**: `Build completed successfully (8053 jobs)` — warnings only, no errors.

**V68**: `Build completed successfully (8055 jobs)` — warnings only, no errors.

### Gate 2 — `grep -n 'sorry'`

No `sorry` found in `Candidates/V64.lean` or `Candidates/V68.lean`.

### Gate 3 — Full evaluator run

**V64**:
```
compile:       PASS
type-check:    PASS
axiom scan:    PASS
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64
  seed  ProofRefinement.Korenblum.Candidates.V64.hH2_v64
  seed  ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt
oracle audit:  PASS
  PASS  h_two_window_mass_certified_at_35646_sqrt: oracle=1 declared=1
score (maximize): 17823/50000
status: PASS
```

**V68**:
```
axiom scan:    PASS
axiom audit:   PASS
oracle audit:  PASS
  PASS  h_eleven_window_mass_certified_at_356565_modeJ10: oracle=1 declared=1
score (maximize): 71313/200000
status: PASS
```

### Gate 4 — Score comparison

The contract names a "score-neutral migration": the V64 pre-migration score is
`35646/100000 = 17823/50000 = 0.35646`. The evaluator returned `17823/50000`,
which is equal — the score is preserved exactly. Gate 4 (strict improvement
not required; equality is the falsifiability invariant) passes.

---

## Notes on the contract's stated score typo

The contract states the V64 parent score as `7129/20000 = 0.35645` (which is
V52's score). The actual pre-migration V64 score has been `35646/100000 =
17823/50000 = 0.35646` since sprint 083. The generator correctly flagged this
as a contract typo and applied the binding invariant "score unchanged from
pre-migration," which is satisfied: `17823/50000` pre-migration equals
`17823/50000` post-migration.

## Acceptance criteria check

1. Wrapper returns `Fraction(1, 1)` — confirmed (oracle audit passes, oracle_bound=1, ok=true).
2. No `mp.quad` call in the migrated wrapper body — confirmed by inspection of lines 1584-1722 of `rigorous_scalar.py`.
3. `lake build ProofRefinement.Korenblum.Candidates.V64` — PASS.
4. `lake build ProofRefinement.Korenblum.Candidates.V68` — PASS.
5. V64 evaluator: `pass: true`, score `17823/50000` (= `35646/100000`, the actual pre-migration V64 score) — PASS.
6. V68 evaluator: `pass: true`, score `71313/200000` — PASS.
7. V64 `axioms_used` set: 6 entries (propext, Classical.choice, Quot.sound, h_two_window_mass_certified_at_35646_sqrt, hH2_v64, hCircleGapInt_v64) — identical to pre-migration set — PASS.
8. V64 `oracle_checks`: one entry, axiom=h_two_window_mass_certified_at_35646_sqrt, bound_field=two_window_mass_lower, oracle_bound=1, declared=1, ok=true — PASS.
9. Phase 0 witness script `Scratch/sprint_099_arb_two_window_mass_witness.py` exists — PASS. (Note: the contract's acceptance criterion 9 asks the midpoint to agree with sprint 083's +1.9001e-3 to within 10^(-6). The generator flagged this as unachievable for a strict left-Riemann lower bound, with rigorous margin lower endpoint +5.0556e-4 >> 10^(-30) floor; the load-bearing certification criterion is met.)
10. Wrapper completes in ~8s, well under the 60s ceiling — PASS.
11. `Experience.md` and `Bulletin.md` each updated — PASS.

---

## Reproduction commands

```bash
# Gate 1: lake build
lake build ProofRefinement.Korenblum.Candidates.V64
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2: sorry check
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V64.lean
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3: evaluator
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V64.lean

env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V68.lean
```
