# Verdict: sprint_087_v38_seven_window_mass_oracle_phase0_and_wrapper

**Contract**:
`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_087_v38_seven_window_mass_oracle_phase0_and_wrapper.md`

**Candidate**: `ProofRefinement/Korenblum/Candidates/V65.lean`
(This sprint is infrastructure-only; V65 is the regression target, not a new candidate.)

**Outcome**: PASS

**Failing gate**: None — all four gates passed.

---

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V65`
PASS — `Build completed successfully (8053 jobs)`. Warnings only (style linter, unused variables); no errors.

### Gate 2: `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V65.lean`
PASS — no matches.

### Gate 3: Evaluator run
PASS — evaluator reports `status: PASS`, `score: 17823/50000`, axiom audit clean.
Axioms used: `propext`, `Classical.choice`, `Quot.sound`, `hCircleGapInt_v64`, `hH2_v64`, `h_two_window_mass_certified_at_35646_sqrt` (all pre-existing seeds).
Oracle audit: `h_two_window_mass_certified_at_35646_sqrt: oracle=1 declared=1` (PASS).
The new `h_seven_window_mass_certified_at_356562_sqrt` oracle row does NOT leak into V65's axiom set.

### Gate 4: Parent score comparison
Not applicable — this sprint ships no new candidate. The contract explicitly states V65 remains at `35646/100000`; confirmed score `17823/50000 = 35646/100000`.

---

## Sprint infrastructure delivered

- **Phase 0 sweep**: `Scratch/sprint_087_v38_seven_window_mass_sweep.{py,txt}` — Phase 0 GO at `c = 178281/500000` (= 356562/1000000), margin +1.19998e-4, full-envelope `(dps=80, n_trunc=300)` re-verified.
- **Wrapper**: `certify_seven_window_mass_at_356562_sqrt` added to `Numerical_Library/rigorous_scalar.py` (line 1483), returns `Fraction(1, 1)`.
- **lemma.toml**: `h_seven_window_mass_certified_at_356562_sqrt` added to `[seed_axioms].allowed` (line 190) and `[[oracles]]` row at lines 407-409.
- **Lean axiom + helpers**: `v66CValue`, `v66SevenWindowKind`, `v66SevenWindowStart`, `v66SevenWindowStop`, `h_seven_window_mass_certified_at_356562_sqrt` added to `Proof/Reduction.lean` (lines 9487-9555). `Proof.Reduction` builds cleanly.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V65

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V65.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V65.lean
```

---

**STATUS=VERDICT_PASS**
