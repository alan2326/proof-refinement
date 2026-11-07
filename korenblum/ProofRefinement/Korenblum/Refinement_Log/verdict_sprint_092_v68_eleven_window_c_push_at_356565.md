# Verdict: sprint_092_v68_eleven_window_c_push_at_356565

**Contract path**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_092_v68_eleven_window_c_push_at_356565.md`

**Candidate path**: `korenblum/ProofRefinement/Korenblum/Candidates/V68.lean`

**Derived-theorem file**: `korenblum/ProofRefinement/Korenblum/Candidates/V68/ElevenWindowEndpoints.lean` (831 lines)

**Outcome**: PASS

**Failing gate**: none — all four gates passed.

---

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V68`

PASS. `Build completed successfully (8055 jobs).` No errors; only pre-existing linter warnings in `KorenblumPaper/`.

Reproduction:
```bash
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V68 2>&1 | grep -E '(error|Build completed|failed)'
```

### Gate 2: `grep -n 'sorry' Candidates/V68.lean`

PASS. No `sorry` in `V68.lean` (exit code 1 = no match). `ElevenWindowEndpoints.lean` contains one comment line mentioning `sorry` (line 18: `-- Contents (no \`axiom\`s, no \`sorry\`s):`); no actual `sorry` tactic usage.

Reproduction:
```bash
grep -n '\bsorry\b' korenblum/ProofRefinement/Korenblum/Candidates/V68.lean
grep -n '\bsorry\b' korenblum/ProofRefinement/Korenblum/Candidates/V68/ElevenWindowEndpoints.lean
```

### Gate 3: Full evaluator run

PASS. Full output:

```
compile:       PASS (79.45s)
type-check:    PASS (87.58s)
axiom scan:    PASS (81.94s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10
  seed  ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68
  seed  ProofRefinement.Korenblum.Candidates.V68.hH2_v68
oracle audit:  PASS
  PASS  h_eleven_window_mass_certified_at_356565_modeJ10: oracle=1 declared=1
score (maximize): 71313/200000
status: PASS
```

Reproduction:
```bash
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```

### Gate 4: Strict parent improvement

PASS. V68 score `71313/200000 = 356565/1000000` strictly exceeds parent V67 score `89141/250000 = 356564/1000000`.

Arithmetic check: 71313 * 250000 = 17,828,250,000 > 17,828,200,000 = 89141 * 200000. Difference = +1/1000000 = +1e-6.

Reproduction:
```bash
python3 -c "from fractions import Fraction; v67=Fraction(89141,250000); v68=Fraction(71313,200000); print(v68>v67, v68-v67)"
```

---

## Audit summary

- **axioms_used**: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`, `ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68`, `ProofRefinement.Korenblum.Candidates.V68.hH2_v68`. No `sorryAx`, no extra free axioms.
- **Oracle**: `h_eleven_window_mass_certified_at_356565_modeJ10` — `oracle=1 declared=1 ok=true`. Bound field `eleven_window_mass_lower = 1` matches.
- **Audit extends V67 by exactly one entry**: V67 used `h_eight_window_mass_certified_at_356564_modeJ7`; V68 replaces it with `h_eleven_window_mass_certified_at_356565_modeJ10` (the old oracle is gone from the V68 audit set; V68's set has the three analogous entries plus the new oracle instead — net +1 oracle vs V67's audit envelope, consistent with contract requirement).
- **Score logged**: `log.jsonl` last entry confirms `candidate: Candidates/V68.lean`, `score: 71313/200000`, `pass: true`.
