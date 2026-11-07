# Verdict: sprint_070_lift_circle_series_bridge_per_candidate_derived_theorem

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_070_lift_circle_series_bridge_per_candidate_derived_theorem.md`

**Candidate path**: `ProofRefinement/Korenblum/Candidates/V55.lean`
**Per-candidate derived theorem**: `ProofRefinement/Korenblum/Candidates/V55/LiftSeriesBridge.lean`

**Outcome**: PASS (Outcome A / Outcome C — Phase A succeeds with sign-corrected theorem set)

**Parent candidate**: `Candidates/V54.lean`, score `7129/20000`
**V55 score**: `7129/20000` — exact tie with V54, as required by contract.

---

## Gate results

### Gate 1 — `lake build`

```
lake build ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge
lake build ProofRefinement.Korenblum.Candidates.V55
```

Both succeed with `Build completed successfully`. Only linter warnings (unused
variables, `show`-tactic style, long lines) — no errors.

### Gate 2 — `grep -n 'sorry'`

```
grep -n 'sorry' \
  ProofRefinement/Korenblum/Candidates/V55.lean \
  ProofRefinement/Korenblum/Candidates/V55/LiftSeriesBridge.lean
```

No output. Both files are sorry-free.

### Gate 3 — Full evaluator

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V55.lean
```

Result:
```
compile:       PASS
type-check:    PASS
axiom scan:    PASS
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V55.hEq15_oracle_certified_hp_35645
oracle audit:  PASS
  PASS  hEq15_oracle_certified_hp_35645: oracle=1 declared=1
score (maximize): 7129/20000
status: PASS
```

Axiom envelope is `{propext, Classical.choice, Quot.sound,
hEq15_oracle_certified_hp_35645}` — byte-for-byte identical to V54's
envelope (same oracle, no new axioms).

### Gate 4 — Score comparison against parent

Parent V54 evaluator score: `7129/20000`.
V55 evaluator score: `7129/20000`.

Contract requires a score tie (Outcome A / C is a c-tying sprint by design).
Gate 4 passes.

---

## Sign-correction note

The sprint contract proposed orientation
`liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ`.

The generator determined this orientation is mathematically false: V54's
lift identity gives `‖b k − α·a k‖² − ‖a k − α·b k‖² = (1 − α²)(‖b k‖² −
‖a k‖²)`, so `liftGapSeries a b … − liftGapSeries b a …` equals
`−circleGapSeries a b ρ`. The shipped orientation is the sign-correct swap:

```
liftGapSeries b a (fun _ => α) ρ − liftGapSeries a b (fun _ => α) ρ
  = circleGapSeries a b ρ
```

This is accepted under Outcome C ("with smaller / sign-adjusted theorem set")
as documented in the sprint contract at §Outcome C. The generator disclosed
the correction fully in both `LiftSeriesBridge.lean` and `V55.lean`
docstrings. The structural value for downstream consumers is identical;
the next planner may re-orient any consumer that prefers the contract's
original swap (which equals `circleGapSeries b a ρ`). The sign correction
is a genuine mathematical fix of an error in the contract, not a workaround
or weakening of the theorem.

The side lemma `v55_lift_series_bridge_compiles_at_seed_witness` in
`V55.lean` exercises the sign-correct form and confirms the theorem
is non-vacuous and reusable.

---

## Failing gate

None.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge
lake build ProofRefinement.Korenblum.Candidates.V55

# Gate 2
grep -n 'sorry' \
  ProofRefinement/Korenblum/Candidates/V55.lean \
  ProofRefinement/Korenblum/Candidates/V55/LiftSeriesBridge.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V55.lean
```
