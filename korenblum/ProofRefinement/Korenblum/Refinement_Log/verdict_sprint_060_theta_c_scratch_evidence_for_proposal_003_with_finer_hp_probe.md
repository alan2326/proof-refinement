# Verdict: sprint_060_theta_c_scratch_evidence_for_proposal_003_with_finer_hp_probe

**Contract**:
`ProofRefinement/Korenblum/Sprint_Contracts/sprint_060_theta_c_scratch_evidence_for_proposal_003_with_finer_hp_probe.md`

**Candidate**: `ProofRefinement/Korenblum/Candidates/V52.lean` (parent; no V53 shipped — Phase A all-reject as predicted)

**Outcome**: PASS (preparatory c-tie sprint; score ties V52 at 7129/20000)

**Failing gate**: none — all gates pass

---

## Gate results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V52`

PASS. Build completes successfully (8049 jobs). Only linter warnings about unused variables in `Reduction.lean` — no errors.

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V52
```

### Gate 2 — `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V52.lean`

PASS. No output (no `sorry` in the candidate file).

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V52.lean
```

### Gate 3 — Evaluator

PASS. Full evaluator output:

- `compile`: PASS
- `type-check`: PASS
- `axiom scan`: PASS
- `axiom audit`: PASS — `axioms_used = {propext, Classical.choice, Quot.sound, hEq15_oracle_certified_hp_35645}`
- `oracle audit`: PASS — `hEq15_oracle_certified_hp_35645: oracle=1 declared=1`
- `score (maximize)`: `7129/20000`
- `status`: PASS

Reproduction:
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V52.lean
```

### Gate 4 — Score comparison vs parent

This sprint is a preparatory c-tie sprint. The contract (AC §8) explicitly justifies the c-tie per Bulletin lines 27–31. No strict score improvement is required. V52's score in `log.jsonl` is `7129/20000`; current score is `7129/20000`. Gate 4 is inapplicable (no V53 shipped, no strict improvement claimed).

---

## Acceptance criteria check

- **AC §1** (Phase A scratch artefacts): PASS. Both
  `Scratch/sprint_060_finer_hp_probe_35646_35647_35648.py` and `.txt` exist.
  The txt reports all 5 calls (3 finer-denominator probes + 2 regressions):
  c=35646/100000 → False (margin -2.19e-04),
  c=35647/100000 → False (margin -4.51e-04),
  c=35648/100000 → False (margin -6.83e-04),
  c=35645/100000 → True (margin +1.35e-05, regression PASS),
  c=3565/10000 → False (margin -1.15e-03, regression PASS).

- **AC §2** (Phase A success branch Lean materialisation): NOT APPLICABLE. All three probes rejected; V53 was not shipped per contract.

- **AC §3** (Phase B primary deliverable): PASS.
  Both `Scratch/sprint_060_theta_c_canonical_extremals.py` and `.txt` exist.
  The txt reports the full tabular `(c, family, α², |f|≤|g|?, Σ⁺(c), Σ⁻(c), θ_emp)` for the contract's 4-family × 6-c × 5-α² grid (with admissibility-excluded rows marked).
  Per-c sup θ_emp footer present (6 rows, one per c value in {0.355, …, 0.36}).
  One-line verdict per c present (outcome (a)/(b)/(c) classification).
  Load-bearing c=0.36 verdict: outcome (a) supports, sup θ_emp = 0.857 < 1 - 1e-3.

- **AC §4** (outcome (c) check): PASS. No (family, α²) triple exhibits θ_emp > 1 while admissible. Outcome (c) is not observed; Experience.md explicitly notes this and honestly discloses the boundary asymptotics (θ_emp → 1 as α² → α²_max).

- **AC §5** (Bulletin.md and Experience.md updates): PASS. Bulletin.md has two sprint_060 rows at the bottom of Recent events (Phase A all-reject PASS preparatory; Phase B outcome (a) supports). Experience.md has a full `### 2026-05-02 sprint_060` section with the HP probe table, θ_emp table, c-tie justification (citing specific Scratch artefacts and Bulletin/proposal lines per AC §8 requirements), honest disclosure, and next-sprint-061 conditional plan.

- **AC §6** (no edits to protected files): PASS. No edits to `KorenblumPaper/`, `Proof/Reduction.lean`, `Proof/CandidateContract.lean`, `Proof/Main.lean`, `Section2Assumptions`, or any `Candidates/V0.lean` through `Candidates/V52.lean`. No new `Proposals/proposal_NNN_*.md` filed. No existing proposal Status fields edited. No edits to `lemma.toml`, `Numerical_Library/rigorous_scalar.py` (these are in the Phase A success branch only, which did not trigger).

- **AC §7** (per-c axiom uniqueness, Phase A success branch only): NOT APPLICABLE. V53 not shipped.

- **AC §8** (c-tie justification): PASS. Experience.md's sprint_060 section explicitly justifies the c-tie citing:
  (i) Slope-extrapolated rejection prediction from sprints 057/058/059 data, citing `Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt`;
  (ii) No other c-pushing reducer in `Reduction.lean` reachable without trust-base expansion, citing `sprint_048_branch2_kernel.txt`, `sprint_048_full_window_kernel.txt`, `sprint_049_paper_eq15_direct_kernel.txt`, `sprint_051_per_k_series_kernel_canonical_extremals.txt`, and Bulletin line 365;
  (iii) proposal_003 pending Alan review as the only remaining route to c > 0.35650, and Phase B's role in unblocking its review, citing proposal_003 lines 366–437 and 412–421.

---

## Summary

Sprint 060 is a two-phase preparatory sprint. Phase A confirmed the HP-tier ceiling at c=35645/100000 (V52) — all three finer-denominator probes rejected as slope-predicted, no V53 ships. Phase B produced the primary deliverable: numerical θ(c) data on canonical E0–E3 extremals supporting proposal_003, with outcome (a) at all c-values in the sweep (sup θ_emp(c=0.36) = 0.857, well below the 1-1e-3 threshold). The c-tie with V52 is justified per Bulletin lines 27–31 and AC §8. All gates pass.

**STATUS=VERDICT_PASS**
**Score: 7129/20000**
