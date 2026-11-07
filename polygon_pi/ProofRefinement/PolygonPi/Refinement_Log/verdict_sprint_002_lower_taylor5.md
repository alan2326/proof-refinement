# verdict — sprint_002_lower_taylor5

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_002_lower_taylor5.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V2.lean` (+ derived `Candidates/V2/Taylor.lean`)
- **Rung type:** `architectural`
- **Side:** `lower`
- **Outcome:** PASS
- **Failing gate:** none

## Gate results

1. **Write scope.** OK. Sprint-caused edits are confined to `Candidates/V2.lean`,
   `Candidates/V2/Taylor.lean`, `Experience.md`, `Bulletin.md`, and the evaluator's
   append to `Refinement_Log/log.jsonl`. The other tracked diffs in the working tree
   (`Candidates/V1.lean`, deletions of old V2-V5 artifacts, sprint contracts,
   `Scratch/`, `.claude/agents/*.md` `model:` field diff, and the earlier V0/V1
   log entries) belong to the deliberate harness reset that preceded this sprint —
   explicitly acknowledged by the launching agent — not to this candidate.
2. **Build.** `scripts/polygonpi_lake_build.sh V2` → "Build completed successfully
   (2161 jobs)".
3. **No forbidden constructs.** Grep hits only a doc-comment line in
   `Candidates/V2/Taylor.lean` that documents "No `axiom`, `opaque`,
   `native_decide`, or `sorry`" — no real construct in either file.
4. **Full evaluator.** `scripts/polygonpi_eval_candidate.sh V2` — all twelve stages
   PASS (workspace imports, candidate imports, transitive import closure = 2146
   modules with no blocked entries, static scan, declarations
   `lambda=1/4, kappa=2/3`, compile 2.63 s, type check 3.19 s, secondary contract
   SKIP, axiom scan + audit, oracle table empty, score record, log append).
5. **Contract-declared inequality.** `strict_improvement=True` as required
   (score `5/12` strictly below parent incumbent `2/3`).
6. **Axiom closure.** Reported closure is exactly
   `{propext, Classical.choice, Quot.sound}` — subset of the allowed set.

## Metrics

- `score`: `5/12` (≈ 0.4166666667)
- `interval width at depth 10`: `5/12582912` (≈ 3.973643e-07)
- `incumbent` (parent): `2/3`
- `strict_improvement`: `true`
- `axioms_used`: `["Classical.choice", "Quot.sound", "propext"]`

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V2
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V2
```
