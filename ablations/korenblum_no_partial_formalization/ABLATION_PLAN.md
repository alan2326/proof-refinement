# Korenblum noPF Ablation — Comprehensive Plan

This document describes the construction of `ablations/korenblum_no_partial_formalization/`, a
sibling workspace to `korenblum/` that ablates the partial
formalization of Wang's Section 2 argument.

The science question: **does giving the agent a Lean-side partial formalization
of Wang (2025)'s numbered equations help the agent search for a larger Korenblum
constant κ?**

The two arms of the experiment:

| Arm | Workspace | Trust surface |
|---|---|---|
| With partial formalization | `korenblum/` | Wang Eq15 axiomatized at c=0.3554; rest of Wang's argument (eqs 2-14, reductions) is formalized in Lean. Agent uses oracle-backed Eq15 sub-claims at higher c, reduces through formalized chain. |
| Without partial formalization | `ablations/korenblum_no_partial_formalization/` | The entire Korenblum max principle axiomatized at c=0.3554, at the Bergman A² level. No formalized chain. Agent must either prove the Bergman A² theorem outright (essentially infeasible in Mathlib today) or add direct axioms at higher c. |

## What is Korenblum's max principle?

Wang (2025) proves κ_Korenblum ≥ 0.3554 where κ is the largest constant such
that for any pair of analytic, A²-integrable functions f, g on the open unit
disk 𝔻, the pointwise domination `|f(z)| ≤ |g(z)|` for all z with `c < |z| < 1`
implies `‖f‖_{A²} ≤ ‖g‖_{A²}` (i.e., `∫_𝔻 |f|² dA ≤ ∫_𝔻 |g|² dA`).

This is the **function-level** statement. It is the statement we want to make
the contract in the noPF arm.

The current `korenblum/` workspace expresses a **coefficient-level intermediate**:
given Wang's bundled hypotheses (`Section2Assumptions` containing 13 fields
encoding eqs 2-14), prove `diskExcess ≤ annulusExcess` at radius c. That
intermediate is exactly the partial formalization we are stripping.

---

## File layout overview

Source: `korenblum/`. Sibling target: `ablations/korenblum_no_partial_formalization/`.

### Files copied verbatim

- `lakefile.toml` — modified to drop `KorenblumPaper` lib target.
- `lake-manifest.json`, `lean-toolchain` — keep.
- `pyproject.toml`, `uv.lock`, `run_eval.sh`, `.gitignore` — keep.
- `CLAUDE.md` — modified to point at noPF workspace.
- `.claude/settings.local.json` — keep (any path references updated).

### Files modified

- `ProofRefinement/Korenblum/Proof/CandidateContract.lean` — rewritten for the
  Bergman-space-level contract (see Phase 1 below).
- `ProofRefinement/Korenblum/Candidates/V0.lean` — rewritten to use the new
  seed axiom directly.
- `ProofRefinement/Korenblum/lemma.toml` — strip `KorenblumPaper.*` workspace
  imports; replace seed axiom name; remove all `[[oracles]]` entries.
- `ProofRefinement.lean` — strip imports of removed modules.
- `ProofRefinement/Korenblum/AGENT_BRIEF.md` — rewritten for the
  Bergman-level contract; remove "read Wang2025 / KorenblumPaper for ideas"
  guidance; remove oracle workflow.
- `ProofRefinement/Korenblum/README.md`, `START_HERE.md` — rewritten.
- `ProofRefinement/Korenblum/CLAUDE.md` — updated.
- `.claude/agents/korenblum-refinement-{planner,generator,evaluator}.md` —
  update absolute path references from `korenblum/` to
  `ablations/korenblum_no_partial_formalization/`. Strip paper-side reading guidance. Strip
  oracle-related steps.
- `.claude/skills/run-next-korenblum-sprint/SKILL.md` — update path
  references.

### Files deleted

- All `KorenblumPaper/*.lean` (PaperAxioms, PaperEq15, OneMode*, Wang*,
  AnnulusIntegralReduction, CertificateCore, ConstantCertificateCore,
  FiniteModeWindow, ModeBridge — the entire paper-side library).
- `KorenblumPaper.lean` (root file).
- `Proof/Reduction.lean` (eq15 → final reduction).
- `Proof/ProblemAxioms.lean` (veneer over PaperAxioms — no longer needed).
- `Proof/Main.lean` (or stub it; it imports Reduction.lean which is gone).
- `Proof/DiskInnerSeriesBridge.lean`, `Proof/Integrability.lean`,
  `Proof/Summability.lean` (per-candidate derived theorems hoisted from
  V63 — depend on partial formalization).
- All `Candidates/V[1-9]*.lean` files and `Candidates/V*/` subdirs.
- `Numerical_Library/` (legacy paper-side oracle wrappers).
- All `Sprint_Contracts/sprint_*.md` (kept: `TEMPLATE.md`).
- All `Refinement_Log/log.jsonl` content (file truncated to empty).
- All `Proposals/` content except `README.md`.
- All `Scratch/` content.
- `Bulletin.md` reset to a blank initial entry.
- `Experience.md` reset to a blank initial entry.
- `V68_vs_Wang.md`, `Wang2025.pdf`, `Wang2025.txt`, `eval_v68_output.txt`,
  `AXIOM_EXTRACTION.md` — paper artifacts unrelated to the Bergman-level
  contract; not relevant to noPF.

### Files preserved as-is (workspace state)

- `Evaluator.py` — the candidate-side evaluator. Should work without
  modification because it reads `lemma.toml` declaratively and applies the
  trust-surface checks against whatever is listed there. (To verify after
  setup: run the evaluator on V0 and check it accepts.)
- `scripts/korenblum_*.sh` — wrappers around `lake build` and `Evaluator.py`.
  Do not reference `KorenblumPaper` directly.
- `docs/` — kept; may have minor references to update later.
- `ShinkaAblation/` — separate evolutionary search side-experiment. Keep
  copied for parity, but it operates on `initial.lean` independently and
  is not part of the harness loop.

---

## Phase 1 — The new contract

File: `ProofRefinement/Korenblum/Proof/CandidateContract.lean`

```lean
import Mathlib

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum

/-- The open complex unit disk. -/
def UnitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- Squared Bergman A² seminorm: ∫_𝔻 |f|² dA. -/
noncomputable def bergmanNormSq (f : ℂ → ℂ) : ℝ :=
  ∫ z in UnitDisk, ‖f z‖ ^ 2 ∂volume

/--
Korenblum maximum principle at radius `c`.

A real number `c ∈ (0,1)` is a valid Korenblum lower bound if, for every pair
of analytic A²-integrable functions `f`, `g` on the open unit disk such that
`|f(z)| ≤ |g(z)|` whenever `c < |z| < 1`, the A²-norm inequality
`‖f‖_{A²} ≤ ‖g‖_{A²}` holds.

This is the actual function-level Korenblum statement. There is no
intermediate coefficient-level reduction, no Wang Section 2 hypothesis bundle,
no formalized equation chain.
-/
def ValidKorenblumBound (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk →
      AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict UnitDisk) →
      (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      bergmanNormSq f ≤ bergmanNormSq g

end ProofRefinement.Korenblum
```

### Why this is rigorous

Every quantifier and every predicate in this statement refers to standard
real / complex / measure-theoretic objects already present in Mathlib:

| Symbol | Mathlib provenance |
|---|---|
| `ℂ`, `ℝ`, `ℕ`, basic arithmetic | core |
| `Metric.ball (0 : ℂ) 1` | `Mathlib.Topology.MetricSpace.Basic` |
| `AnalyticOn ℂ f S` | `Mathlib.Analysis.Analytic.Basic` |
| `Integrable f μ` | `Mathlib.MeasureTheory.Function.L1Space` |
| `volume` on ℂ (Lebesgue, via `ℂ ≃ ℝ²`) | `Mathlib.MeasureTheory.Constructions.BorelSpace.Complex` |
| `volume.restrict S` | `Mathlib.MeasureTheory.Measure.Restrict` |
| `∫ z in S, F z ∂μ` | `Mathlib.MeasureTheory.Integral.Bochner.Basic` |
| `‖·‖` on ℂ | `Complex.normedField` |

There is no hidden axiom, no hidden coefficient-level intermediate, no
Wang Section 2 bundle, and no oracle. The statement is exactly the Korenblum
max principle.

### Optional sanity property

Add (also in `CandidateContract.lean` or a sibling file):

```lean
/-- The bergman seminorm is monotone in pointwise norm domination on the
disk (a sanity check; not load-bearing for the contract). -/
theorem bergmanNormSq_mono_of_pointwise
    {f g : ℂ → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict UnitDisk))
    (hg : Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict UnitDisk))
    (h : ∀ z ∈ UnitDisk, ‖f z‖ ≤ ‖g z‖) :
    bergmanNormSq f ≤ bergmanNormSq g := by
  -- standard monotone integral; punt as `sorry` if Mathlib doesn't expose
  -- the exact lemma immediately, this is non-load-bearing.
  sorry
```

(Optional — can be omitted if Mathlib lookup is non-trivial. The main
`ValidKorenblumBound` definition is what matters.)

---

## Phase 2 — Strip everything else

Concrete deletion list (relative to `ablations/korenblum_no_partial_formalization/`):

```
KorenblumPaper/                              # entire dir
KorenblumPaper.lean                          # root
ProofRefinement/Korenblum/Proof/Reduction.lean
ProofRefinement/Korenblum/Proof/ProblemAxioms.lean
ProofRefinement/Korenblum/Proof/Main.lean    # rewrite to a stub
ProofRefinement/Korenblum/Proof/DiskInnerSeriesBridge.lean
ProofRefinement/Korenblum/Proof/Integrability.lean
ProofRefinement/Korenblum/Proof/Summability.lean
ProofRefinement/Korenblum/Candidates/V[1-9]*.lean
ProofRefinement/Korenblum/Candidates/V*/      # subdirs
ProofRefinement/Korenblum/Numerical_Library/  # legacy oracle code
ProofRefinement/Korenblum/Sprint_Contracts/sprint_*.md
ProofRefinement/Korenblum/Wang2025.pdf
ProofRefinement/Korenblum/Wang2025.txt
ProofRefinement/Korenblum/V68_vs_Wang.md
ProofRefinement/Korenblum/AXIOM_EXTRACTION.md
ProofRefinement/Korenblum/eval_v68_output.txt
```

Reset to empty / minimal:

```
ProofRefinement/Korenblum/Bulletin.md         → one-line initial entry
ProofRefinement/Korenblum/Experience.md       → blank header
ProofRefinement/Korenblum/Refinement_Log/log.jsonl → empty
ProofRefinement/Korenblum/Scratch/            → empty (dir only)
ProofRefinement/Korenblum/Proposals/          → empty (dir only, retain README.md if useful)
```

Preserve:

```
ProofRefinement/Korenblum/Sprint_Contracts/TEMPLATE.md
ProofRefinement/Korenblum/Evaluator.py
ProofRefinement/Korenblum/scripts/*.sh
ProofRefinement/Korenblum/docs/*.md
```

---

## Phase 3 — New seed `V0.lean`

File: `ProofRefinement/Korenblum/Candidates/V0.lean`

```lean
-- @parent seed
import ProofRefinement.Korenblum.Proof.CandidateContract

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V0

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value]
theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value]

/--
Seed external input: Wang (2025) proved the Korenblum maximum principle
holds at radius c = 0.3554 at the Bergman A² level. This single axiom
asserts the entire Wang theorem at this c.

Unlike the Wang-eq15 seed in the with-partial-formalization arm of the
ablation, this axiom asserts the full conclusion (not a sub-claim) because
this workspace contains no Lean-side reduction chain.
-/
axiom hKorenblum_published_3554 : ValidKorenblumBound ((3554 : ℝ) / 10000)

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V0
```

---

## Phase 4 — `lemma.toml`

```toml
name = "Korenblum Constant (noPF)"
slug = "korenblum_noPF"
paper_ref = "Korenblum max principle (Bergman A² level); Wang (2025) at c=0.3554"

sink_theorem = "korenblum_constant_search"
constant_def = "c_value"
score = "c_value"
score_direction = "maximize"

[search_constants]

[import_policy]
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Korenblum.Proof",
  "Mathlib",
]

[workspace_import_policy]
# No KorenblumPaper.* — the partial formalization is removed in this arm.
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[seed_axioms]
allowed = [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
  "Lean.trustCompiler",

  # Wang (2025) result, axiomatized at the Bergman A² level. The single
  # paper-side leaf in this ablation arm.
  "hKorenblum_published_3554",
]

# No oracles. The Bergman-level contract has no natural numerical sub-claim
# in this workspace.
```

---

## Phase 5 — Agent scaffolding

### `AGENT_BRIEF.md`

Rewrite to describe:

- The Bergman-level contract (`ValidKorenblumBound c`).
- That this is the **noPF ablation arm**: no partial formalization is
  available. The agent has only the contract and the seed axiom.
- The agent's options for improvement:
  1. Add a new direct axiom at higher c (must be listed in
     `[seed_axioms].allowed`). Honest path but does not advance the science.
  2. Prove the Bergman A² Korenblum max principle outright in Lean — this
     would require building Bergman space theory, the annulus
     pseudohyperbolic distance, and Wang-style or alternative arguments
     against Mathlib. Likely infeasible in a single sprint budget.
  3. Re-introduce a partial formalization of one's own design — this is
     allowed but defeats the ablation; flag in Bulletin if attempted.
- Removed sections: paper-side reading guidance ("read Wang2025.pdf,
  KorenblumPaper modules"), oracle workflow, Eq15 framing.

### `.claude/agents/korenblum-refinement-{planner,generator,evaluator}.md`

Update three agent definitions:

- Replace `korenblum/` with `ablations/korenblum_no_partial_formalization/`.
- Strip "Read for ideas" sections that point at `KorenblumPaper/` or
  `Wang2025.pdf` — those don't exist here.
- Strip oracle-workflow guidance (no oracles).
- Keep the rest of the planner/generator/evaluator workflow unchanged
  (the harness mechanics — sprint contracts, refinement log, candidate
  build, evaluator gate — are arm-independent).

### `.claude/skills/run-next-korenblum-sprint/SKILL.md`

- Update any path references.
- Workflow unchanged (preflight → planner → generator → evaluator).

### `scripts/`

- `korenblum_harness_preflight.sh` — should work unchanged. Verify it
  doesn't reference `KorenblumPaper`.
- `korenblum_eval_candidate.sh`, `korenblum_lake_build.sh` — verify.
- `korenblum_checkpoint_*.sh` — verify.

(If any script hard-codes `korenblum/`, update to
`ablations/korenblum_no_partial_formalization/`.)

---

## Phase 6 — Reset workspace state

Empty out:

```
Bulletin.md                  → "## Initial entry\nnoPF ablation workspace seeded with Wang 2025 at c=0.3554.\n"
Experience.md                → "# Experience log (noPF arm)\n\n_initial state, no entries yet_\n"
Refinement_Log/log.jsonl     → ""
Sprint_Contracts/sprint_*.md → deleted (kept TEMPLATE.md)
Proposals/*.md               → deleted (kept README.md if it has structure)
Scratch/                     → empty dir
```

---

## Phase 7 — `ABLATION_NOTES.md`

After the workspace is constructed, write `ABLATION_NOTES.md` covering:

1. **Trust surface comparison.** The seed axiom changed from
   `hEq15_seed_3554` (asserting one numerical inequality, with eqs 2-14 in
   `Section2Assumptions` and a Lean-formalized chain to the conclusion) to
   `hKorenblum_published_3554` (asserting the entire Bergman A² Korenblum
   max principle at c=0.3554). The latter is a strictly larger leaf of
   trust — the *whole* paper, not one inequality.
2. **Mathlib volume measure on ℂ.** The Lebesgue measure on ℂ is realized
   in Mathlib via `Complex.measureSpace` (or the `MeasurableEquiv ℂ ℝ²`
   pull-back). The contract uses `volume.restrict UnitDisk` which compiles
   correctly. Verified by `lake build`.
3. **Paper-boundary gap.** The Lean formalization in this arm has *one*
   paper-boundary axiom: `hKorenblum_published_3554`. There is no other
   external mathematical content. This is honest about the gap that the
   noPF agent must work against.
4. **Why this ablation is asymmetric.** Adding axioms is technically free,
   so the harness gate's job is to flag direct-conclusion axioms as
   non-progress. The expectation is: with PF, agent makes
   numerically-verified incremental gains; without PF, agent stagnates
   or shortcuts. Either result confirms the value of partial
   formalization.
5. **Open uncertainties.** Ones I'm flagging now (to be resolved during
   implementation):
   - Whether `volume.restrict UnitDisk` typechecks with the right
     measure-on-ℂ instance, or whether we need
     `(MeasureTheory.volume : Measure ℂ).restrict UnitDisk` explicitly.
   - Whether `bergmanNormSq` should use `‖z‖^2` or `Complex.normSq z`
     (the latter gives `‖z‖² = re² + im²` more directly; both are
     equivalent up to definitional unfolding).
   - Whether the Evaluator's axiom-counting logic can be left unchanged
     after we strip `Numerical_Library/` and the `[[oracles]]` entries.
     Most likely yes (the Evaluator reads `lemma.toml` declaratively),
     but verify.
   - Whether keeping `ShinkaAblation/` makes sense — it operates
     independently on `initial.lean` and is not part of the agent loop.
     Default: keep for parity but document that it's not exercised by
     the harness in this arm.

---

## Implementation order

1. Copy source → target (excluding `.lake`, `.venv`, `.uv-cache`, `.git`).
2. Delete files per Phase 2.
3. Write Phase 1 contract (`CandidateContract.lean`).
4. Write Phase 3 seed (`V0.lean`).
5. Write Phase 4 `lemma.toml`.
6. Stub `Proof/Main.lean` to a one-line entrypoint.
7. Update `ProofRefinement.lean` root to import only the new modules.
8. Update `lakefile.toml` to drop `KorenblumPaper`.
9. Update `KorenblumPaper.lean` root → delete.
10. Reset workspace state (Phase 6).
11. Update Phase 5 agent scaffolding.
12. Run `lake build` to confirm the contract typechecks (target:
    `ProofRefinement.Korenblum.Candidates.V0`).
13. If build is broken at step 12, debug (most likely Mathlib lookup
    issues for `volume` on ℂ, `Integrable`, `AnalyticOn`).
14. Write `ABLATION_NOTES.md`.

After implementation, the user runs the harness from `ablations/korenblum_no_partial_formalization/`
and observes agent behavior under the stripped trust surface.

---

## Difficulty estimate

| Phase | Effort | Risk |
|---|---|---|
| 1 — Bergman contract | 15 min | Low (Mathlib lookups for `volume` on ℂ) |
| 2 — file deletes | 10 min | Trivial |
| 3 — seed | 5 min | Trivial |
| 4 — lemma.toml | 5 min | Trivial |
| 5 — agent scaffolding | 15 min | Trivial (path edits) |
| 6 — reset state | 5 min | Trivial |
| 7 — ABLATION_NOTES.md | 10 min | Trivial |
| 12 — `lake build` | 10-30 min | **Medium** — first build is slow; may surface a Mathlib volume/integrable issue requiring 1-2 small tweaks |

Total: ~1 hour, dominated by the cold `lake build`.

The largest unknown is whether `volume.restrict UnitDisk` and `Integrable
(fun z => ‖f z‖ ^ 2) (volume.restrict UnitDisk)` typecheck against Mathlib's
current ℂ measure-space instance without finagling. If they don't, two
small known fixes:

- Use `MeasureSpace.volume` explicitly: `(volume : Measure ℂ).restrict UnitDisk`.
- Use `Complex.measureSpace` instance imports.

Both are minor. Worst case I add a `sorry`-free workaround using `MeasurableEquiv
ℂ ℝ²` to push everything to ℝ². Confidence in successful Phase 12: high.
