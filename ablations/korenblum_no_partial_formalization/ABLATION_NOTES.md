# noPF Ablation — Notes for Inspection

This file is the human-facing inspection log for the
`ablations/korenblum_no_partial_formalization/` workspace. The companion design document is
`ABLATION_PLAN.md`.

## What was built

A sibling Korenblum harness workspace with the partial formalization
stripped. The candidate contract is now stated at the **function-level
Bergman A² Korenblum maximum principle**, not at the coefficient-level
disk-vs-annulus intermediate.

```
ablations/korenblum_no_partial_formalization/
├── ProofRefinement/Korenblum/
│   ├── Proof/CandidateContract.lean       # ← THE CONTRACT (full content below)
│   ├── Candidates/V0.lean                  # ← seed (one direct axiom)
│   ├── lemma.toml                          # ← trust surface
│   ├── AGENT_BRIEF.md                      # ← rewritten for noPF arm
│   ├── README.md                           # ← rewritten
│   ├── Bulletin.md, Experience.md, Refinement_Log/, Sprint_Contracts/
│   │                                        ← reset to initial state
│   ├── Proposals/, Scratch/                ← reset
│   ├── docs/                               ← carried over (may have stale refs)
│   ├── scripts/                            ← unchanged
│   └── Evaluator.py                        ← unchanged
├── .claude/agents/korenblum-refinement-{planner,generator,evaluator}.md
│                                            ← rewritten for noPF arm
├── .claude/skills/run-next-korenblum-sprint/SKILL.md
│                                            ← unchanged (path-relative)
├── lakefile.toml                           ← KorenblumPaper lib dropped
├── ProofRefinement.lean                    ← imports trimmed
├── CLAUDE.md                               ← rewritten
└── ABLATION_PLAN.md, ABLATION_NOTES.md     ← design + inspection
```

## The contract

```lean
def UnitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

noncomputable def bergmanNormSq (f : ℂ → ℂ) : ℝ :=
  ∫ z in UnitDisk, ‖f z‖ ^ 2 ∂(volume : Measure ℂ)

def ValidKorenblumBound (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk →
      AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      bergmanNormSq f ≤ bergmanNormSq g
```

This is exactly the function-level Korenblum max principle. Every term
references standard Mathlib (`Metric.ball`, `AnalyticOn`, `Integrable`,
`volume`, `MeasureTheory.integral`). No coefficient-level intermediate, no
Wang Section 2 hypothesis bundle, no equation chain.

## Verified working state

The seed candidate `Candidates/V0.lean` builds cleanly and the evaluator
passes:

```
$ lake build ProofRefinement.Korenblum.Candidates.V0
Build completed successfully (8027 jobs).

$ uv run Evaluator.py --file Candidates/V0.lean --skip-oracle
workspace imports: PASS
import audit:      PASS
compile:           PASS (8.33s)
type-check:        PASS (6.26s)
axiom scan:        PASS (7.61s)
axiom audit:       PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V0.hKorenblum_published_3554
score (maximize):  1777/5000
status:            PASS
```

The seed depends on exactly one paper-trusted axiom
(`hKorenblum_published_3554`) plus standard Lean axioms. No `sorryAx`. No
oracle.

## Trust surface comparison

| Property | `korenblum/` (with PF) | `korenblum_noPF/` (this arm) |
|---|---|---|
| Contract level | Coefficient-level (disk-vs-annulus on `(a, b, K)` satisfying eqs 2-14) | Function-level Bergman A² (`f, g : ℂ → ℂ` analytic, `‖f‖ ≤ ‖g‖` on outer annulus) |
| Lean-side scaffolding | `KorenblumPaper.PaperAxioms`, `PaperEq15`, `OneModePaperBridge`, `Wang*.lean`, `OneMode*.lean`, `Reduction.lean` | none |
| Numerical infrastructure | `Numerical_Library/` with mp.quad wrappers, oracle registrations | none |
| Seed axiom | `hEq15_seed_3554`: ONE numerical inequality (Wang Eq 15) at c=0.3554 | `hKorenblum_published_3554`: THE FULL Korenblum max principle at c=0.3554 |
| Trust leaf size | One numerical leaf; rest of Wang chain in Lean | Whole theorem |
| Improvement mechanism | Oracle-backed numerical sub-claims at higher c, reduced through Lean chain | Direct proof against Mathlib (very hard) OR direct-conclusion axiom (cheap shortcut) |

The seed in this arm asserts **strictly more** than the seed in the
companion arm. That asymmetry is the entire point — without partial
formalization, the agent has no reduction to lean on.

## Open uncertainties (please inspect)

### 1. ShinkaAblation/ left untouched

The `ShinkaAblation/` directory was copied verbatim. Its scripts hardcode
`korenblum/...` paths in `build_task_prompt.py`,
`run_evo.py`, and `README.md`. ShinkaAblation is not part of the
planner/generator/evaluator harness loop — it is a separate evolutionary
search side-experiment that operates on `initial.lean`. If you want to
also ablate ShinkaAblation, those paths need updating; currently it
would still target the with-PF workspace if invoked. Default assumption:
not exercised by the harness in this arm. Flag if this is wrong.

### 2. The `volume` measure on ℂ

The contract uses `(volume : Measure ℂ).restrict UnitDisk`. Mathlib
provides this through the `MeasureSpace ℂ` instance (Lebesgue on ℂ via
the standard `ℂ ≃ₗᵢ[ℝ] ℝ²` identification). The build went through clean,
so this is correctly resolved. If you want to spot-check, look at:

- `Mathlib.MeasureTheory.Constructions.BorelSpace.Complex`
- `Complex.measureSpace`

There is a 2π / Jacobian normalization choice implicit in the integral
`∫_𝔻 |f|² dA`. Mathlib's `volume` on ℂ gives the standard 2D Lebesgue
measure (no scaling). Different sources sometimes scale by `1/π`. For the
Korenblum statement, *only the inequality* `bergmanNormSq f ≤ bergmanNormSq g`
matters, and that is invariant under any positive scalar — so the choice
of convention is immaterial for the theorem statement.

### 3. The seed axiom asserts the entire conclusion

`hKorenblum_published_3554 : ValidKorenblumBound (3554/10000)` is the
full Korenblum max principle at c=0.3554. Wang (2025) proves this, so
the axiom is mathematically true. But it is a *much larger* trust leaf
than the with-PF arm's `hEq15_seed_3554`, which only asserts one
numerical inequality and lets Lean derive the rest. This is the design
of the ablation — strip the partial formalization and the trust leaf
balloons.

### 4. The agent's improvement mechanism is asymmetric

In the with-PF arm, the agent can register oracle wrappers for
numerical Eq15-style sub-claims at higher c, and the Lean reduction chain
turns those into a proof of the conclusion. The trust leaf grows by
small certified pieces.

In this arm there is no chain. The agent's options are:

a. **Prove `ValidKorenblumBound c` for a larger `c` directly against
   Mathlib.** This is the science-advancing path. Hard — Mathlib has
   `AnalyticOn`, `MeasureTheory`, but no Bergman A² theory, no annulus
   pseudohyperbolic distance, no Wang-style apparatus. Likely
   infeasible in single sprints; possible only with substantial
   infrastructure investment.

b. **Add another direct-conclusion axiom at higher `c`** (e.g.
   `hKorenblum_seed_36 : ValidKorenblumBound (36/100)`). Mechanically
   allowed if listed in `[seed_axioms].allowed`. Gives a c-bump but
   does not advance the science — the trust leaf just gets bigger.

c. **Reconstruct a partial formalization on top of Mathlib.** Build,
   in Lean, the apparatus that was stripped. This is allowed (per
   `AGENT_BRIEF.md`) but rebuilds what the ablation removed.

Expected experimental signal:

- If the agent improves through (a), the ablation is *unfavourable* to
  the science question (the partial formalization wasn't needed).
- If the agent improves through (b), the ablation reveals a *gating
  failure* (direct axiomatization shouldn't be considered progress).
- If the agent improves through (c), the ablation confirms the
  *value* of partial formalization (the agent had to rebuild it
  itself).
- If the agent stagnates, the ablation also confirms value (without
  partial formalization, no progress).

The interesting outcomes are (c) and stagnation.

### 5. The Evaluator's axiom-counting

`Evaluator.py` reads `lemma.toml` declaratively. Its `[seed_axioms]`
check enforces that every `axiom` symbol referenced by the candidate
either is in the allow-list or matches a registered oracle. Removing
`Numerical_Library/` and all `[[oracles]]` entries from `lemma.toml`
appears to work — the V0 evaluator run passed without complaint. If a
later sprint introduces a new axiom, the Evaluator will reject it
unless the planner adds it to `[seed_axioms].allowed`. Verified by the
clean V0 evaluator run logged above.

### 6. The Sprint_Contracts/TEMPLATE.md still mentions `(15)` indirectly

It now reads "function-level Bergman A² Korenblum max principle" but
the rest of the template's structure is unchanged. The planner agent
should naturally fill in noPF-appropriate language. If the template
needs a more aggressive rewrite, flag it.

### 7. docs/ folder retained as-is

`ProofRefinement/Korenblum/docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md`
and other doc files were copied without modification. They likely
contain references to `KorenblumPaper`, `Section2Assumptions`, and
Wang Eq 15. The agents read these from time to time. If you want
strict noPF discipline on the docs side too, those need a sweep —
ABOUT 2-3 files, none of which are load-bearing for the build but
which might confuse the agent. The high-traffic docs (AGENT_BRIEF,
README, agent definitions) have all been rewritten.

### 8. Hardlinked .lake (build cache)

To speed the cold build, `.lake` was hardlink-copied from
`korenblum/.lake`. This shares Mathlib's pre-built
`.olean` files between the two workspaces. The hardlinking is safe
because Mathlib's olean files are content-addressed — neither workspace
will mutate them. If you ever run `lake clean` or `lake update` in
*either* workspace, the link is broken and that workspace will rebuild
its dependencies independently.

### 9. The `change` tactic in V0

V0 uses `change ValidKorenblumBound ((3554 : ℝ) / 10000)` to rewrite
the goal to the literal form before applying `hKorenblum_published_3554`.
This is required because `c_value : ℝ := 3554 / 10000` doesn't reduce
defeq to the `(3554 : ℝ) / 10000` shape the axiom is stated in. Could
also be done with `unfold c_value` or by stating the axiom over `c_value`
directly. Cosmetic, not load-bearing.

## How to run the harness in this arm

```bash
cd ablations/korenblum_no_partial_formalization
# from a Claude Code session inside this directory:
/run-next-korenblum-sprint
# or for a full autonomous loop:
/loop 30m /run-next-korenblum-sprint
```

The harness wiring is identical to the with-PF arm. Only the trust
surface and the contract's mathematical level differ.

## Quick build verification

```bash
cd ablations/korenblum_no_partial_formalization
lake build ProofRefinement.Korenblum.Candidates.V0
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V0.lean \
  --skip-oracle --no-log
```

Expected: V0 builds, evaluator returns `status: PASS` with score
`1777/5000`, four axioms (`propext`, `Classical.choice`, `Quot.sound`,
`hKorenblum_published_3554`).
