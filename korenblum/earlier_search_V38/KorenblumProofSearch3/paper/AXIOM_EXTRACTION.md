# Wang 2025 Axiom Extraction

This note documents the current Section 2 paper interface in
[PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean).

Paper sources:

- [Wang2025.pdf](grothendieck/KorenblumProofSearch3/paper/Wang2025.pdf)
- [Wang2025.txt](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt)

## Current Status

The old design in this workspace used global Lean axioms such as
`eq3_circleGap_decomposition`, `eq4_sigmaPlus_bound`, and
`eq8_sigma_to_liftGap` quantified over arbitrary functions. That design was
unsound: those axioms could be instantiated against unrelated placeholders.

The current file has been rebuilt around two structures:

- [Section2Objects](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:219),
  which fixes the paper scale parameter `a(\rho)` as `liftScale`
- [Section2Assumptions](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:244),
  whose fields are the paper equations `(2)` through `(14)` attached to those
  fixed objects

The actual gap quantities are now concrete definitions:

- `circleGap a b`
- `liftGapSeries a b liftScale`
- `diskExcess (circleGap a b) c`
- `annulusLeftExcess (circleGap a b) c`
- `annulusRightExcess (circleGap a b) c`
- `annulusExcess (circleGap a b) c`

So the paper interface is now sounder in the following sense:

- there are no longer global axioms about arbitrary functions
- the equations are hypotheses about a single coherent Wang Section 2 context
- convenience bridges can still be proved in Lean from those fields

## Fixed Definitions

### Coefficient-side definitions

The following Lean definitions are direct paper notation, not axioms:

- `n1Pred`:
  Wang's `N1 = {k ∈ N : |a_k| ≥ |b_k|} ∪ {0}`
- `n2Pred`:
  Wang's `N2 = {k ∈ N : |a_k| < |b_k|}`
- `sigmaPlus`:
  Wang's `Σ⁺(s)`
- `sigmaMinus`:
  Wang's `Σ⁻(s)`
- `sigmaZeroMinus`:
  Wang's `Σ⁻₀(s)`
- `circleGapSeries`:
  the normalized boundary excess written in coefficient form in equation `(3)`
- `circleGap`:
  the concrete Section 2 boundary excess attached to the coefficients
- `liftGapSeries`:
  the concrete Section 2 lifted-gap series for a chosen scale `a(\rho)`

These are definitional copies of the paper notation and do not introduce any
paper assumptions by themselves.

## Section2Assumptions Fields

The structure
[Section2Assumptions](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:244)
contains one field for each currently exposed paper equation. The equations are
the same as before, but they are now attached to fixed paper objects rather than
quantified over arbitrary placeholders.

### `eq2_sigmaZeroMinus_lower`

- Lean name:
  [eq2_sigmaZeroMinus_lower](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(2)`
- abstraction:
  - `sigmaZeroMinus` represents `Σ⁻₀`
  - the side conditions are the printed `0 ≤ r < c < ρ < 1`

### `eq3_circleGap_decomposition`

- Lean name:
  [eq3_circleGap_decomposition](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(3)`
- abstraction:
  - `circleGap a b` is the normalized boundary excess
  - `sigmaPlus` and `sigmaZeroMinus` represent `Σ⁺` and `Σ⁻₀`

### `eq4_sigmaPlus_bound`

- Lean name:
  [eq4_sigmaPlus_bound](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(4)`
- abstraction:
  - `sigmaPlus`, `sigmaMinus`, and `sigmaZeroMinus` represent `Σ⁺`, `Σ⁻`,
    and `Σ⁻₀`
  - the side conditions are the printed `0 ≤ r < c < 1`

### `eq5_branch1_sigmaReduction`

- Lean name:
  [eq5_branch1_sigmaReduction](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(5)`
- abstraction:
  - `innerExcess` is concretely `diskExcess (circleGap a b) c`
  - `sigmaMinus ρ` represents `Σ⁻(ρ)`

### `eq6_branch2_sigmaReduction`

- Lean name:
  [eq6_branch2_sigmaReduction](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(6)`
- abstraction:
  - `innerExcess` is concretely `diskExcess (circleGap a b) c`
  - `sigmaMinus ρ` represents `Σ⁻(ρ)`

### `eq8_sigma_to_liftGap`

- Lean name:
  [eq8_sigma_to_liftGap](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(8)`
- abstraction:
  - `sigmaMinus ρ` represents `Σ⁻(ρ)`
  - `liftGapSeries a b liftScale ρ` represents the normalized circle integral
    `(1 / (2π)) ∫ |g(ρe^{iθ}) - a f(ρe^{iθ})|^2 / (1 - a^2) dθ`

### `eq9_liftGap_to_circleGap`

- Lean name:
  [eq9_liftGap_to_circleGap](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(9)`
- abstraction:
  - `liftGapSeries a b liftScale ρ` represents the normalized integral from equation `(8)`
  - `circleGap a b ρ` represents the normalized boundary excess
    `(1 / (2π)) ∫ (|g(ρe^{iθ})|^2 - |f(ρe^{iθ})|^2) dθ`
  - `paperLambda K c ρ` is Lean's explicit name for Wang's `1 + γ₂(ρ)`

### `eq7_paperK_formula`

- Lean name:
  [eq7_paperK_formula](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(7)`
- abstraction:
  - `K` is tied to Wang's displayed product formula through
    `WangKernelExact.PaperKFormula`
  - this is now carried inside `Section2Assumptions` rather than passed as a
    separate downstream theorem parameter

### `eq10_branch1_pointwise`

- Lean name:
  [eq10_branch1_pointwise](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(10)`

### `eq11_branch2_pointwise`

- Lean name:
  [eq11_branch2_pointwise](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(11)`

### `eq12_branch1_integrated`

- Lean name:
  [eq12_branch1_integrated](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(12)`
- abstraction:
  - `annulusLeftExcess` represents the paper annulus integral over
    `c ≤ |z| < sqrt(4/3) c`

### `eq13_branch2_integrated`

- Lean name:
  [eq13_branch2_integrated](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(13)`
- abstraction:
  - `annulusRightExcess` represents the paper annulus integral over
    `sqrt(4/3) c ≤ |z| < 1`

### `eq14_combined`

- Lean name:
  [eq14_combined](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- paper source: equation `(14)`
- abstraction:
  - `annulusExcess` represents the paper integral over `A(c,1)`

## Equation `(15)`

Equation `(15)` is represented in Lean by the definition
[Eq15ScalarBound](grothendieck/KorenblumProofSearch3/PaperAxioms.lean).
It is intentionally **not** an axiom:

- `(15)` is already an explicit scalar inequality written in the paper,
- the search goal is to prove it, not assume it,
- and exposing the unnumbered proof sentence after `(15)` as an axiom would add
  a stronger endpoint bridge than the paper's displayed formulas justify for the
  current generic candidate interface.

## Derived Lean Convenience Theorems

The following are ordinary Lean theorems, not approved axioms:

- [eq8eq9_sigma_to_circleBridge_of_eq8_eq9](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- [eq10_of_eq5_eq8_eq9](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
- [eq11_of_eq6_eq8_eq9](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)

These are allowed because they are proved in Lean from the literal paper axioms.

## Non-Axiomatized Items

### Lemma 2

The paper says “Now we apply Lemma 2” before equation `(3)`, but that lemma is
an external ingredient rather than a theorem proved inside Wang 2025 itself.
So this workspace does **not** approve Lemma 2 as a paper axiom. Instead, the
effect of that step only appears through the explicit printed equation `(3)`.

### The `K` to `Lambda` algebra

This remains explicit Lean mathematics in
[WangCertificateCore.lean](grothendieck/KorenblumProofSearch3/WangCertificateCore.lean).
It is not treated as a paper axiom.

### The `K` product formula implementation

The current exact implementation of the paper's displayed equation `(7)` still
uses the existing
[PaperKFormula](grothendieck/KorenblumProofSearch3/WangKernelExact.lean:156)
predicate from `WangKernelExact.lean`. The `Section2Assumptions` surface now
carries that displayed paper formula as `eq7_paperK_formula`, but the longer
term closure goal is still to keep the approved paper surface restricted to
literal paper definitions/results and standard Lean proofs.

## Current Lean Promotion Target

The first post-seed analytic promotion lives in
[OneModeKernel.lean](grothendieck/KorenblumProofSearch3/OneModeKernel.lean).
It is not an axiom file. It is ordinary Lean proving finite-support lemmas for
the new one-mode coefficient kernel discovered in
[scratch/2026-04-12_one_mode_kernel.md](grothendieck/KorenblumProofSearch3/scratch/2026-04-12_one_mode_kernel.md).
