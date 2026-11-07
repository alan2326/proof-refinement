# V38 Remaining Non-Paper Hypotheses

This note records the non-paper theorem parameters that still remain in the
public `V38` theorem
[direct_disk_vs_annulus](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:855).

## Scope

This list is only about the extra theorem parameters that appear *outside* the
paper context object

- `paper : PaperAxioms.Section2Assumptions a b K c`

in the public `V38` theorem type.

So, when we say “remaining non-paper hypotheses” here, we mean:

- extra theorem arguments that are not themselves fields of
  `Section2Assumptions`
- not the entire trusted surface of `Section2Assumptions`

That distinction used to matter because `Section2Assumptions` carried extra
non-paper side-condition fields. Those have now been removed, so this note is
also the complete list of the remaining non-paper trusted items in `V38`.

## Current Public Non-Paper Hypotheses

The current public theorem still takes exactly these four extra parameters:

1. [hPlusSigma](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:859)
   ```lean
   Summable (fun n : ℕ => OneModePaperBridge.plusSeq a b n * (cValueQ : ℝ) ^ (2 * n))
   ```
2. [hMinusSigmaC](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:861)
   ```lean
   Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * (cValueQ : ℝ) ^ (2 * n))
   ```
3. [hMinusSigma](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:863)
   ```lean
   ∀ ⦃ρ : ℝ⦄, (cValueQ : ℝ) < ρ → ρ < 1 →
     Summable (fun n : ℕ => OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))
   ```
4. [hAnnInt](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:866)
   ```lean
   IntervalIntegrable (AnnulusIntegralReduction.annulusDensity paper.circleGap)
     volume (cValueQ : ℝ) (1 : ℝ)
   ```

## Hypothesis-By-Hypothesis Status

### 1. `hPlusSigma`

- what it says:
  the `Σ⁺(c)` coefficient series converges at `c`
- where it is used:
  the inner-disk identity
  [annulusSlice_circleGap_eq_innerSeriesExcess](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean:114)
  uses it through
  [annulusSlice_sigmaPlus_eq_diskWeightedSeq](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean:49)
- is it explicitly stated in the paper:
  no
- how it is present in the paper:
  Wang defines `Σ⁺(s)` as a genuine series for `0 ≤ s < 1` after introducing
  the power-series expansions of `f` and `g`
  [Wang2025.txt:111](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:111)
  and
  [Wang2025.txt:134](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:134).
  So convergence is implicit in the paper’s analytic background, not a separate
  printed assumption.
- what needs to be formalized to remove it:
  enough analytic background to prove the coefficient-square series converges
  for every `ρ < 1`, then deduce the same for `plusSeq`

### 2. `hMinusSigmaC`

- what it says:
  the `Σ⁻(c)` coefficient series converges at `c`
- where it is used:
  the same inner-disk identity
  [annulusSlice_circleGap_eq_innerSeriesExcess](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean:114)
  uses it through
  [annulusSlice_sigmaMinus_eq_diskWeightedSeq](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean:67)
- is it explicitly stated in the paper:
  no
- how it is present in the paper:
  same status as `hPlusSigma`; `Σ⁻(s)` is introduced as a bona fide series on
  `0 ≤ s < 1`
  [Wang2025.txt:144](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:144),
  so convergence is implicit in the analytic setup
- what needs to be formalized to remove it:
  the analytic/coefficient identity for `g` and `f`, plus a domination lemma
  showing `minusSeq` is summable whenever the coefficient-square tails are
  summable

### 3. `hMinusSigma`

- what it says:
  the `Σ⁻(ρ)` coefficient series converges for every `c < ρ < 1`
- where it is used:
  the one-mode pointwise bridge
  [pointwise_of_series_eq8_eq9](grothendieck/KorenblumProofSearch3/OneModePaperBridge.lean:176),
  which feeds the mode-window inequalities in `V38`
- is it explicitly stated in the paper:
  no
- how it is present in the paper:
  again, only implicitly: Wang writes `Σ⁻(ρ)` throughout Section 2 as an
  ordinary function on `0 ≤ ρ < 1`, after defining it by a power series
  [Wang2025.txt:144](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:144)
- what needs to be formalized to remove it:
  a reusable theorem that the `minusSeq` series converges for all radii
  `ρ < 1`, derived from the actual analytic functions and their coefficients

### 4. `hAnnInt`

- what it says:
  the outer annulus density `2ρ * paper.circleGap ρ` is interval-integrable on
  `[c, 1]`
- where it is used:
  it is the integrability input needed for the annulus window inequalities, for
  example in
  [fallbackA_mass_mul_le_slice_of_pointwise](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:443)
  via
  [mass_mul_le_annulusSlice_of_integral_bound_ae](grothendieck/KorenblumProofSearch3/AnnulusIntegralReduction.lean:107)
- is it explicitly stated in the paper:
  no
- how it is present in the paper:
  implicitly through the reduction
  “we may assume that `‖g‖_{A²}` is finite, and so `‖f‖_{A²}` is also finite”
  at
  [Wang2025.txt:105](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:105).
  Once Wang starts integrating `|g|² - |f|²` over disk and annulus regions,
  finiteness/integrability is being used silently as background analysis.
- what needs to be formalized to remove it:
  the Bergman-space layer itself:
  `f, g ∈ A²(D)`, the radial/polar formula for their `A²` norms, and the
  identification of `paper.circleGap` with the actual circle integral so that
  annulus integrability follows from `A²` finiteness

## What “Lean-Side API” Means

This does **not** mean a user-facing program API. It means a small collection of
Lean definitions and theorems that downstream files can use without redoing the
analysis each time.

Concretely, the missing API is something like:

- a definition of the analytic objects `f`, `g`, and their coefficient data
- a theorem identifying circle means with coefficient-square series
- a theorem proving `Σ⁺` and `Σ⁻` are summable for `ρ < 1`
- a theorem proving the annulus density is integrable on `[c,1]` under the
  Bergman-space hypotheses used by the paper

That is the “API” the current coefficient-only V38 proof is missing.

## What “Public V38 Theorem Surface” Means

This means the exact theorem type of the final audited result

- [direct_disk_vs_annulus](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:855)

that the evaluator checks.

So “public theorem surface” means:

- the parameters that appear in that final theorem statement
- not the internal helper lemmas
- not the implementation details hidden inside the proof body

Right now, outside the `paper : Section2Assumptions ...` argument, the public
surface consists exactly of the four hypotheses listed above.

## Are These The Only Remaining Non-Paper Assumptions?

Yes.

- these four are the only remaining non-paper assumptions on the *public V38
  theorem surface*
- and, after removing `liftScale` and its side conditions from
  `Section2Assumptions`, they are also the only remaining non-paper trusted
  items anywhere in the current `V38` path

## Constant Status

The constant improvement is unchanged.

- the certified radius is still
  `cValueQ = 356401 / 1000000 = 0.356401`
  [README.md:16](grothendieck/KorenblumProofSearch3/Candidates/V38/README.md:16)
- the certified mass lower bound is still
  `hybridTotalMassQ ≥ 1`
  [Data.lean:1185](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1185)
  [Data.lean:1194](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1194)
- the audit note still records the same strict scan bracket:
  `0.356401` passes, `0.356402` fails
  [README.md:18](grothendieck/KorenblumProofSearch3/Candidates/V38/README.md:18)

The recent work shrank the trusted surface, but it did not change the candidate
data or the certified radius.
