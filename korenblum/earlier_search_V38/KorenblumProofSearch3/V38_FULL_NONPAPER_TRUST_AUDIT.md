# V38 Full Non-Paper Trust Audit

This note is the full answer to:

- what assumptions/items in the current audited `V38` path are **not** literal
  displayed paper statements
- which of them are still on the **public theorem surface**
- which of them are hidden inside the trusted paper context
- which are only surrogate definitions rather than assumptions
- and whether each one looks reducible or is only implicitly used by the paper

## Scope

This audit is about the current trusted `V38` path, excluding:

- standard Lean / mathlib background
- certified rational box data
- ordinary proved lemmas in the project

It includes three different kinds of things:

1. extra theorem hypotheses on the final audited theorem
2. trusted fields/objects inside `PaperAxioms.Section2Assumptions`
3. surrogate definitions/modeling choices that are not themselves assumptions,
   but are still not exact paper objects

Those three categories should not be conflated.

## A. Extra Non-Paper Hypotheses On The Final Theorem

The final audited theorem is
[direct_disk_vs_annulus](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:855).

Outside the `paper : Section2Assumptions ...` argument, it currently has exactly
four extra non-paper theorem parameters:

| Item | Location | Exact paper statement? | Paper status | Reducible? | Notes |
| --- | --- | --- | --- | --- | --- |
| `hPlusSigma` | [Direct.lean:859](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:859) | No | Implicit in Wang’s use of `Σ⁺(s)` as a genuine convergent series on `0 ≤ s < 1` after introducing the power-series expansions [Wang2025.txt:111](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:111), [Wang2025.txt:134](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:134) | Yes, likely | Should come from analytic/coefficient background |
| `hMinusSigmaC` | [Direct.lean:861](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:861) | No | Implicit in Wang’s use of `Σ⁻(s)` as a genuine convergent series [Wang2025.txt:144](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:144) | Yes, likely | Same status as `hPlusSigma` |
| `hMinusSigma` | [Direct.lean:863](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:863) | No | Implicit background needed to evaluate `Σ⁻(ρ)` for every `c < ρ < 1` | Yes, likely | Needed by the one-mode pointwise bridge |
| `hAnnInt` | [Direct.lean:866](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:866) | No | Implicit in the proof reduction “we may assume `‖g‖_{A²}` is finite, and so `‖f‖_{A²}` is also finite” [Wang2025.txt:105](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:105) | Yes, but harder | Needs the Bergman-space layer, not just coefficient algebra |

### Assessment For Category A

These four are the only remaining non-paper assumptions on the **public V38
theorem surface**.

They all look reducible.

More precisely:

- `hPlusSigma`, `hMinusSigmaC`, and `hMinusSigma` should come from formalizing
  the actual analytic functions and their coefficient-square/circle-mean
  identities
- `hAnnInt` should come from formalizing the Bergman `A²` finiteness reduction
  and the radial/polar annulus integral

So these do **not** look like permanent paper assumptions. They look like
missing background formalization.

## B. Hidden Trusted Items Inside `Section2Assumptions`

The trusted paper context is
[Section2Assumptions](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:317).

Most of its fields are exact displayed Wang equations `(2)` through `(14)`,
and it no longer carries extra non-paper side-condition fields.

There are no remaining hidden non-paper trusted items in that context.

The earlier `liftScale`, `liftScale_nonneg`, and `liftScale_lt_one` fields have
been removed. `Section2Assumptions` now bundles the paper lifted-gap quantity
from equation `(8)` directly, so the trusted context only carries:

- exact displayed paper equations `(2)` through `(14)`
- the paper lifted-gap object used in equations `(8)` and `(9)`

### Assessment For Category B

So there is no longer any hidden non-paper trust caveat for this file. The only
remaining non-paper trusted items are on the public theorem surface in
Category A.

## C. Non-Paper Surrogate Definitions / Modeling Choices

These are **not assumptions**, but they are still places where the current Lean
artifact does not yet use the paper’s literal analytic objects.

| Item | Location | Exact paper object? | Paper status | Reducible? | Notes |
| --- | --- | --- | --- | --- | --- |
| coefficient parameters `a b : ℕ → ℂ` | theorem/model-wide | No | Surrogate for coefficients of actual analytic functions `f,g` | Yes | Current theorem is coefficient-centric |
| `circleGap := circleGapSeries` | [PaperAxioms.lean:94](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:94) | No | Coefficient-side surrogate for the normalized boundary integral from `(3)` | Yes | Paper starts from the integral, then identifies it with the series via Lemma 2 [Wang2025.txt:200](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:200) |
| `liftGapSeries` as a definition | [PaperAxioms.lean:105](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:105) | No | Coefficient-side surrogate for the normalized circle integral in `(8)` | Yes | Paper writes the integral in `(8)` [Wang2025.txt:410](grothendieck/KorenblumProofSearch3/paper/Wang2025.txt:410) |

### Assessment For Category C

These are not hidden assumptions, but they matter if the target standard is:

- “the trusted Lean artifact should speak in the same analytic objects as the
  paper”

They all look reducible by further formalization.

## D. What Is **Not** Non-Paper Here

The following trusted fields are exact displayed paper statements and should not
be counted as non-paper assumptions merely because they are trusted:

- `eq7_paperK_formula`
- `eq2_sigmaZeroMinus_lower`
- `eq3_circleGap_decomposition`
- `eq4_sigmaPlus_bound`
- `eq5_branch1_sigmaReduction`
- `eq6_branch2_sigmaReduction`
- `eq8_sigma_to_liftGap`
- `eq9_liftGap_to_circleGap`
- `eq10_branch1_pointwise`
- `eq11_branch2_pointwise`
- `eq12_branch1_integrated`
- `eq13_branch2_integrated`
- `eq14_combined`

Those are all fields of
[Section2Assumptions](grothendieck/KorenblumProofSearch3/PaperAxioms.lean:317)
and correspond to the displayed Section 2 equations in Wang.

## E. Bottom Line

### Current non-paper items that are still truly trusted

There are **4** current trusted non-paper items in the V38 path:

1. `hPlusSigma`
2. `hMinusSigmaC`
3. `hMinusSigma`
4. `hAnnInt`
### Of those 4

- **all 4 look reducible**
- **none of the 4 should remain permanent trusted assumptions**
- **all 4 are implicit analytic background used by the paper**

### Important nuance

If you ask only:

- “what extra non-paper hypotheses are still visible in the final theorem type?”

then the answer is just the first 4.

If you ask more broadly:

- “what non-paper trusted items still exist anywhere in the current V38 proof
  path?”

then the answer is the same list of 4 above.

## F. Constant Status

The constant improvement is unchanged.

- the certified radius is still
  `cValueQ = 356401 / 1000000 = 0.356401`
  [README.md:16](grothendieck/KorenblumProofSearch3/Candidates/V38/README.md:16)
- the strict scan bracket still records
  `0.356401` as passing and `0.356402` as failing
  [README.md:18](grothendieck/KorenblumProofSearch3/Candidates/V38/README.md:18)
- the certified mass lower bound is still
  `hybridTotalMassQ ≥ 1`
  [Data.lean:1194](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1194)

So the recent cleanup changed the trusted surface, not the constant.
