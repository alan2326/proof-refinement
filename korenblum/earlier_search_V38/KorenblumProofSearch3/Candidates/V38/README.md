# V38 Audit Guide

This note is about the latest promoted candidate
[Direct.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean).

## Status

- current trust status:
  `V38` has been replayed against the repaired `Section2Assumptions` paper
  interface and now passes the strict evaluator again
- current remaining non-paper theorem inputs:
  `hPlusSigma`, `hMinusSigmaC`, `hMinusSigma`, and `hAnnInt`
- recently eliminated from the public theorem type by proof:
  `hPaperK`, `hAnnNonneg`, `hPlusDisk`, `hMinusDisk`, and `hMinusWeight`
- recently eliminated from the trusted paper context:
  `liftScale`, `liftScale_nonneg`, and `liftScale_lt_one`
- candidate namespace: `KorenblumProofSearch3.V38`
- certified radius used in the Lean artifact:
  `c = cValueQ = 356401 / 1000000 = 0.356401`
- strict scan bracket from the search notes:
  - `c = 0.356401` gives total mass `1.000012381570`
  - `c = 0.356402` gives total mass `0.999989183931`
  - so the current strict frontier is around `0.3564015`
- this is a real improvement over the old strict `V36` radius `0.3563`

The final theorem proved by `V38` is the direct disk-vs-annulus statement

$$
\operatorname{annulusSlice}(\mathrm{circleGap}, 0, c)
\le
\operatorname{annulusSlice}(\mathrm{circleGap}, c, 1).
$$

rather than the older scalar-criterion endpoint used by `V36`.

## File Structure

The relevant file structure for `V38` is:

```text
KorenblumProofSearch3/
  Candidates/
    V38/
      Data.lean
      Main.lean
      Direct.lean
      README.md
  PaperAxioms.lean
  OneModeKernel.lean
  OneModeSup.lean
  OneModePaperBridge.lean
  OneModeTauWindow.lean
  OneModeDiskBridge.lean
  OneModeInnerBridge.lean
  AnnulusIntegralReduction.lean
  WindowBoxReduction.lean
  WangCertificateCore.lean
  WangKernelExact.lean
  WangPaperSideConditions.lean
  evaluate_wang.py
  paper/
    Wang2025.pdf
    Wang2025.txt
    AXIOM_EXTRACTION.md
  results/
    mode_hybrid_boxes_c_0_356401.csv
  experiments/
    export_mode_hybrid_boxes.py
    generate_v38_candidate.py
```

The roles of those files are:

- [Candidates/V38/Data.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean):
  concrete rational data for the candidate. This file fixes `cValueQ`, stores
  all certified boxes, defines the hybrid partition, and proves the rational
  total-mass lower bound `hybridTotalMassQ_ge_one`.
- [Candidates/V38/Main.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Main.lean):
  converts each window's certified mass into an annulus-slice inequality, then
  packages the seven window contributions into the global outer bound.
- [Candidates/V38/Direct.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean):
  final theorem `direct_disk_vs_annulus`.
- [PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean):
  the paper-facing interface. The numbered paper equations are now explicit
  fields of `Section2Assumptions`, and the disk/annulus excess terms are
  defined from `circleGap` rather than left abstract.
- [paper/AXIOM_EXTRACTION.md](grothendieck/KorenblumProofSearch3/paper/AXIOM_EXTRACTION.md):
  exact documentation of which paper equations were axiomatized and which were
  deliberately not trusted.
- [OneModeKernel.lean](grothendieck/KorenblumProofSearch3/OneModeKernel.lean):
  the core new coefficient inequality introduced in this run.
- [OneModeSup.lean](grothendieck/KorenblumProofSearch3/OneModeSup.lean):
  the supremum form of the one-mode kernel.
- [OneModeTauWindow.lean](grothendieck/KorenblumProofSearch3/OneModeTauWindow.lean):
  proves that on suitable `tau = c^2 / rho^2` windows, the supremum is attained
  by a fixed mode `j`.
- [OneModePaperBridge.lean](grothendieck/KorenblumProofSearch3/OneModePaperBridge.lean):
  connects the one-mode coefficient objects to the paper-style `Sigma` objects
  and the radial annulus bookkeeping.
- [OneModeDiskBridge.lean](grothendieck/KorenblumProofSearch3/OneModeDiskBridge.lean)
  and [OneModeInnerBridge.lean](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean):
  identify the inner disk contribution with the coefficient-side one-mode series.
- [AnnulusIntegralReduction.lean](grothendieck/KorenblumProofSearch3/AnnulusIntegralReduction.lean):
  the direct target-facing layer that proves “mass lower bound on a window
  implies annulus-slice lower bound on that window”.
- [WindowBoxReduction.lean](grothendieck/KorenblumProofSearch3/WindowBoxReduction.lean):
  converts certified Wang boxes into lower bounds for the direct annulus
  windows.
- [WangCertificateCore.lean](grothendieck/KorenblumProofSearch3/WangCertificateCore.lean),
  [WangKernelExact.lean](grothendieck/KorenblumProofSearch3/WangKernelExact.lean),
  and [WangPaperSideConditions.lean](grothendieck/KorenblumProofSearch3/WangPaperSideConditions.lean):
  existing Lean infrastructure for Wang's `K`, `Lambda`, exact box kernels, and
  routine analytic side conditions.
- [evaluate_wang.py](grothendieck/KorenblumProofSearch3/evaluate_wang.py):
  strict audit script. It compiles the candidate from source, checks the theorem
  type, and rejects any project-specific global axioms.
- [results/mode_hybrid_boxes_c_0_356401.csv](grothendieck/KorenblumProofSearch3/results/mode_hybrid_boxes_c_0_356401.csv):
  the exported certified box data used to generate `V38`.
- [experiments/export_mode_hybrid_boxes.py](grothendieck/KorenblumProofSearch3/experiments/export_mode_hybrid_boxes.py)
  and [experiments/generate_v38_candidate.py](grothendieck/KorenblumProofSearch3/experiments/generate_v38_candidate.py):
  untrusted generation tooling. These are useful for audit and reproduction, but
  they are not part of the trusted Lean proof path.

## Candidate Anatomy

`V38` has:

- `32` boxes on the interval $c < \rho < \sqrt{4/3}\,c$, the interval appearing in
  Wang's equation `(5)`
- `516` boxes on the interval $\sqrt{4/3}\,c < \rho < 1$, the interval appearing in
  Wang's equation `(6)`

Those boxes are regrouped into the following seven windows:

```text
fallbackA : branch1_box_0000 .. branch1_box_0003
mode4     : branch1_box_0004 .. branch1_box_0005
fallbackB : branch1_box_0006
mode3     : branch1_box_0007 .. branch1_box_0011
fallbackC : branch1_box_0012
mode2     : branch1_box_0013 .. branch1_box_0031
mode1     : branch2_box_0000 .. branch2_box_0515
```

This split is defined in
[Data.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1113)
through
[Data.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1194).

The important point is that `V38` is not just one big box sum. It is a hybrid:

- three small fallback windows still use the original Wang-style box treatment
  on subintervals of $c < \rho < \sqrt{4/3}\,c$
- the remaining four windows use the new one-mode analytic theorem with fixed
  active mode `j = 4, 3, 2, 1`

The final rational mass lower bound is
[hybridTotalMassQ_ge_one](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean:1194).

## What V38 Does Differently From the Paper

Wang's original Section 2 route is:

1. reduce the disk term to coefficient-side $\Sigma$ quantities
2. use the two piecewise coefficient kernels in equations `(5)` and `(6)`
3. use equations `(8)` and `(9)` to pass from $\Sigma^-$ to the circle gap
4. integrate to get equations `(12)` and `(13)`
5. combine into `(14)`, then prove the scalar inequality `(15)`

`V38` changes two major parts of that story.

### 1. Direct comparison with equations `(5)` and `(6)`

In Wang's notation, equation `(5)` is the estimate on the interval
$c < \rho < \sqrt{4/3}\,c$:

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
\frac{c^6}{6\rho^2(\rho^2-c^2)} \, \Sigma^-(\rho).
$$

Equation `(6)` is the estimate on the interval
$\sqrt{4/3}\,c < \rho < 1$:

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
\frac{c^4}{2\rho^2} \, \Sigma^-(\rho).
$$

The new analytic input in `V38` is a replacement for those coefficient kernels.
It introduces

$$
H(c,\rho)
=
\sup_{j \ge 1}
\left[
\frac{j}{j+1} \frac{c^{2j+2}}{\rho^{2j}}
\right].
$$

The point is that `V38` proves a bound of the same general shape as `(5)` and
`(6)`,

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
H(c,\rho)\,\Sigma^-(\rho),
$$

but with a sharper coefficient factor.

Two structural facts connect this directly back to Wang's formulas:

- when $j = 1$, the term in $H(c,\rho)$ is exactly

  $$
  \frac{1}{2}\frac{c^4}{\rho^2}
  =
  \frac{c^4}{2\rho^2},
  $$

  which is Wang's equation `(6)`
- the transition where the maximizing mode changes from $j = 2$ to $j = 1$
  occurs exactly at $\rho = \sqrt{4/3}\,c$, so Wang's split point is the first
  breakpoint of the stronger kernel

So equation `(6)` is literally the `j = 1` piece of `H(c, ρ)`, while equation
`(5)` is replaced by sharper fixed-mode pieces of `H(c, \rho)` on subintervals of
$c < \rho < \sqrt{4/3}\,c$.

In `V38`, this supremum is not used abstractly everywhere. Instead, the proof
cuts the $\rho$-range into windows where a single mode is known to dominate, and
then proves the corresponding fixed-mode lower bound there.

That is why the windows are labeled `mode4`, `mode3`, `mode2`, and `mode1`.
The fixed-mode pieces used in `V38` are:

$$
H_4(c,\rho) = \frac{4}{5}\frac{c^{10}}{\rho^8},
\qquad
H_3(c,\rho) = \frac{3}{4}\frac{c^8}{\rho^6},
\qquad
H_2(c,\rho) = \frac{2}{3}\frac{c^6}{\rho^4},
\qquad
H_1(c,\rho) = \frac{1}{2}\frac{c^4}{\rho^2}.
$$

Here:

- `mode4` uses $H_4(c,\rho)$
- `mode3` uses $H_3(c,\rho)$
- `mode2` uses $H_2(c,\rho)$
- `mode1` uses $H_1(c,\rho)$, which is exactly Wang's equation `(6)`

What “sharper” means is: in an inequality of the form

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
\text{coefficient}(\rho)\,\Sigma^-(\rho),
$$

a smaller coefficient is better.

On the interval $c < \rho < \sqrt{4/3}\,c$, Wang uses the single envelope

$$
G_5(c,\rho) := \frac{c^6}{6\rho^2(\rho^2-c^2)}.
$$

`V38` replaces most of that interval by subintervals on which one of
$H_4(c,\rho)$, $H_3(c,\rho)$, or $H_2(c,\rho)$ is already the true maximizing
piece of $H(c,\rho)$ and is strictly smaller than $G_5(c,\rho)$.

If one writes

$$
\tau = \frac{c^2}{\rho^2},
$$

then the ratio of the fixed-mode piece

$$
H_j(c,\rho) = \frac{j}{j+1}\frac{c^{2j+2}}{\rho^{2j}}
$$

to Wang's equation `(5)` coefficient is

$$
\frac{H_j(c,\rho)}{G_5(c,\rho)}
=
6\frac{j}{j+1}\tau^{j-2}(1-\tau).
$$

For the pieces actually used in `V38`, this becomes

$$
\frac{H_2(c,\rho)}{G_5(c,\rho)} = 4(1-\tau),
$$

$$
\frac{H_3(c,\rho)}{G_5(c,\rho)} = \frac{9}{2}\tau(1-\tau),
$$

$$
\frac{H_4(c,\rho)}{G_5(c,\rho)} = \frac{24}{5}\tau^2(1-\tau).
$$

On the corresponding `mode2`, `mode3`, and `mode4` windows, these ratios are
$< 1$, so the coefficient used by `V38` is strictly smaller than Wang's
equation `(5)` coefficient. Near $\rho = c$, this improvement is especially
large, because $1-\tau$ is very small while Wang's factor
$1/(\rho^2-c^2)$ becomes singular.

In earlier notes I used “branch 1” and “branch 2” as shorthand. In the paper's
notation, those just mean:

- the interval $c < \rho < \sqrt{4/3}\,c$ from equation `(5)`
- the interval $\sqrt{4/3}\,c < \rho < 1$ from equation `(6)`

### 1a. Why the mode argument is correct

The conceptual reason is that, after the coefficient-side reduction, the inner
disk excess is controlled by a positive linear combination of the negative-mode
coefficients. Once one normalizes by $\Sigma^-(\rho)$, one gets a weighted
average of single-mode contributions, and a weighted average is always bounded
by its largest term.

Write

$$
\eta_j = |b_j|^2 - |a_j|^2
\qquad (j \in N_2).
$$

Then

$$
\Sigma^-(\rho) = \sum_{j \in N_2} \eta_j \rho^{2j}.
$$

Using the coefficient expansion of the inner disk term together with Wang's
equation `(4)` at $r=c$, one gets

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
\sum_{j \in N_2} \eta_j \frac{j}{j+1} c^{2j+2}.
$$

Now multiply and divide each term by $\rho^{2j}$:

$$
\sum_{j \in N_2} \eta_j \frac{j}{j+1} c^{2j+2}
=
\Sigma^-(\rho)
\sum_{j \in N_2}
\frac{\eta_j \rho^{2j}}{\Sigma^-(\rho)}
\cdot
\frac{j}{j+1}\frac{c^{2j+2}}{\rho^{2j}}.
$$

The coefficients

$$
p_j(\rho) := \frac{\eta_j \rho^{2j}}{\Sigma^-(\rho)}
$$

are nonnegative and satisfy

$$
\sum_{j \in N_2} p_j(\rho) = 1.
$$

So the last sum is a weighted average of the single-mode quantities

$$
\frac{j}{j+1}\frac{c^{2j+2}}{\rho^{2j}}.
$$

Therefore

$$
\sum_{j \in N_2}
p_j(\rho)\,
\frac{j}{j+1}\frac{c^{2j+2}}{\rho^{2j}}
\le
\sup_{j \ge 1}
\frac{j}{j+1}\frac{c^{2j+2}}{\rho^{2j}}
=
H(c,\rho),
$$

which gives

$$
\int_{D(c)} \bigl(|f(z)|^2 - |g(z)|^2\bigr)\, dA(z)
\le
H(c,\rho)\,\Sigma^-(\rho).
$$

This is the whole reason the mode kernel is valid: the worst possible ratio is
achieved by concentrating all the negative mass in the single most dangerous
mode.

The reason fixed-mode windows are possible is that, after factoring out $c^2$,
the kernel depends only on

$$
\tau = \frac{c^2}{\rho^2},
\qquad
H(c,\rho)
=
c^2 \sup_{j \ge 1} \frac{j}{j+1}\tau^j.
$$

Two consecutive modes $j$ and $j+1$ are equal exactly when

$$
\frac{j}{j+1}\tau^j

=

\frac{j+1}{j+2}\tau^{j+1},
$$

which is equivalent to

$$
\tau = \tau_j := \frac{j(j+2)}{(j+1)^2}
=
1 - \frac{1}{(j+1)^2}.
$$

So on any interval where

$$
\tau_{m-1} \le \frac{c^2}{\rho^2} \le \tau_m,
$$

the supremum is attained by a single fixed mode $m$, and hence

$$
H(c,\rho) = \frac{m}{m+1}\frac{c^{2m+2}}{\rho^{2m}}.
$$

That is exactly why `V38` can use the explicit windows `mode4`, `mode3`,
`mode2`, and `mode1`.

### 2. Direct disk-vs-annulus endpoint

`V38` does not close the proof by reproducing Wang's old scalar-criterion route
through equations `(10)` to `(15)`.

Instead, it proves the target directly in annulus language:

$$
\operatorname{annulusSlice}(\mathrm{circleGap}, 0, c)
\le
\operatorname{annulusSlice}(\mathrm{circleGap}, c, 1).
$$

This is mathematically cleaner for the one-mode argument. Once the inner disk
term is identified with the coefficient-side one-mode series, each certified
window contributes directly to the outer annulus slice. Then the seven window
contributions are summed, and the rational total mass `>= 1` finishes the proof.

So the main difference from the paper is not “better numerical integration”.
The main difference is:

- a new coefficient theorem replaces most of Wang's use of equations `(5)` and
  `(6)`
- the proof terminates in a direct annulus inequality rather than Wang's final
  scalar criterion

## Which Paper Axioms V38 Still Uses

The workspace allows the literal paper equations `(2)` through `(14)` as custom
axioms, but `V38` uses only a proper subset of them.

There are two different notions here:

- the axioms that appear explicitly as parameters of the final theorem
- the axioms that appear in the full transitive closure of the proof

The final theorem
[direct_disk_vs_annulus](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:627)
explicitly takes only:

- equation `(8)` as `h8`
- equation `(9)` as `h9`

However, the actual Lean axiom report for
`KorenblumProofSearch3.V38.direct_disk_vs_annulus` shows that the full proof
depends on the following paper axioms:

- equation `(3)`
- equation `(4)`
- equation `(5)`
- equation `(8)`
- equation `(9)`

The roles are:

- equation `(3)` is used in
  [OneModeInnerBridge.lean](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean:37)
  to identify the paper's circle-gap quantity with
  $\Sigma^+(r) - \Sigma^-(r)$
- equation `(4)` is used in
  [Candidates/V38/Direct.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:274)
  to deduce
  $\Sigma^+(c) \le \Sigma^-(c)$, which is the key coefficient comparison behind
  the one-mode argument
- equation `(5)` is still used in
  [Candidates/V38/Direct.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean:284)
  to handle the small fallback subintervals inside
  $c < \rho < \sqrt{4/3}\,c$
- equations `(8)` and `(9)` are used to convert the coefficient-side bound into
  a bound against the circle-gap density on the annulus

Equation `(6)` is not used as an axiom in `V38`; the `j=1` one-mode piece
reproduces its coefficient internally. Equations `(10)` through `(15)` are also
not used as axioms in `V38`.

Besides those, the theorem still takes standard analytic hypotheses such as
summability and annulus integrability.

The Wang kernel product formula is no longer a separate theorem parameter in the
final statement. It is carried by the paper context through
`paper.eq7_paperK_formula`.

Everything else in the candidate is ordinary Lean proof plus exact rational box
data.

## How To Audit V38

If you want to check the candidate from first principles, the shortest reading
order is:

1. [paper/Wang2025.pdf](grothendieck/KorenblumProofSearch3/paper/Wang2025.pdf)
2. [paper/AXIOM_EXTRACTION.md](grothendieck/KorenblumProofSearch3/paper/AXIOM_EXTRACTION.md)
3. [PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)
4. [OneModeKernel.lean](grothendieck/KorenblumProofSearch3/OneModeKernel.lean)
5. [OneModeTauWindow.lean](grothendieck/KorenblumProofSearch3/OneModeTauWindow.lean)
6. [OneModePaperBridge.lean](grothendieck/KorenblumProofSearch3/OneModePaperBridge.lean)
7. [OneModeDiskBridge.lean](grothendieck/KorenblumProofSearch3/OneModeDiskBridge.lean)
8. [OneModeInnerBridge.lean](grothendieck/KorenblumProofSearch3/OneModeInnerBridge.lean)
9. [AnnulusIntegralReduction.lean](grothendieck/KorenblumProofSearch3/AnnulusIntegralReduction.lean)
10. [WindowBoxReduction.lean](grothendieck/KorenblumProofSearch3/WindowBoxReduction.lean)
11. [Candidates/V38/Data.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Data.lean)
12. [Candidates/V38/Main.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Main.lean)
13. [Candidates/V38/Direct.lean](grothendieck/KorenblumProofSearch3/Candidates/V38/Direct.lean)
14. [evaluate_wang.py](grothendieck/KorenblumProofSearch3/evaluate_wang.py)

The evaluator's job is narrow:

- compile the candidate
- check the exact theorem type
- run `#print axioms` on the theorem
- reject any custom axiom not declared in
  [PaperAxioms.lean](grothendieck/KorenblumProofSearch3/PaperAxioms.lean)

So the trust boundary for `V38` is:

- approved literal Wang axioms
- Lean proofs
- exact rational data embedded in `Data.lean`

The Python scripts used during search and export are not part of the trusted
proof path once `V38` is generated.
