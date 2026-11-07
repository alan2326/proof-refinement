# Korenblum Proof Search Results

## Current Status

The current trustworthy headline result in this workspace is:

- `V36`
- `c = 3563 / 10000 = 0.3563`
- `405` boxes
- exact Lean-side total `= 1.000542248901...`
- evaluator status: compile `PASS`, axiom audit `PASS`, type check `PASS`,
  numeric verify `PASS`
- audit status: `PASS` under
  [numerical_audit.py](grothendieck/KorenblumProofSearch3/oracle/numerical_audit.py)

This improves Wang's published `0.3554` bound.

## Preferred Certificate

`V36` is the preferred certificate, not the older `v24`, `v25`, `v26`,
`v27`, or `v28` files.

Why `V36` is better:

- it keeps the same strict `0.3563` radius as `v28`,
- but the transformed-`t` Wang box kernel now closes directly inside Lean for
  the generated candidate modules,
- the old large-list dispatcher was replaced by a Lean `Fin`-indexed wrapper,
  so the certificate is now a real compiled Lean artifact instead of a partly
  stalled design,
- Lean proves the equation `(9)` step
  `K^2 <= kSqUpper -> Lambda <= lambdaUpper`,
- Lean proves the reciprocal step, the routine equation `(15)` analytic side
  conditions from `PaperKFormula`, exact box masses, exact total, and the Wang
  truncation/monotonicity kernel,
- and the external Arb code is now only a search and audit aid for the
  current `V36` certificate, not part of the candidate's proof term.

Concretely, each box in `V36` stores:

- its rational endpoints,
- a rational `kSqUpper`,
- a rational `lambdaUpper`,
- and a rational `alpha = 1 / lambdaUpper`.

Lean then proves, box by box, that if `K(c, rho)^2 <= kSqUpper` on that
interval and the exact rational equation `(9)` witness holds, then
`Lambda(rho) <= lambdaUpper`, hence `alpha <= 1 / Lambda(rho)`. The finite sum
and the branch integrals are then handled exactly inside Lean.

## Trust Model

What is now Lean-grounded:

- the equation `(15)` scalar-integrand and scalar-criterion definitions,
- the equation `(9)` algebra from `K^2` to `Lambda`,
- the exact branch integrals for each box,
- the exact rational total mass,
- the passage from per-box `Lambda` upper bounds to lower bounds for the scalar
  criterion integrand,
- the positivity of `paperLambda` and interval-integrability of Wang's two
  scalar integrands on the required subintervals,
- and the final reduction from `totalBoxMass >= 1` to
  `1 <= scalarCriterion`.

What remains outside Lean:

- Wang's paper bridge
  `1 <= scalarCriterion -> innerExcess <= annulusExcess`,
- and the separate Arb-backed evaluator cross-check that the searched
  `kSqUpper` values are compatible with the older external Wang kernel.

So the current result is still a rigorous computer-assisted proof rather than a
fully formal end-to-end Lean proof, but the trusted numerical surface is now
smaller than before.

## Older Claims

The earlier `0.356504` claim from `candidate_v24` should not be treated as the
current trusted result.

That older certificate used a less Lean-grounded affine-lower-bound oracle.
After tightening the trust model, the robust surviving result is the current
`0.3563` certificate.

`candidate_v25` is an intermediate strict all-constant certificate at the same
radius, `candidate_v26` was the first direct-`Lambda` version,
`candidate_v27` was the first Arb-backed constant-box repair,
`candidate_v28` moved the Wang paper objects into the new Lean shell, and
`V36` is the first module-style candidate where the transformed-`t` box kernel
compiles cleanly all the way through Lean.

## Numerical Benchmarks

Useful heuristic scalar-criterion values:

- `I(0.3554) = 1.021241198...`
- `I(0.3558) = 1.012223218...`
- `I(0.3560) = 1.007535090...`
- `I(0.3561) = 1.005198873...`
- `I(0.3562) = 1.002867873...`
- `I(0.3563) = 1.000542078...`
- `I(0.3564) = 0.997823398...`

Those values match the current strict certificate picture: `0.3563` still has
real margin, while `0.3564` is already below threshold in the stronger model.

## Main Bottleneck

The limiting factor remains the outer control `Lambda = 1 + gamma2`.

The current strict certificate is already constant-box only, so the next real
improvement would likely need one of:

1. a genuinely sharper outer-control bound,
2. a better certified bound on `K(c, rho)` itself,
3. or a stronger formally checked reduction that extracts more from the same
   `Lambda` data.

Simple refactoring is no longer the issue. The certificate format is now
reasonably clean; the remaining problem is mathematical slack.
