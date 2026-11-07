# sprint_002_lower_taylor5

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V1.lean` (score `2/3`)
**Target file:** `Candidates/V2.lean`
**Side:** `lower`
**Strict improvement required:** yes

## Goal

Open the `lambda` side for the first time. Prove the fifth-order Taylor upper
bound `sin x < x - x^3/6 + x^5/120` for `x > 0`, combine with a candidate-space
lower bound `π > 3` (from `polygonLower_lt_pi 1` + a rational nested-radical
estimate), and land `lambda = 1/4`. `kappa` stays at `2/3`. Score drops
`2/3 → 5/12` (a `1/4` improvement).

## Rationale

Two directives point at this sprint before any other:

1. **Standing directive 3 (keep both sides moving).** `lambda` has been `0` for
   sprints 000 and 001. `frontier.csv`'s `side` column will show two upper-only
   passes, and the third one being upper again would make the run
   one-sided-in-fact regardless of what the directive text says. The lower side
   is where the next architectural rung lives.
2. **Standing directive 2 (interrogate every constant).** The chain in V1 has
   three quantitative pieces: the cubic Taylor coefficient (V1 tightened it),
   the `π ≤ 4` factor (untouched — a live target for a later upper sprint), and
   the `lambda = 0` constant (never interrogated). This sprint hits (3), leaving
   (2) cleanly available as a separate future architectural sprint on the upper
   side.

The mechanism is genuinely a **new analytic ingredient**, not a variant of V1:

- V1 needed `sin x > x - x^3/6` (lower Taylor).
- This sprint needs `sin x < x - x^3/6 + x^5/120` (upper Taylor).

They are separate strict Taylor bounds around `sin`, on opposite sides. The
upper bound's proof is structurally a nested `strictMonoOn_of_deriv_pos` chain
that *uses* V1's lower bound at the innermost step: differentiating twice, the
sign of `g''(x) = sin x - (x - x^3/6)` is exactly what V1 proved. That reuse is
what keeps this sprint bounded to one session.

Concrete witness that `lambda = 1/4` succeeds:

At `x = π/2^(n+2)`, multiplying the upper Taylor by `2^(n+2)` gives

    polygonLower n < π - π^3/(96·4^n) + π^5/(30720·16^n).

Rearranged and multiplied by `4^n`,

    4^n · (π - polygonLower n) > π^3/96 - π^5/(30720·4^n).

That RHS is monotone increasing in `n`, so the tightest constraint is `n = 0`:
we need `π^3/96 - π^5/30720 ≥ 1/4`, i.e., `π^3(320 - π^2) ≥ 7680`. On the
interval `π ∈ (3, 4)` the function `π^3(320-π^2)` is strictly increasing (its
derivative is `5π^2(192-π^2) > 0` for `π < √192`), and both `π^3 > 27` and
`320 - π^2 > 304` are strict, so

    π^3 · (320 - π^2) > 27 · 304 = 8208 > 7680.

Headroom `528/30720 ≈ 0.017` at the tightest step. Numerically `π - 2√2 ≈
0.3132`, well above `1/4`.

The `π > 3` premise is not in the trusted surface (Mathlib's `pi_gt_three` is on
the text-blocked list), but it is one nested-radical bound away:
`polygonLower 1 = 4√(2 - √2)` and `4√(2 - √2) > 3` iff `√2 < 23/16` iff
`2 < 529/256`, which is `norm_num`.

Directive checks:

- **Architectural, not precision.** New Taylor bound, new estimator direction,
  first candidate with `lambda > 0`. Not the same chain as V1 with a numerical
  tweak.
- **Untouched factor.** `lambda = 0` has been unchallenged since sprint 000.
- **Bounded to one session.** Two derived lemmas (`sin_lt_taylor5`, an inline
  `polygonLower 1 > 3`), each modeled on the V1 template.

## Concrete edits expected

- `Candidates/V2.lean` — declares `def lambda : ℝ := 1 / 4` and
  `def kappa : ℝ := 2 / 3` on single lines. Proves the contract by
  (a) rerunning V1's upper-conjunct arithmetic verbatim for `kappa = 2/3`, and
  (b) proving the lower conjunct via the 5th-order Taylor upper bound plus a
  `π > 3` step and V1-style rescaling arithmetic.
- `Candidates/V2/Taylor.lean` — **recommended**, not mandatory. If the
  helpers push V2.lean above ~180 lines, lift `sin_gt_sub_cube_div_six`
  (restated from V1) and `sin_lt_taylor5` into this file. Theorems only,
  imported only by `Candidates/V2.lean`. No axioms.
- `Experience.md` — append the sprint entry.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, `Candidates/V0.lean`, `Candidates/V1.lean`, or any sprint contract
is out of scope.

Do **not** register `Candidates/V2/Taylor.lean` in `lemma.toml`; the allowed
prefixes already cover it because it lives under
`ProofRefinement.PolygonPi.Candidates.V2.*`.

## Acceptance criteria

- [ ] `Candidates/V2.lean` declares `def kappa : ℝ := 2 / 3` and
      `def lambda : ℝ := 1 / 4` on single lines
- [ ] `-- @parent V1` header present
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V2` succeeds
- [ ] evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
      (no `native_decide`, no project axiom, no `sorry`)
- [ ] `score = 5/12`, strictly below parent score `2/3`
- [ ] no import of `Mathlib.Analysis.Real.Pi.*`, bare `Mathlib`, or any
      text-blocked identifier (`pi_lt_sqrtTwoAddSeries`,
      `pi_gt_sqrtTwoAddSeries`, `sqrtTwoAddSeries_step_up`/`_down`,
      `pi_lower_bound_start`, `pi_upper_bound_start`, `pi_gt_three`,
      `pi_gt_3141592`, `pi_lt_3141593`)

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V2
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V2.lean --no-log
```

## Notes / expected obstructions

### The 5th-order Taylor upper bound

Target lemma:

```
lemma sin_lt_taylor5 {x : ℝ} (hx : 0 < x) :
    Real.sin x < x - x ^ 3 / 6 + x ^ 5 / 120
```

Route (nested `strictMonoOn_of_deriv_pos`, following the V1 template):

1. Let `g t := t - t^3/6 + t^5/120 - Real.sin t`. Then `g 0 = 0` and
   `g'(t) = 1 - t^2/2 + t^4/24 - Real.cos t`.
2. Let `h t := 1 - t^2/2 + t^4/24 - Real.cos t`. Then `h 0 = 0` and
   `h'(t) = -t + t^3/6 + Real.sin t = Real.sin t - (t - t^3/6)`.
3. By V1's `sin_gt_sub_cube_div_six` (restate it in the derived file — do not
   import V1), `h'(t) > 0` for `t > 0`. So `h` is strictly monotone on
   `Set.Ici 0`, hence `h t > h 0 = 0` for `t > 0`.
4. So `g'(t) > 0` for `t > 0`, hence `g` is strictly monotone on `Set.Ici 0`,
   hence `g x > g 0 = 0` for `x > 0`. That is exactly the target.

All the derivative-assembly boilerplate is in V1 already: `Real.hasDerivAt_sin`,
`Real.hasDerivAt_cos`, `hasDerivAt_pow n`, `.div_const`, `.add`, `.sub`, then
`(h).deriv`. `fun_prop` closes the `ContinuousOn` side goals. The one lint gotcha
noted in Experience: prefer `change` over `show` when rewriting the lambda
shape, and use `Set.self_mem_Ici` (`Set.left_mem_Ici` is deprecated).

Estimated length: ~90 lines for `sin_lt_taylor5`, plus ~55 lines to restate
`sin_gt_sub_cube_div_six` (a near-verbatim copy of V1's proof, needed because
V2 must not import V1). If the pair pushes V2.lean above ~180 lines total, move
them into `Candidates/V2/Taylor.lean`.

### The `π > 3` step

Target: `Real.pi > 3`. Route:

1. `polygonLower_lt_pi 1 : polygonLower 1 < Real.pi`.
2. `polygonLower 1 = 2^(1+1) · √(2 - Real.sqrtTwoAddSeries 0 1)` by unfolding
   `PolygonCore.polygonLower`.
3. `Real.sqrtTwoAddSeries 0 1 = Real.sqrt 2` by `simp [Real.sqrtTwoAddSeries]`
   (or the `_succ` lemma). Experience §env-notes flags this exact `simp` as
   the right unfold hammer.
4. Prove `Real.sqrt 2 < 23/16`: since `(23/16)^2 = 529/256 > 2`, apply
   `Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) <
   (23/16)^2)` and rewrite the RHS with `Real.sqrt_sq` (guard `0 ≤ 23/16`).
   Alternative: `Real.sqrt_lt_one` variants, or `nlinarith [Real.sq_sqrt
   (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]`.
5. Hence `2 - Real.sqrt 2 > 9/16` (linarith).
6. Prove `Real.sqrt (2 - Real.sqrt 2) > 3/4` by the same
   `sqrt_lt_sqrt`/`sqrt_sq` pattern (guard `0 ≤ 9/16` and `0 ≤ 2 - √2`,
   the latter from step 4).
7. So `polygonLower 1 = 4 · √(2 - √2) > 3`, and `polygonLower_lt_pi 1` gives
   `Real.pi > 3`.

Estimated length: ~35 lines. Inline in V2.lean.

### The lower-conjunct rescaling

At `x = π/2^(n+2) > 0`, `sin_lt_taylor5 hx` gives

    Real.sin x < x - x^3/6 + x^5/120.

Multiply by `2^(n+2) > 0` (use `mul_lt_mul_of_pos_left`, following V1's
`hcube`/`key` pattern), rewrite the LHS with `polygonLower_eq_mul_sin`, and
collapse the RHS with `hpow`, `h4n`, `field_simp; ring` (all as in V1) to

    polygonLower n < Real.pi - Real.pi^3 / (96 * 4^n)
                     + Real.pi^5 / (30720 * 16^n).

Introduce `h16n : (16:ℝ)^n = 4^n * 4^n` alongside V1's `h4n`, both closed with
`← mul_pow; norm_num`.

Then the target `polygonLower n + (1/4)/4^n < Real.pi` reduces to

    Real.pi^3/(96·4^n) - Real.pi^5/(30720·16^n) > (1/4)/4^n.

Multiply through by `4^n > 0`; the inequality becomes

    Real.pi^3/96 - Real.pi^5/(30720·4^n) > 1/4.

Since `Real.pi^5/(30720·4^n) ≤ Real.pi^5/30720` (because `4^n ≥ 1`), it suffices
to show `Real.pi^3/96 - Real.pi^5/30720 > 1/4`, i.e. `320·π^3 - π^5 > 7680`,
i.e. `π^3·(320 - π^2) > 7680`.

Close with `Real.pi > 3` (from the previous step, so `π^3 > 27`) and
`Real.pi ≤ 4` (from `Real.pi_le_four`, so `π^2 ≤ 16` and `320 - π^2 ≥ 304`).
`nlinarith [Real.pi_pos, Real.pi_le_four, sq_nonneg Real.pi]` with the two
premises as hints should handle this in one shot; if not, split it as
`mul_lt_mul` on positive lower bounds and finish with `norm_num`.

### The upper conjunct is unchanged

`kappa = 2/3` is preserved. Copy V1's upper-conjunct proof verbatim — do not
try to also improve kappa in this sprint. The `π ≤ 4 ⇒ π^3 ≤ 64` step is
still the loose factor, but improving it needs an independent `π < c`
(circumscribed polygon or Niven's `22/7 - π`), which is a separate future
architectural sprint. Bundling would violate the one-session bound.

### Do not import `Candidates/V1.lean`

Candidates are self-contained. Restate `sin_gt_sub_cube_div_six` in V2's own
namespace (or in `Candidates/V2/Taylor.lean`) rather than importing V1. This
also keeps the axiom closure and import-closure audits localized.

### If truly `BLOCKED`

Exit only after (a) stating the stuck goal with `lean_goal`, (b) trying at
least two tactically distinct closes on it (not three `simp` flavours), and
(c) writing the exact goal and what you tried into `Experience.md` so the next
planner can attack it from a different angle. Suspect nested-radical arithmetic
(the `Real.sqrt (2 - Real.sqrt 2)` term) if you get stuck early; the
`sq_sqrt`/`sqrt_sq` guards need the non-negativity side conditions supplied by
hand.
