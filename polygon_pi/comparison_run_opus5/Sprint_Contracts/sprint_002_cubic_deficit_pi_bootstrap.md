# sprint_002_cubic_deficit_pi_bootstrap

**Rung type:** `architectural`

**Parent candidate:** `Candidates/V1.lean` (score `71/100`)
**Target file:** `Candidates/V2.lean`
**Side:** `upper`
**Strict improvement required:** yes

## Goal

Replace the entire upper chain. Prove the **uniform, domain-free** deficit bound

```
∀ n,   π - polygonLower n  ≤  π ^ 3 / (96 * 4 ^ n)
```

from the sharp cubic `x - sin x ≤ x ^ 3 / 6` (valid on all of `[0, ∞)`, no
`x ≤ 1` side condition), which collapses the upper side to the single statement
`kappa > π ^ 3 / 96`. Then **bootstrap**: feed the resulting bound back through
itself at depth `2` to turn the crude `Real.pi_le_four` into a sharp rational
upper bound for `π`, and re-close `kappa`.

`lambda` stays at `29/100`. Required: `kappa ≤ 2/3` (score `≤ 0.3767`).
Target: `kappa ≤ 33/100` (score `≤ 0.04`). Stretch: `kappa ≤ 3231/10000`
(score `≤ 331/10000`).

## Rationale

### The two untouched factors, and why both are in scope

The Bulletin's directive 2 says to interrogate every constant in the chain. V1's
upper conjunct is *literally unchanged from V0* and is a product of exactly two
separately-replaceable pieces, both flagged as unexamined by sprint 001's
handover note:

| factor in V1's chain | what it gives | what is true |
|---|---|---|
| `Real.sin_gt_sub_cube` | `sin x > x - x ^ 3 / 4` on `0 < x ≤ 1` | `sin x ≥ x - x ^ 3 / 6` on all of `[0, ∞)` |
| `Real.pi_le_four` (used **twice**) | `π ^ 3 ≤ 64`, and the domain check `π / 2 ^ (n+2) ≤ 1` | `π ^ 3 ≈ 31.006` |

V1 therefore ships `kappa = π ^ 3 / 64 ≤ 64/64 = 1`. Note that
`Real.pi_le_four` is doing *two different jobs* there: it supplies the numeric
`π ^ 3 ≤ 64` **and** it is what makes `Real.sin_gt_sub_cube`'s domain hypothesis
`x ≤ 1` discharge. That coupling is the structural defect this sprint removes —
the sharp cubic holds globally, so once it is in place the domain job disappears
entirely and `Real.pi_le_four` survives only as a numeric seed that can then be
replaced independently.

### Why this is architectural, not a precision push

Two genuinely new analytic ingredients, neither a smaller version of anything
already in the tree:

1. **A global cubic Taylor bound with an exact-square-free derivative ladder.**
   `ψ x := x ^ 3 / 6 - x + sin x` has `ψ 0 = 0` and
   `ψ' x = x ^ 2 / 2 - 1 + cos x ≥ 0` **for every real `x`** — this is exactly
   the content of `Real.one_sub_sq_div_two_lt_cos`, which `Experience.md`
   (sprint_000) records as present in this Mathlib. So `ψ` is monotone on all of
   `ℝ` by `monotone_of_hasDerivAt_nonneg`, the idiom sprint_001 confirmed
   working. The resulting deficit bound is *uniform in `n` with the `n`
   cancelling exactly*: with `N = 2 ^ (n+2)`, `x = π / N`,

   ```
   4 ^ n (π - polygonLower n) = 4 ^ n · N · (x - sin x)
                              ≤ 4 ^ n · N · x ^ 3 / 6
                              = 4 ^ n π ^ 3 / (6 · N ^ 2)
                              = 4 ^ n π ^ 3 / (6 · 4 ^ (n+2))
                              = π ^ 3 / 96.
   ```

   No `n` survives, no interval hypothesis survives. The upper side becomes one
   number, mirroring what sprint 001 did to the lower side.

2. **A self-referential bootstrap of the `π` constant.** Once `∀ n, π ≤
   polygonLower n + π ^ 3 / (96 · 4 ^ n)` is a theorem, it is *itself* a
   `π`-upper-bound generator: instantiate at `n = 2`, bound `polygonLower 2`
   above by a rational, and any hypothesis `π ≤ c` yields the strictly better
   `π ≤ p₂ + c ^ 3 / 1536`. This is a new logical move for this workspace —
   using the theorem's own conclusion to sharpen its own input — and it is
   contraction-mapping convergent at **fixed depth 2**, so it buys near-optimal
   precision *without* any deeper nested radical. Iterating from
   `c₀ = 4 (Real.pi_le_four)`:

   | round | `kappa = c ^ 3 / 96` | next `c = p₂ + kappa/16` |
   |---|---|---|
   | 0 | `2/3 = 0.66667` | `3.16312` |
   | 1 | `0.3296651` | `3.1420505` |
   | 2 | `0.3231233` | `3.1416417` |
   | 3 | `0.3229972` | `3.1416338` |
   | fixed point | `0.3229943` | `3.1416323` |

   (computed with `p₂ = 3.1214464`, the 7-digit rational certified below; true
   `polygonLower 2 = 3.12144515…`, true `π ^ 3 / 96 = 0.32298205`.)

Both ingredients are reusable and *piecewise improvable* by a successor, which
is the third bullet of the planner objective: a later sprint can sharpen the
cubic to a quintic, or sharpen `p₂` by going to depth 3, and each drops straight
into the same bootstrap without re-deriving anything.

### Why not the alternatives

- **Lower-side depth push (`lambda` `29/100 → 31/100`).** Rejected. Sprint 001
  proved the lower side is analytically closed with a hard ceiling of
  `π - 2√2 = 0.3131655`; the entire remaining lower headroom is `0.0232`, versus
  `0.677` on the upper side. It is also pure precision on a chain that ran last
  sprint, which directive 1 demotes. It becomes the right sprint *after* this
  one, when the upper side is within `10 ^ -4` of its floor.
- **Upper-side limit argument** (`sup_n D n = lim_n D n = π ^ 3 / 96` via
  `Filter.Tendsto` plus V1's existing `deficit_step` monotonicity). Rejected as
  strictly dominated: it needs `lim_{x→0} (x - sin x)/x ^ 3 = 1/6`, which in
  Lean means either L'Hôpital three times or the `sin` power series, and it
  arrives at exactly the same constant that ingredient 1 above reaches with one
  `monotone_of_hasDerivAt_nonneg` call and no limit machinery.
- **Richardson extrapolation** `(4 · polygonLower (n+1) - polygonLower n)/3`,
  whose error is `O(N ^ -4)`, as a cheaper route to a sharp rational `π`.
  Rejected for *this* sprint: it needs the quintic `sin x ≤ x - x ^ 3/6 +
  x ^ 5/120` first, and it competes with the bootstrap for the same job — the
  bootstrap reaches `0.3229943` against the true ceiling `0.3229820`, i.e. it
  leaves only `1.2 × 10 ^ -5` for extrapolation to recover. Not worth it now;
  recorded here so a later planner does not re-derive the comparison.
- **Filing a proposal.** Nothing here needs one. No new import is required (the
  seed lemmas are in modules `Proof/Main.lean` already pulls, or in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` /
  `Mathlib.Analysis.Calculus.Deriv.MeanValue`, both already reachable and both
  used by V1's ancestors), and no claim here has yet been attacked and blocked in
  a generator session, which `Proposals/README.md` requires before filing.

### The witness that this is provable

Every load-bearing lemma is one that `Experience.md` records as **confirmed
present in this Mathlib**:

- `Real.one_sub_sq_div_two_lt_cos (hx : x ≠ 0) : 1 - x ^ 2 / 2 < cos x`
  (sprint_000 entry) — gives `ψ' x > 0` for `x ≠ 0`; at `x = 0`,
  `ψ' 0 = 0 - 1 + 1 = 0`, so a two-case `rcases eq_or_ne x 0` closes
  `0 ≤ ψ' x` globally.
- `monotone_of_hasDerivAt_nonneg` (sprint_001 entry, confirmed working, no
  `ContinuousOn`/`Convex`/`interior` side goals).
- `Real.hasDerivAt_sin`, `hasDerivAt_pow`, `.div_const`, `.sub`, `.add`.
- `Real.sq_sqrt` + `Real.sqrt_nonneg` + `nlinarith` staged one radical level at a
  time (sprint_001: "each stage is a single `nlinarith` with exactly three
  hints"; do **not** hand the nested expression to one call).
- `pow_le_pow_left₀`, `le_div_iff₀`, `div_lt_iff₀'`, `mul_lt_mul_of_pos_left`,
  `positivity`, `field_simp`, `gcongr`.

The radical certification needed is the **upper** companion of the one V1
already ships, at 7 digits, and each inequality below has been checked
numerically:

```
√2         > 1.4142135      (1.4142135 ^ 2 = 1.99999982… < 2)
√(2 + √2)  > 1.8477590      (1.8477590 ^ 2 = 3.41421… < 2 + 1.4142135)
√(2 - √(2 + √2)) < 0.3901808   (0.3901808 ^ 2 = 0.15224106… > 2 - 1.8477590)
polygonLower 2 = 8 √(2 - √(2 + √2)) < 3.1214464
```

Note the direction flip relative to V1: an **upper** bound on `polygonLower 2`
needs a **lower** bound on the inner radical's argument, hence **lower** bounds
on `√2` and `√(2 + √2)`. V1's lemmas go the other way and cannot be reused as
they stand.

## Concrete edits expected

- `Candidates/V2/CubicDeficit.lean` — the new derived theorems. Theorems and
  lemmas only, never `axiom`. Expected contents:
  - `∀ x : ℝ, 0 ≤ x → x - Real.sin x ≤ x ^ 3 / 6` (or the equivalent
    `x - x ^ 3 / 6 ≤ Real.sin x`), proved by `monotone_of_hasDerivAt_nonneg` on
    `fun t => t ^ 3 / 6 - t + Real.sin t`, with **no** upper restriction on `x`;
  - `∀ n : ℕ, Real.pi - polygonLower n ≤ Real.pi ^ 3 / (96 * 4 ^ n)`, derived
    from it with the `n` cancelling algebraically — **not** by a per-`n` case
    analysis and **not** using `Real.sin_gt_sub_cube`;
  - the staged rational certification `polygonLower 2 < 31214464/10000000`
    (three `nlinarith` stages, one radical level each);
  - the bootstrap step, stated so it can be applied repeatedly, e.g.
    `∀ c : ℝ, Real.pi ≤ c → Real.pi ≤ 31214464/10000000 + c ^ 3 / 1536`.
- `Candidates/V2/DeficitMonotone.lean` — a **verbatim copy** of
  `Candidates/V1/DeficitMonotone.lean` with the namespace changed to
  `ProofRefinement.PolygonPi.Candidates.V2`, so that `V2` is self-contained and
  independently replayable. Do not edit, move, or import `Candidates/V1/`.
- `Candidates/V2.lean` — `-- @parent V1`, `def lambda : ℝ := 29/100` and
  `def kappa : ℝ := <literal>` each on a single line, the lower conjunct carried
  over from `V1` (including its `√2` / nested-radical *upper* lemmas, which the
  lower side still needs in the original direction), and the new upper conjunct.
- `Experience.md` — append the sprint entry, including any lemma-name drift you
  hit and the exact final `kappa` with the number of bootstrap rounds used.

Nothing else. Do **not** edit `lemma.toml` (the module paths
`ProofRefinement.PolygonPi.Candidates.V2.*` already match an allowed prefix),
`PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, sprint contracts, or any
older candidate.

## Acceptance criteria

Required — the sprint fails without all of these:

- [ ] `Candidates/V2.lean` declares `def lambda : ℝ := 29/100` and
      `def kappa : ℝ := <rational>` **each on a single line**, with
      `kappa ≤ 2/3`
- [ ] `Candidates/V2/CubicDeficit.lean` contains a theorem whose statement is,
      up to naming, `∀ n : ℕ, Real.pi - polygonLower n ≤ Real.pi ^ 3 / (96 * 4 ^ n)`
- [ ] that theorem's proof does **not** mention `Real.sin_gt_sub_cube` and does
      **not** depend on any hypothesis of the form `Real.pi / 2 ^ (n + 2) ≤ 1`
      (grep the file: `sin_gt_sub_cube` must not appear anywhere in
      `Candidates/V2.lean` or `Candidates/V2/`)
- [ ] `Candidates/V2/CubicDeficit.lean` contains a lemma of the shape
      `0 ≤ x → x - Real.sin x ≤ x ^ 3 / 6`, with no upper bound hypothesis on `x`
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V2` succeeds
- [ ] the evaluator passes all twelve stages
- [ ] axiom closure of `polygon_pi_constant_search` is a subset of
      `{propext, Classical.choice, Quot.sound}`
- [ ] `score = kappa - lambda < 71/100`

Target — attempt this before declaring done; it is one bootstrap round past the
required bar and the whole reason the sprint is shaped this way:

- [ ] `kappa ≤ 33/100`, via a certified rational upper bound for
      `polygonLower 2` and at least one application of the bootstrap step
      starting from `Real.pi_le_four`

Stretch — only after the target is met, and only if the session still has room.
Each extra round is `≈ 10` lines of `norm_num` arithmetic reusing the same step
lemma:

- [ ] `kappa ≤ 3231/10000` (three bootstrap rounds), giving score `≤ 331/10000`

If the target is not reached, ship the required `kappa ≤ 2/3` candidate and
write the exact blocking goal into `Experience.md`. A partial sprint that lands
`2/3` with a precise obstruction note is a good outcome; an unbuildable file is
not.

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V2
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V2.lean --no-log
```

## Notes / expected obstructions

Read the `sprint_000` and `sprint_001` entries in `Experience.md` first. The
`monotone_of_hasDerivAt_nonneg` recipe, the `4 ^ n = 2 ^ n * 2 ^ n` /
`2 ^ (n+2) = 4 * 2 ^ n` identity idioms, and the staged-`nlinarith` radical
recipe are all written out there and all transfer directly.

Specific things likely to cost time:

- **Forbidden-token collisions in your own lemma names.** The static scan is a
  plain substring match on comment-stripped source (`Evaluator.py:354`).
  `pi_lt_d`, `pi_gt_d`, `pi_gt_314`, `pi_lt_315`, `pi_upper_bound_start`,
  `pi_lower_bound_start` are forbidden **tokens**, so a lemma named
  `pi_lt_depth2` or `pi_upper_bound_start_seed` will hard-fail stage 4 even
  though it is your own lemma. Name the bootstrap results something like
  `pi_le_bootstrap_step`, `pi_le_round_one`, `pi_le_final`. Rational literals
  such as `31416417/10000000` are not affected.
- **Assembling the `HasDerivAt` for `ψ t = t ^ 3 / 6 - t + sin t`.** State the
  derivative in the *unsimplified* form the combinators actually produce
  (`3 * t ^ 2 / 6 - 1 + cos t` from `((hasDerivAt_pow 3 t).div_const 6).sub
  (hasDerivAt_id t) |>.add (Real.hasDerivAt_sin t)`) and prove the
  non-negativity lemma about *that* expression, rather than `simp`-normalizing
  first. sprint_001 records that `exact` closes the derivative goal with no
  `simp` when the shape is left raw, and that `simpa` is only needed to repair
  `const_mul` / `const_sub` artefacts.
- **The `x = 0` case.** `Real.one_sub_sq_div_two_lt_cos` has hypothesis
  `x ≠ 0`. Split with `rcases eq_or_ne x 0 with rfl | hx`; the `rfl` branch is
  `norm_num [Real.cos_zero]`.
- **Fallback if that seed lemma has drifted.** Build the same conclusion with a
  second application of the identical idiom: `Real.sin_lt` / `Real.sin_le`
  (`sin x < x` for `0 < x`) makes `t ↦ cos t - 1 + t ^ 2 / 2` have derivative
  `t - sin t ≥ 0`, giving `cos t ≥ 1 - t ^ 2 / 2`, which then seeds `ψ`. Two
  rungs of the same ladder, no new machinery. Record which route you used.
- **The `n` cancellation.** After `polygonLower_eq_mul_sin`, the goal is
  `π - 2 ^ (n+2) * sin (π / 2 ^ (n+2)) ≤ π ^ 3 / (96 * 4 ^ n)`. Apply the cubic
  at `x = π / 2 ^ (n+2)`, multiply through by `2 ^ (n+2) > 0`, then close with
  the recorded `h4n : (4:ℝ) ^ n = 2 ^ n * 2 ^ n` plus `hpow : (2:ℝ) ^ (n+2) =
  4 * 2 ^ n`, `field_simp`, `ring`. This is the same shape as V1's `hid` step;
  do not fight it with `ring_nf` alone.
- **Direction of the radical bounds.** As noted in the Rationale, the *upper*
  bound on `polygonLower 2` needs *lower* bounds on `√2` and `√(2 + √2)` and
  then an *upper* bound on `√(2 - √(2 + √2))`. V1's three lemmas go the other
  way. You need both families in `V2` — V1's originals for the lower conjunct,
  the new flipped ones for the bootstrap. Keep them clearly named
  (`..._lt` / `..._gt`) so a successor can find them.
- **No circularity.** The bootstrap is not circular: `deficit_le` is proved
  outright with `π ^ 3` symbolic, and only *afterwards* is a numeric hypothesis
  `π ≤ c` substituted to produce a numeric conclusion. Keep those two lemmas
  separate in the file so the ordering is visible; do not try to state a single
  fixed-point lemma.
- **Strictness.** The contract's upper conjunct is strict (`π < polygonLower n +
  kappa / 4 ^ n`). Your deficit bound is non-strict (`≤ π ^ 3 / (96 * 4 ^ n)`);
  strictness comes for free from choosing the rational `kappa` strictly above
  the certified bound on `π ^ 3 / 96`. Do not chase a strict version of the
  Taylor inequality.
- **Do not weaken the contract**, do not touch `polygon_pi_constant_search`'s
  name or type, and do not lower `lambda`. Stage 5 also checks
  `lambda < kappa` — at `lambda = 29/100` and a stretch `kappa = 3231/10000`
  that holds with `0.0331` to spare, but it is the reason `lambda` must not be
  raised in the same sprint.

**For the next planner:** after this sprint the upper side is within roughly
`1.2 × 10 ^ -5` of its analytic floor `π ^ 3 / 96 = 0.3229820`, and the lower
side's remaining headroom (`29/100 → π - 2√2 = 0.3131655`) is `0.0232`, i.e.
about three orders of magnitude larger. Sprint 003 should be `lower`, and per
sprint_001's ladder it is a depth-3 or depth-4 rational certification with no new
analysis — the first legitimately `precision`-typed sprint of this run. The
quintic Taylor bound and the Richardson extrapolation both remain unspent, but
both now buy less than `10 ^ -4` and should be held until the lower side is
exhausted.
