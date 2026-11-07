# sprint_005_optimality_certificate

**Rung type:** `infrastructure`
_(the core deliverable is a **converse** theorem — the first statement in this
workspace quantified over *all* candidates rather than proved about one — and it
has no score effect by construction. It is not "tooling": it contains the first
genuine limit argument the workspace has needed. The optional precision items
P2/P3 are gated behind it and are explicitly labelled as precision work. See
"Honesty about the rung type".)_

**Parent candidate:** `Candidates/V4.lean` (score `9816589/1000000000 = 0.009816589`)
**Target file:** `Candidates/V5.lean`
**Side:** `both`
**Strict improvement required:** no

## Goal

Prove that the admissible set of the scored contract is exactly

    { (lam, kap) : 0 ≤ lam < π - 2√2 }  ×  { kap : π ^ 3 / 96 ≤ kap },

so that **no candidate, ever, can score below `π ^ 3 / 96 - (π - 2√2)`**, and
certify that real number from both sides with the rational bounds `V4` already
proves. The result is a machine-checked bracket

    9816471/1000000000  <  π ^ 3 / 96 - (π - 2√2)  <  kappa - lambda = 9816589/1000000000,

i.e. the benchmark's true optimum is pinned to a window of width `1.18e-7` and
the incumbent sits at the top of that window. After this the frontier is closed
with a proof rather than with a plateau in `frontier.csv`.

## Rationale

### Why not another digit push

`Experience.md` sprint 004 measured the remaining headroom exactly: `1.12e-8` on
`kappa` (above the unreachable floor `π ^ 3 / 96 = 0.322982048753…`) and
`5.78e-8` on `lambda` (below the unreachable ceiling
`π - 2√2 = 0.313165528844…`), for a total of `6.91e-8` out of a score of
`9.82e-3` — seven parts per hundred thousand. Every remaining score-moving
sprint is a rational re-certification through one of the two anchors sprints 002
–004 already built. The standing directive's first line ("prefer architectural
rungs over precision pushes") and its fourth ("interrogate every constant, not
just the obvious one") both point away from that.

### The factor that has never been interrogated

Sprints 001–004 interrogated, in order: the binding depth of the lower conjunct,
the Taylor order, the Taylor order again, and the anchor. **The one factor never
questioned is the target itself** — every sprint has assumed, on the strength of
an informal note in `Experience.md`, that `π ^ 3 / 96` is a floor and
`π - 2√2` a ceiling. Neither claim is proved anywhere in the workspace. They are
prose in a docstring. This sprint turns them into theorems, and in doing so
answers the only question a reader of the artifact can still ask: *is
`0.009816589` good, or merely the best this loop happened to reach?*

The mathematics is a genuine converse and it is not free:

* `lam < π - 2√2` is one line (instantiate the contract at `n = 0`), but
* `π ^ 3 / 96 ≤ kap` is an **asymptotic** statement. It is false at every finite
  `n`: for each individual `n`, `4 ^ n (π - polygonLower n)` sits strictly below
  the floor, and only the limit forces `kap` above it. The workspace has never
  needed a limit, an Archimedean step, or an `∀ ε > 0` argument before; every
  previous sprint was finitely many inequalities between explicit rationals.
  The ingredient that makes it cheap is `V3`'s `deficit_ge` — the quintic lower
  deficit bound, which has been used only as a bootstrap input and never as an
  asymptotic statement.

### The structural payoff, which is why this is worth the last sprint

Once `valid_of_bracket` (the converse direction, §4 below) exists, the scored
contract's proof in `V5.lean` collapses to three lines and the *entire* problem
is reduced to two one-dimensional certification questions:

    how tightly can we bound  π ^ 3 / 96  from above,  and  π - 2√2  from below?

Nothing else about polygons, deficits, monotonicity or Taylor order can ever
matter again. That is exactly the "restructuring of the incumbent's chain into
something a successor can improve piecewise" that the planner's objective (3)
asks for, and it is the honest ending for this run: a successor sprint becomes a
one-line literal change plus a sharper radical certification, with a proved
statement of what it is chasing and how much is left.

### Alternatives considered and rejected

- **(A) Widen `lambda` by re-certifying the depth-2 lower chain at 12 digits and
  refreshing the `π ^ 5` correction with `pi_le_sharp`.** Worth `2.1e-8`
  (verified: the depth-2 quintic truncation pins the fixed point at
  `π - 3.62e-8`, so the best reachable `lambda` there is `0.313165492`). Pure
  grind on the factor sprint 003 already ground, and it recovers less than a
  third of the remaining gap. Rejected as a sprint; the better depth-3 version
  survives as the optional item **P2**.
- **(B) A cosine anchor for the *lower* bound on `π`, mirroring sprint 004.**
  `cos(π/64) = s₅/2` with `s₅` certified from *above* inverts through a *lower*
  polynomial bound on `cos`. The only such bound available is
  `Real.one_sub_sq_div_two_lt_cos`, whose truncation at `t = π/64` costs
  `t ^ 4 / 24 = 2.4e-7` in `cos`, i.e. `3.2e-4` in `π` — useless. Making it work
  needs the sextic rung `cos t ≥ 1 - t²/2 + t⁴/24 - t⁶/720` (obtainable by
  squaring `V3`'s quintic through the half-angle identity, so it is real work
  but not hard). Rejected: it buys the same `≤ 5.8e-8` as the far cheaper P2,
  and it is a fourth consecutive sprint on the Taylor-order/anchor axis.
- **(C) Prove the *boundary* case of the converse, `π ^ 3 / 96 ≤ kap ⟹
  admissible`.** This needs `4 ^ n (π - polygonLower n) < π ^ 3 / 96` *strictly*,
  which needs a septic rung (`x - sin x ≤ x³/6 - x⁵/120 + x⁷/5040`) or a
  `StrictMonoOn` redo of the cubic. Deliberately out of scope: `kappa` is a
  rational literal and the strict-inequality form of the converse (§4) already
  characterizes every rational `kap`. Do not spend session budget here.
- **(D) Formalize `Tendsto (fun n => 4 ^ n * (π - polygonLower n)) atTop (𝓝 (π ^ 3 / 96))`
  as a `Filter.Tendsto` statement.** Prettier, strictly more work (`Metric.tendsto_atTop`
  plumbing, `squeeze_zero`, and the same Archimedean step underneath), and it is
  not what the optimality claim needs. The ε-form in §2 is the whole content.
- **(E) Ship nothing but a better `lambda` (the "one last digit" sprint).** This
  is what the loop does when it has stopped having ideas, and sprint 004's own
  Experience entry names it as the characteristic failure mode. It is available
  here as a gated optional item precisely so that it cannot displace the core.

## Concrete edits expected

- `Candidates/V5/DeficitMonotone.lean` — copy of `V4`'s, namespace renamed to
  `…Candidates.V5`. Unchanged content.
- `Candidates/V5/CubicDeficit.lean` — copy of `V4`'s, namespace renamed.
- `Candidates/V5/QuinticDeficit.lean` — copy of `V4`'s, namespace renamed.
- `Candidates/V5/CosineAnchor.lean` — copy of `V4`'s, namespace renamed
  (optionally extended by P2's four new radical stages; see §5).
- `Candidates/V5/Optimality.lean` — **new**, the substance of the sprint.
- `Candidates/V5.lean` — `-- @parent V4`, the literals, the contract proof
  routed through `valid_of_bracket`, and the exported bracket theorem.
- `Experience.md` — append the sprint entry.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, or any older candidate is out of scope for every sprint.

## Priority order — read this before writing any Lean

The items below are strictly ordered. **Do not start P2 until the evaluator has
passed on a `V5` containing P0 and P1**, with `V4`'s literals unchanged. A `V5`
that ships P0 alone, with `kappa` and `lambda` copied verbatim from `V4`, is a
successful sprint; `Strict improvement required: no` is not a formality.

| item | content | score effect |
|---|---|---|
| **P0** | the optimality certificate (§1–§3) | none |
| **P1** | the converse `valid_of_bracket`, and `V5`'s contract proof routed through it (§4) | none |
| **P2** | *optional*: depth-3 lower anchor, `lambda → 313165527/1000000000` (§5) | `−5.6e-8` |
| **P3** | *optional*: the secondary depth-10 contract (§6) | none (second frontier) |

## The plan, with every constant pre-verified in exact arithmetic

All constants below were checked by the planner in exact `Fraction` arithmetic
against 60-digit decimal values. Margins are quoted so the generator can tell a
formalization failure from a wrong number.

Reference values:

    π           = 3.14159265358979323846…
    π ^ 3 / 96  = 0.322982048753123126…      (the floor,   unattained)
    π − 2√2     = 0.313165528843603140…      (the ceiling, attained at n = 0)
    optimum     = 0.009816519909519985…      (= floor − ceiling)
    V4 score    = 0.009816589                (6.91e-8 above the optimum)

### 1. Scaling the two deficit bounds once, in the form the rest of the file uses

```lean
lemma deficit_scaled_le (n : ℕ) :
    4 ^ n * (Real.pi - polygonLower n) ≤ Real.pi ^ 3 / 96

lemma deficit_scaled_ge (n : ℕ) :
    Real.pi ^ 3 / 96 - Real.pi ^ 5 / (30720 * 4 ^ n)
      ≤ 4 ^ n * (Real.pi - polygonLower n)
```

Both are `deficit_le n` / `deficit_ge n` multiplied by `4 ^ n > 0`. The first is
already inlined in `V4.lean`'s contract proof (a two-step `calc`, then
`field_simp`); lift it out and do the second the same way. `deficit_ge`'s right
tail is stated as `π ^ 5 / (30720 * 4 ^ n * 4 ^ n)`, so exactly one factor of
`4 ^ n` cancels — keep the `4 ^ n * 4 ^ n` form and let `field_simp; ring` do it,
per sprint 002's note.

Also useful, one line from the contract:

```lean
lemma scaled_lt_kappa {lam kap : ℝ} (h : ValidPolygonBound lam kap) (n : ℕ) :
    4 ^ n * (Real.pi - polygonLower n) < kap
```

from `(h.2.2 n).2 : π < polygonLower n + kap / 4 ^ n` via
`lt_div_iff₀ (h4n : 0 < 4 ^ n)` (confirmed to resolve, sprint 002) plus a
`linarith` to move `polygonLower n` across. Note `V4.lean` already does this
manipulation in the opposite direction.

### 2. The Archimedean step and the floor

```lean
lemma nat_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 ^ n
```

by induction; `| zero => norm_num`, and in the successor case `push_cast` then
`k + 1 ≤ 4 ^ k + 4 ^ k ≤ 4 ^ (k+1)` using `one_le_pow₀` (confirmed present,
sprint_000) and `pow_succ`. Do **not** go looking for `Nat.lt_two_pow`-style
lemmas or for `exists_pow_lt_of_lt_one`; the induction is five lines and has no
name risk.

```lean
theorem admissible_kappa_ge {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    Real.pi ^ 3 / 96 ≤ kap
```

Proof shape (no numeric input at all — everything stays symbolic in `π`):

- `by_contra`, `push_neg`, set `ε := π ^ 3 / 96 - kap`, `hε : 0 < ε`.
- `obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi ^ 5 / (30720 * ε))`. `exists_nat_gt
  (x : α) : ∃ n : ℕ, x < n` is the Archimedean lemma; if the name has drifted,
  search for it before inventing a substitute, and note that the only property
  needed is "ℝ is Archimedean".
- `hn.trans_le (nat_le_four_pow n)` gives `π ^ 5 / (30720 * ε) < 4 ^ n`, hence
  `π ^ 5 < 30720 * ε * 4 ^ n` by `div_lt_iff₀` (positivity of `30720 * ε`).
- From `deficit_scaled_ge n` and `scaled_lt_kappa h n`:
  `π ^ 3 / 96 - π ^ 5 / (30720 * 4 ^ n) < kap`, i.e.
  `ε < π ^ 5 / (30720 * 4 ^ n)`, i.e. `30720 * ε * 4 ^ n < π ^ 5` by
  `lt_div_iff₀`. Contradiction with the previous line, `linarith`.

Keep every step division-free where you can: the two-`have` pattern sprint 003
recommends (`have hb : … := by norm_num` beside the inequality, then `linarith`)
applies here too, and `linarith` will not see through a division it has not been
handed in cleared form.

```lean
theorem admissible_lambda_lt {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    lam < Real.pi - 2 * Real.sqrt 2
```

from `(h.2.2 0).1 : polygonLower 0 + lam / 4 ^ 0 < π`, `polygonLower_zero_eq`
(already in `V4.lean` — move it into `Optimality.lean` and do not duplicate the
name), and `norm_num` on `4 ^ 0`.

```lean
theorem admissible_score_gt {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) < kap - lam
```

is then `linarith` from the two.

### 3. Certifying the optimum from below, and the bracket

```lean
theorem optimum_gt :
    (9816471/1000000000 : ℝ) < Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2)
```

Inputs, all already proved in `V4` and carried over unchanged:

| input | file | value |
|---|---|---|
| `pi_ge_round_five` | `QuinticDeficit` | `3.141592597 ≤ π` |
| `pi_le_sharp` | `CosineAnchor` | `π ≤ 3.1415926848` |
| `s1_gt` (`= √2` after `Real.sqrtTwoAddSeries_one`) | `CosineAnchor` | `1.414213562373 < √2` |

Exact arithmetic, verified:

    (3141592597/1000000000) ^ 3 / 96 = 0.3229820312994086786…      ≤ π ^ 3 / 96
    3.1415926848 − 2 · 1.414213562373 = 0.313165560054              ≥ π − 2√2
    difference                        = 0.0098164712454086786…      > 9816471/1000000000   ✓ (margin 2.45e-10)

Use `pow_le_pow_left₀ (by norm_num) pi_ge_round_five 3` for the cube (10-digit
numerator, 30-digit intermediates — sprint 004 handled 33 digits), then the
division-free `have hb : (3141592597/1000000000 : ℝ) ^ 3 > 96 * (322982031299/1000000000000) := by norm_num`
pattern and `linarith`. `s1_gt` is stated about `Real.sqrtTwoAddSeries 0 1`;
`Real.sqrtTwoAddSeries_one` converts it to `Real.sqrt 2` (`V4/CosineAnchor.lean`
already `rw`s that lemma in the other direction).

```lean
theorem admissible_score_gt_rat {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    (9816471/1000000000 : ℝ) < kap - lam :=
  optimum_gt.trans (admissible_score_gt h)
```

**This is the headline theorem of the sprint**: *every* candidate that satisfies
the scored contract, past, present or future, has score above `0.009816471`.

Then in `V5.lean`, the two-sided bracket on the true optimum:

```lean
theorem optimum_bracket :
    (9816471/1000000000 : ℝ) < Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) ∧
    Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) < kappa - lambda
```

The right half is `admissible_score_gt polygon_pi_constant_search` — the
candidate's own contract, applied to itself. Together with `kappa - lambda =
9816589/1000000000` this says the optimum lies in a window of width `1.18e-7`
and the incumbent is at its top edge. Optionally also state the arithmetic
consequence

```lean
theorem optimality_gap_lt :
    kappa - lambda - (Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2))
      < 118/1000000000
```

(with `47/1000000000` in place of `118/1000000000` if P2 lands; see §5).

### 4. The converse, and the collapse of the contract proof

```lean
theorem valid_of_bracket {lam kap : ℝ} (h0 : 0 ≤ lam)
    (hlam : lam < Real.pi - 2 * Real.sqrt 2)
    (hkap : Real.pi ^ 3 / 96 < kap) :
    ValidPolygonBound lam kap
```

This is `V4.lean`'s existing contract proof with two substitutions and no new
mathematics: the lower conjunct is `deficit_ge_zero_deficit` plus
`polygonLower_zero_eq` plus `hlam`; the upper conjunct is `deficit_scaled_le`
plus `hkap`; `0 < kap` follows from `hkap` and `positivity`/`Real.pi_pos`.

`V5.lean`'s contract proof then becomes

```lean
theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa :=
  valid_of_bracket (by norm_num [lambda]) lambda_lt_ceiling
    (by rw [kappa]; exact pi_cube_div_lt_sharp)
```

where `lambda_lt_ceiling : lambda < Real.pi - 2 * Real.sqrt 2` is `V4`'s
`lambda_lt_deficit_zero` restated against `2 * √2` instead of `polygonLower 0`.

With §2 and §4 together the workspace then contains, as theorems:

    (0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 < kap)  →  ValidPolygonBound lam kap
    ValidPolygonBound lam kap  →  (0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 ≤ kap)

i.e. the admissible set is determined up to the single boundary point
`kap = π ^ 3 / 96`, which no rational literal can hit anyway. Say exactly this in
the `V5.lean` module docstring, and say that closing the boundary case needs a
septic Taylor rung and was deliberately left open.

### 5. P2 (optional) — the depth-3 lower anchor

Only after P0 + P1 build and the evaluator passes. This is the score-moving
item and it is a **precision** push: same quintic chain as sprint 003, evaluated
at depth 3 instead of depth 2, with the `π ^ 3` and `π ^ 5` inputs supplied by
`V4`'s existing sharp bounds so that **no iteration is needed** — one step, like
sprint 004's inversion.

Why depth 3 rather than a sixth bootstrap round at depth 2: the depth-2 quintic
truncation `16 · x ⁷/5040` at `x = π/16` is `3.6e-8` and pins the depth-2 fixed
point there no matter how many rounds are run (verified). At depth 3 the same
term is `5.6e-10`. The cost is one extra level of the well-conditioned
`+`-nested chain plus one `2 − ·` step, which sprint 004's margin table says is
affordable at twelve decimals.

Four new radical stages, all in the *upper* direction on the series (the mirror
of `CosineAnchor.lean`'s `s1_gt … s5_gt`, same three-hint `nlinarith` recipe,
one multiplication per call):

| lemma | statement | margin |
|---|---|---|
| `s1_lt` | `sqrtTwoAddSeries 0 1 < 1414213562374/1000000000000` | `a₁² − 2 = 2.56e-12` |
| `s2_lt` | `sqrtTwoAddSeries 0 2 < 1847759065023/1000000000000` | `a₂² − (2 + a₁) = 6.71e-13` |
| `s3_lt` | `sqrtTwoAddSeries 0 3 < 1961570560807/1000000000000` | `a₃² − (2 + a₂) = 1.69e-12` |
| `sqrt_two_sub_s3_gt` | `196034280657/1000000000000 < √(2 − sqrtTwoAddSeries 0 3)` | `(2 − a₃) − c² = 2.93e-13` |

(True values: `s₃ = 1.96157056080646…`, `2 − s₃ = 0.0384294391935…`,
`√(2 − s₃) = 0.19603428065912…`.)

Then

```lean
lemma polygonLower_three_eq :
    polygonLower 3 = 16 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 3)
theorem polygonLower_three_gt : (3136548490512/1000000000000 : ℝ) < polygonLower 3
theorem pi_ge_depth_three : (3141592652724/1000000000000 : ℝ) ≤ Real.pi
```

`polygonLower n = 2 ^ (n+1) * √(2 - sqrtTwoAddSeries 0 n)` definitionally, so
`rw [polygonLower]` and then `norm_num` on `2 ^ (3+1) = 16` — **but** watch the
trap `V4/CosineAnchor.lean` records: a bare `norm_num` may also fire the
`sqrtTwoAddSeries` simp set and unfold the series. If it does, use
`show (2:ℝ) ^ (3+1) * _ = _` plus `norm_num` on the coefficient only, or
`congr 1`.

`pi_ge_depth_three` is one step from `deficit_ge 3`
(`norm_num` normalises `96 * 4 ^ 3` to `6144` and `30720 * 4 ^ 3 * 4 ^ 3` to
`125829120`, as it did at `n = 2` in sprints 002/003):

    π  ≥  polygonLower 3 + π ^ 3 / 6144 − π ^ 5 / 125829120
       ≥  3.136548490512 + 0.005046594239 − 0.000002432027
       =  3.141592652724                                   (true π is 8.65e-10 above)

with the two numeric inputs

    π ^ 3 / 6144       ≥ 5046594239/1000000000000   from  pi_ge_round_five  (3.141592597 ≤ π)
    π ^ 5 / 125829120  ≤ 2432027/1000000000000      from  π ≤ 3.1415927

For the second one **do not** raise `31415926848/10000000000` to the fifth power
(55-digit intermediates for a bound that needs seven digits). Weaken first:
`have h : Real.pi ≤ 31415927/10000000 := pi_le_sharp.trans (by norm_num)`, then
`pow_le_pow_left₀ Real.pi_pos.le h 5`; the exact value is
`(3.1415927) ^ 5 / 125829120 = 2.432026127…e-6 < 2.432027e-6` ✓.

Finally

```lean
def lambda : ℝ := 313165527/1000000000
```

certified by `pi_ge_depth_three` and `s1_lt` (via `Real.sqrtTwoAddSeries_one`):
`3.141592652724 − 2 · 1.414213562374 = 0.313165527976 > 0.313165527` ✓
(margin `9.76e-10`; the exact ceiling `π − 2√2` is `1.84e-9` above the
literal, so P2 recovers all but `1.84e-9` of the lower side). Score becomes
`32298206/100000000 − 313165527/1000000000 = 9816533/1000000000 = 0.009816533`.

If P2 lands, **also re-tighten §3**: `optimum_gt` with `pi_ge_depth_three` in
place of `pi_ge_round_five` and `s1_lt` in place of the 9-digit `sqrt_two_lt`
gives

    (3141592652724/1000000000000) ^ 3 / 96 = 0.32298204848609…
    3.1415926848 − 2 · 1.414213562374      = 0.313165560052
    difference                              = 0.0098164884340…  > 9816488/1000000000  ✓

so the bracket narrows to `9816488/1000000000 < optimum < 9816533/1000000000`,
width `4.5e-8`. Keep both literals consistent: the `optimum_gt` literal, the
`optimality_gap_lt` literal (`47/1000000000`) and the docstring numbers must all
match whichever branch you shipped.

If any stage of P2 misbehaves, revert `lambda` to `313165471/1000000000` and
`optimum_gt` to `9816471/1000000000` and ship P0+P1. Record the measured margin
in `Experience.md` either way.

### 6. P3 (optional, last) — the secondary depth-10 frontier

Never declared in four sprints, costs no new mathematics, and is the finite-`n`
shadow of the same sandwich that proves optimality: at a frozen depth,
`deficit_scaled_le` and `deficit_scaled_ge` pin `4 ^ 10 (π − polygonLower 10)`
between two rationals `2.2e-8` apart.

```lean
def kappaDepth10  : ℝ := 32298206/100000000
def lambdaDepth10 : ℝ := 322982021/1000000000     -- 322982038/1000000000 if P2 landed
theorem polygon_pi_depth10_search :
    ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10
```

The upper conjunct is the main contract's at `n = 10`. The lower conjunct is
`deficit_scaled_ge 10` plus

    π ^ 3 / 96                ≥ 322982031299/1000000000000     from pi_ge_round_five
                              ≥ 322982048486/1000000000000     from pi_ge_depth_three (P2)
    π ^ 5 / (30720 * 4 ^ 10)  ≤ 9500103/1000000000000000       from π ≤ 3.1415927

giving `4 ^ 10 (π − polygonLower 10) ≥ 0.322982021798897` (resp.
`0.322982038985897`), both strictly above the chosen literal (margins `7.99e-10`
and `9.86e-10`). Width coefficient `3.9e-8` (resp. `2.2e-8`), i.e. a reported
depth-10 interval of width `3.7e-14` (resp. `2.0e-14`) — against the main
frontier's `9.36e-9`. The evaluator logs this as `score_secondary` and it is
**never** a substitute for the main contract; declaring it must not change
`kappa`, `lambda`, or `polygon_pi_constant_search`.

Names are fixed by `lemma.toml` and must be exactly `kappaDepth10`,
`lambdaDepth10`, `polygon_pi_depth10_search`, each `def` on a single line.

## Acceptance criteria

- [ ] `Candidates/V5.lean` declares `def kappa : ℝ := <literal>` and
      `def lambda : ℝ := <literal>` on single lines, with
      `kappa ≤ 32298206/100000000` and `lambda ≥ 313165471/1000000000`
      _(i.e. never worse than the parent; equality is acceptable)_
- [ ] `Candidates/V5/Optimality.lean` contains `admissible_kappa_ge` proving
      `ValidPolygonBound lam kap → Real.pi ^ 3 / 96 ≤ kap`, quantified over
      arbitrary `lam kap : ℝ`, with **no numeric bound on `π` anywhere in its
      proof** (it is a symbolic statement; if a decimal literal appears in that
      proof, something has gone wrong)
- [ ] it also contains `admissible_lambda_lt` and
      `admissible_score_gt_rat : ValidPolygonBound lam kap →
      (9816471/1000000000 : ℝ) < kap - lam` (or the P2-sharpened literal)
- [ ] it contains `valid_of_bracket`, and `V5.lean`'s
      `polygon_pi_constant_search` is proved **through** it rather than by
      repeating `V4`'s inline argument
- [ ] `V5.lean` states `optimum_bracket` (or an equivalent pair of theorems)
      sandwiching `Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2)` between the
      certified rational floor and `kappa - lambda`
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V5` succeeds
- [ ] the evaluator passes all twelve stages with `--no-log`
- [ ] axiom closure is exactly a subset of `{propext, Classical.choice, Quot.sound}`
- [ ] `score ≤ 9816589/1000000000` — **strict improvement is not required**; a
      score-identical `V5` carrying the certificate is a PASS
- [ ] optional (P2): `lambda = 313165527/1000000000`, score `9816533/1000000000`
- [ ] optional (P3): `polygon_pi_depth10_search` type-checks against
      `ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10`
- [ ] `Experience.md` records, for whichever of P2/P3 was attempted, the
      measured margins, and — if `exists_nat_gt` or `one_le_pow₀` did not
      resolve — the name that replaced it

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V5

env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V5.lean --no-log
```

Worth `#check`ing in a scratch file before writing §2, since the whole sprint
rests on them and neither has been used in this workspace before:

```lean
#check @exists_nat_gt
#check @one_le_pow₀
```

No new Mathlib import is expected. If you add one:

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  <module> --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi
```

## Notes / expected obstructions

- **Read first:** `Experience.md` sprint 004 in full (the margin table, the
  `series_succ`-by-`rfl` trick, and the warning that `norm_num` will fire the
  `sqrtTwoAddSeries` simp set if you let it), then sprint 003's digit-budget
  section if you attempt P2.
- **The likeliest failure in P0 is the Archimedean step**, not the analysis.
  Everything else in §2 is `linarith` over cleared denominators. If
  `exists_nat_gt` does not resolve, do not improvise a limit argument through
  `Filter.Tendsto` — search for the Archimedean lemma with at least two tools,
  and as a last resort prove `∃ n : ℕ, x < 4 ^ n` directly from
  `Nat.ceil`/`Nat.floor` API or from `Archimedean.arch`.
- **Keep `admissible_kappa_ge` symbolic.** The temptation is to substitute a
  numeric bound on `π ^ 5` to make `nlinarith` happier. Resist it: the theorem is
  strictly stronger without one, and every quantity in the argument cancels.
- **Division discipline.** `lt_div_iff₀` and `div_lt_iff₀'` both resolve
  (sprints 001/002); `div_le_div_iff` and `mul_lt_mul_left` do not. `le_or_lt`
  does not exist — use `le_or_gt`.
- **Namespace hygiene when copying.** All five derived files and the candidate
  share the namespace `…Candidates.V5`, so each name may be defined once.
  `polygonLower_zero_eq` currently lives in `V4.lean`; if you move it into
  `Optimality.lean`, do not also leave a copy in `V5.lean`.
- **`certified_polygon_interval` must still apply** (evaluator stage 7). Adding
  theorems cannot break that, but changing the name or type of
  `polygon_pi_constant_search` would.
- **Do not attempt the septic rung, the sextic cosine rung, or a `Filter`-level
  limit.** All three are named in "Alternatives considered" as out of scope, and
  each is a plausible-looking way to lose the session.

## Honesty about the rung type, and what this closes

Declared `infrastructure` because the required deliverable moves no constant of
the incumbent's chain and, by construction, cannot move the score: it proves a
statement *about* the score. That said, it is not bookkeeping. The converse
direction is new mathematics for this workspace — the first argument here that
is false at every finite depth and true only in the limit — and it consumes
`V3`'s `deficit_ge` in a way no sprint has: as an asymptotic statement rather
than as a bootstrap input.

The tradeoff the planner is making, stated plainly so the next reader can
disagree with it: this sprint leaves up to `6.9e-8` of score on the table
(`1.2e-8` of it permanently, since `kappa` cannot reach its floor), in exchange
for a proof that `6.9e-8` is *all* that was ever on the table. Given that the
run's four previous sprints already moved the score by five orders of magnitude,
and that every remaining sprint on either side is a rational re-certification
through machinery that already exists, the certificate is worth more than the
digits. P2 exists so that a generator with session budget left over can take the
digits too, and it is gated so that it cannot cost the certificate.

After this sprint the workspace can state, with a machine-checked proof and no
prose:

    9816471/1000000000  <  inf { kappa − lambda : ValidPolygonBound lambda kappa }
                        ≤  9816589/1000000000  =  the shipped score,

with the infimum itself equal to `π ^ 3 / 96 − (π − 2√2)` and approached but not
attained. There is no sprint after this one that is not a digit.
