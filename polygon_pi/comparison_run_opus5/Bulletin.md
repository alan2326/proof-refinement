# Bulletin — Polygon-π refinement

Volatile. The planner reads this first. The human edits the priority block; the
sprint driver appends one line per sprint.

## Frontier

| | value |
|---|---|
| incumbent candidate | `Candidates/V5.lean` |
| incumbent `kappa` | `32298206/100000000` |
| incumbent `lambda` | `313165527/1000000000` |
| incumbent score (`kappa - lambda`, minimize) | `9816533/1000000000 = 0.009816533` |
| reported interval width at depth 10 | `9.361775e-09` |
| axiom closure | `{propext, Classical.choice, Quot.sound}` |
| sprints run | 5 |

## Standing priority directive (human-maintained)

1. **Prefer architectural rungs over precision pushes.** A sprint that
   introduces a genuinely new analytic ingredient is worth more than one that
   moves a digit. Every contract must declare `Rung type:
   architectural | precision | infrastructure`, and a `precision` sprint must
   justify itself against the last `architectural` one in its Rationale.

2. **Interrogate every constant in the current chain, not just the obvious one.**
   The baseline's upper bound is a product of several separately-replaceable
   factors. If you have been attacking the same factor for two sprints, attack a
   different one.

3. **Keep both sides moving.** The score is `kappa - lambda`. The `lambda` side
   starts at `0` and is completely unexplored, but it is not a free lunch either
   — do not let the run become one-sided in either direction. `frontier.csv`
   records a `side` column and a one-sided run will be obvious in the report.

4. **A failed sprint with a precise obstruction note is a useful sprint.** Write
   what you tried into `Experience.md` so the next planner can attack the same
   goal from a different angle instead of repeating yours.

## Sprint log

_(one line per sprint, appended by the driver skill)_

| sprint | slug | rung | side | outcome | score | what changed |
|---|---|---|---|---|---|---|
| 001 | deficit_monotonicity_lambda | architectural | lower | PASS | 71/100 | Proved `4^n(π − P_n)` is monotone in `n`, so the lower conjunct binds only at `n = 0`. Lower side is now analytically closed — its exact ceiling is `π − 2√2 = 0.31317`, and every future lower sprint is one rational certification, no new analysis. `lambda` 0 → 29/100. |
| 002 | cubic_deficit_pi_bootstrap | architectural | upper | PASS | 0.0329947 | Sharp global cubic `x − sin x ≤ x³/6` with no domain hypothesis, so `4ⁿ(π − P_n) ≤ π³/96` uniformly. Then made the theorem its own π-bound generator and iterated 5 rounds from `pi_le_four` at fixed depth 2. `kappa` 1 → 0.3229947, within 1.25e-5 of the analytic floor `π³/96`. |
| 003 | quintic_lower_deficit_bootstrap | architectural | lower | PASS | 0.0098297 | Quintic lower deficit `sin x ≤ x − x³/6 + x⁵/120`, giving a companion to `deficit_le` in the other direction, then five bootstrap rounds to `π ≥ 3.141592597`. `lambda` 0.29 → 0.313165, within 5.3e-7 of the ceiling `π − 2√2`. |
| 004 | cosine_anchor_pi_inversion | architectural | both | PASS | 0.009816589 | Replaced the depth-2 *deficit* route to a numeric `π` with a **cosine anchor**: `cos (π/2^(k+1)) = s_k/2` at `k = 5`, certified through a five-stage `+`-nested radical at 12 dp (errors *contract* on `2 + ·`, unlike the `2 - ·` chain), then inverted through `V3`'s already-proved global quartic in **one** step — no bootstrap. `π ≤ 3.1415926848`, `kappa` 0.3229947 → 0.32298206, now `1.6e-9` above the permanent floor `π³/96`. `lambda` 0.313165 → 0.313165471 for free from `V3`'s own lemmas. Score is `7.0e-8` from the theoretical optimum. |
| 005 | optimality_certificate | infrastructure | both | PASS | 0.009816533 | Proved the **converse** of the contract: any valid `(lam, kap)` must have `pi^3/96 <= kap` and `lam < pi - 2*sqrt 2`, so the benchmark's own optimum is now a Lean theorem rather than prose. Pins the true optimum to a window of width `4.5e-8` and proves no candidate can ever score below `0.009816488`. Also landed a depth-3 lower anchor and the first depth-10 secondary contract. |
