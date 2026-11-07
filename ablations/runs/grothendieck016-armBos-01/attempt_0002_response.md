act rational arithmetic (`1500681/12500000 ≤ 1/8`), so its margin size is irrelevant to `norm_num`.

**Trust surface.** Unchanged in every respect that matters: `r = 23/25` and `eta = 1/100` untouched, the oracle rectangle `Ω(1635/10000, 1115/1000)` byte-identical to V9–V11, `h_oracle_domain_contains_image` byte-identical, no frozen `Proof/Lib` theorem edited, no new free-floating analytic axiom. The one new axiom is oracle-backed and has the *same statement shape* as the axiom it replaces (`‖iteratedDeriv 2 (F_p η p) w‖ ≤ bound`, over the same domain) — only the certified value it carries is tighter, and the evaluator recomputes that value itself.

**On the success bar.** I did not reach `Cr_val ≤ 1/6400`, and I want to be explicit that this is not a matter of remaining slack in the constants. With the sup-norms taken over the locked rectangle, the first chunk of the second-`p`-derivative bound alone is

```
‖Φ'‖ · ‖Φ‖ · sup‖1/D‖²  ≈  0.0541 · 0.0476 · 2.42  ≈  6.2·10⁻³,
```

i.e. ~40× above `1.5625·10⁻⁴`, and `M_phi ≈ 0.0476`, `M_phi_prime ≈ 0.0541` are certified sups at the locked `η`, while `sup‖1/D‖ ≈ 1.70` is set by the rectangle's corner. Reaching the bar therefore requires either a smaller certified image domain (forbidden here — it would weaken `h_oracle_domain_contains_image`) or a different remainder architecture, not a better constant. Two structural levers I evaluated and rejected for this one-shot, recorded so they aren't re-derived:

- **Joint `DD/D³` oracle** (replacing `M_pp · inv³ = 96` by a pointwise `sup‖DD‖/‖D‖³`). Note `H_0''/(H_0')³ = w` exactly, so at `p = 0` this sup is just `max_Ω|w| ≈ 1.394`; with the `p ∈ [0,1]` perturbation it lands near `(0.370 + sup‖Φ''‖)/(0.589)³ ≈ 10`. That would give `Cr ≈ 0.023` → `Cr_val ≈ 1/32` (~4× beyond what I emitted), but it needs a new `F_inv_p_second_deriv_bound_*` lemma — a ~450-line blind transcription plus a ~180-line wrapper, whose only genuinely new step is
  `‖u_zz‖ = ‖DD‖·‖h‖³ ≤ M_uzz` via `le_of_mul_le_mul_right` against `‖DD‖ ≤ M_uzz·‖D‖³`. Worth a sprint with a compiler in the loop; not worth risking a whole one-shot.
- **Tightening `inv_F_p_z_val` from `2` to `7/4`.** The oracle recomputes ≈1.70, so `7/4` should pass with ~2.6 % headroom and would buy 8×→12×. I left it at `2` because a single mis-estimate there voids the entire attempt for a 1.5× gain.

**If a later attempt builds on this:** the dominant remaining term is `term2 = ½·M_pp·inv³·M_phi² ≈ 0.110` (91 % of the score), and its looseness is now entirely the `inv³ = 8` factor against a true pointwise `≈ 4.9` at the corner where `‖DD‖` is small — which is exactly what the joint `DD/D³` oracle collapses. That is the next real factor of ~4, and after it the score is `M_phi·M_phi_prime·inv² ≈ 0.010`-dominated, at which point the floor argument above binds.