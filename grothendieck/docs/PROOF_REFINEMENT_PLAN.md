# ProofRefinement: Migrating Lemma 5.4 Seed to the LeanProof/ Proof

## 1. Background

The project has three Lemma 5.4 artifacts, each with a different `C_r`
formula and a different relationship to "effectivity":

| Artifact | `C_r` formula | Where | Effective? |
|---|---|---|---|
| Braverman paper | `8·M²·R/(1−r)² · (1 + 16·R/(1−r)³)` | [assets/pdf/braverman.pdf](../assets/pdf/braverman.pdf) (eq. just below (76)) | Yes in concept (closed-form in `M`, `R`); `M`, `R` themselves come from compactness arguments and are not effective in the paper. |
| Banach-FPT proof in Lean | `2·Bcos²·(B₁·Bdiff + B_H0′) + 2·Bcos·C_R + 1`, with `C_R = 16·L₂·Bcos²·B₁²` | [LeanProof/Lemma54.lean:217](../LeanProof/Lemma54.lean#L217) | **No** — see §3 |
| ProofRefinement seed `v0` | `2·Bcos²·B₁·Bdiff + 2·Bcos·C_R` (no `B_H0′`, no `+1`) | [ProofRefinement/Lemma54/Lemma54_proof_v0.lean:86](../ProofRefinement/Lemma54/Lemma54_proof_v0.lean#L86) | Yes — all 6 bounds are concrete rationals certified by the Python Arb oracle. |
| Arb pipeline (separate) | Braverman's formula (Cauchy/Rouché) | [grothendieck/proof/certified/compute_cr.py:141](../grothendieck/proof/certified/compute_cr.py#L141) | Yes — Arb ball arithmetic. |

The **separate Arb pipeline** in `grothendieck/proof/certified/` is not
in scope here; it certifies a different formula. The relevant oracle for
ProofRefinement is the Banach-FPT-aligned one at
[ProofRefinement/Lemma54/oracle/](../ProofRefinement/Lemma54/oracle/).

The user's directive: **the seed candidate (`v0`) should mirror the
LeanProof/Lemma54.lean proof, not the tightened variant currently in `v0`.**
This makes the evolutionary starting point a less-optimized proof, leaving
the agent more room to improve.

## 2. Why the seed currently differs

`v0` was written as a tightened rewrite of `LeanProof/Lemma54.lean`. Two
deliberate optimizations were folded into the seed:

1. **Eliminated `B_H0′`** — the bound `‖H₀′(sin z′)‖ ≤ B_H0′`. The
   LeanProof proof uses it inside Term-1 of the error decomposition; `v0`
   restructures the algebra so that the `B_H0′` factor cancels into
   `Bcos` (since `Bcos · B_H0′ ≥ ‖cos z‖ · ‖H₀′(sin z)‖ = 1` on `S`).
2. **Dropped the `+ 1`** in the `Cr` definition. LeanProof adds `+ 1` to
   keep `Cr` strictly positive without case analysis; `v0` proves
   positivity directly from the rational values.

Both are legitimate refinements — exactly the kind of change the
evolutionary agent is supposed to *discover*, not start with.

## 3. Effectivity audit of LeanProof/Lemma54.lean

`lemma_5_4` ([LeanProof/Lemma54.lean:41](../LeanProof/Lemma54.lean#L41))
returns `∃ Cr pr, …`. The `Cr` and `pr` it produces are **not closed
form**. Specifically:

- **`B₁, Bcos, Bdiff, B_H0′`** (lines ~67–137) are extracted by
  `IsCompact.exists_bound_of_continuousOn` and `H_eta_bounded_on_compact`.
  These are pure existentials — no rate, no formula in `r` or `η`.
- **`σ`** ([line 141](../LeanProof/Lemma54.lean#L141)) is
  `|Re(sin z₀)|` for `z₀` an unspecified maximizer. Existential.
- **`M_sin`** ([line 156](../LeanProof/Lemma54.lean#L156)) — same.
- **`L₂`** ([line 201](../LeanProof/Lemma54.lean#L201)) — `‖H₀″‖ + ‖H_η″‖`
  bound from `exists_bound_of_continuousOn` on `K₂`. Existential.
- **`pr₀`** comes from `lemma_5_3` ([line 52](../LeanProof/Lemma54.lean#L52)),
  which is itself an existential threshold (Rouché argument; see Braverman
  Lemma 5.3 on PDF page 21).
- **`p₃`** comes from `F_p_deriv_ne_zero_small_p` ([line 60](../LeanProof/Lemma54.lean#L60)),
  again existential.

So the proof body is *structurally* the Banach-FPT contraction argument,
but the constants flowing in are 8 abstract reals. The `Cr` it returns is
a closed-form *expression* in those abstract reals. **Verdict: not
effective as written, but effectivable** — every `obtain ⟨B, hB⟩ := …`
can be replaced by a parameter (rational) plus a hypothesis (axiom).

The proof body itself uses no inherently non-constructive step beyond
those constant extractions (`Convex.norm_image_sub_le_of_norm_deriv_le`,
`ContractingWith.exists_fixedPoint'`, MVT — all fine for effectivity in
the sense we need).

## 4. Lean's role: what we can and cannot prove there

Lean is the *consumer* of certified rationals; it cannot perform the
high-precision interval arithmetic itself. The split is:

- **Python (Arb)** computes rigorous upper-bound rationals for `B₁`,
  `Bcos`, `Bdiff`, `B_H0′`, `σ`, `M_sin`, `L₂`. This is what
  [ProofRefinement/Lemma54/oracle/](../ProofRefinement/Lemma54/oracle/)
  already does for 6 of the 7 (everything except `B_H0′`).
- **Lean** axiomatizes those rationals as upper bounds on the actual
  analytic quantities, then runs the structural proof (Banach FPT) over
  them.

The two non-arithmetic existentials — `pr₀` from Lemma 5.3 and `p₃` from
Lemma 5.3-style derivative non-vanishing — are kept as Lean-side
existentials (their `.choose`); they affect `pr` but not `Cr`, so the
*score* the agent optimizes is unaffected by their non-effectivity.

## 5. Migration plan

### 5.1 Architectural choice

Two viable shapes:

**Option A — Restore parameterization.** Reintroduce a
`Lemma54_Explicit.lean` (the file the legacy bridge once imported) that
holds a `Lemma54Data` structure and a `lemma_5_4_local` parameterized
over it. Refactor `LeanProof/Lemma54.lean` to derive `lemma_5_4` by
discharging the structure with the existential bounds. Then `v0` calls
`lemma_5_4_local` with a structure populated from oracle axioms.

- Pro: separation of concerns, structural proof not duplicated.
- Con: the agent can't evolve the proof body (it lives behind a stable
  API), only the constants. That contradicts ProofRefinement's
  "proof-space search" architecture (see
  [ProofRefinement/Lemma54/README.md:35](../ProofRefinement/Lemma54/README.md#L35)).

**Option B — Inline the LeanProof proof verbatim into `v0`.** Copy the
proof body from `LeanProof/Lemma54.lean` into a new
`Lemma54_proof_v0.lean`. Replace each `obtain ⟨B, hB⟩ := …` for a
constant with `def B_val := <rational>` plus `axiom hB : … ≤ B_val`. Keep
the original `Cr` formula (with `B_H0′` and `+ 1`).

- Pro: matches the existing "one file is the evolutionary unit" model;
  the agent can edit any line of the contraction argument; preserves the
  current `evaluate.py` pipeline structure.
- Con: ~600 lines of proof live in a candidate file (already true of
  `v0` today, ~565 lines).

**Recommendation: Option B.** It is consistent with the existing
ProofRefinement architecture, requires no changes to
`LeanProof/Lemma54.lean`, and lets the agent rediscover the
optimizations (`B_H0′` elimination, `+ 1` removal) that are currently
hard-coded into the seed.

### 5.2 Concrete steps

1. **Verify imports work.** The current `v0` imports
   `LeanProof.Lemma54_Proof_Search_ClaudeCode2.SearchConfig`,
   `LeanProof.Lemma54_Explicit`, and `LeanProof.Lemma54_Cauchy` — none of
   which exist in the present `LeanProof/` tree. Before any rewrite, run
   `lake build` against `ProofRefinement/Lemma54/Lemma54_proof_v0.lean`
   to confirm what compiles. *Likely outcome: it does not compile.* This
   is step 0; we cannot evolve a proof we cannot build.

2. **Decide on the import surface.** The replacement seed needs only:
   - `Defs` from `LeanProof` (sets `S`, `disk`, `H0`, `H_eta`, `F_p`, `K2`).
   - The two infrastructure lemmas: `lemma_5_3` and
     `F_p_deriv_ne_zero_small_p` (in `LeanProof/Lemma53.lean`).
   - Mathlib: `MeanValue`, `Contracting`, `Cauchy`-style estimates if
     the proof uses them.

   Concretely: `import LeanProof.Lemma53` should pull in everything the
   LeanProof proof body needs. Keep `SearchConfig.lean` as the locked
   `(η = 1/100, r = 23/25)` file.

3. **Add `B_H0′` to the oracle.** Add a 7th certifier in
   [ProofRefinement/Lemma54/oracle/certify_bounds.py](../ProofRefinement/Lemma54/oracle/certify_bounds.py)
   and [oracle/certify_lemma54.py](../ProofRefinement/Lemma54/oracle/certify_lemma54.py):
   - **Quantity:** `‖H₀′(sin z′)‖` for `z′ ∈ disk(r)`.
   - **Identity:** `H₀′(w) = 1/√(1 − w²)` (Lemma 4.3 in the paper).
   - **Strategy:** bound `|1/√(1 − w²)|` for `w ∈ sin(closedBall(0, r))`.
     Since `‖sin z‖ ≤ M_sin = sinh(r)` and `|Re(sin z)| ≤ σ`, the worst
     case is `w` real with `|w| = σ`, giving `B_H0′ ≤ 1/√(1 − σ²)`. (Verify
     this is actually the worst case over the Arb-certified `K₂`; if
     not, fall back to a uniform bound on `sin(closedBall(0, r))` via
     Arb interval evaluation of `1/√(1 − w²)`.)

4. **Write the new `Lemma54_proof_v0.lean`:**
   - Section 1: `def B1_val, Bcos_val, Bdiff_val, BH0_val, sigma_val, Msin_val, L2_val`
     (7 rationals from the oracle).
   - Section 2: `norm_num` positivity lemmas for each.
   - Section 3: 7 axioms — one per bound. The `BH0` axiom statement:
     ```
     axiom hBH0_bound :
       ∀ z ∈ disk SearchConfig.r, ‖deriv H0 (Complex.sin z)‖ ≤ BH0_val
     ```
   - Section 4: `def C_R_val := 16 * L2_val * Bcos_val^2 * B1_val^2`
     and **`def Cr_val := 2 * Bcos_val^2 * (B1_val * Bdiff_val + BH0_val) + 2 * Bcos_val * C_R_val + 1`**.
   - Sections 5–11: copy the proof body from `LeanProof/Lemma54.lean:209–681`
     with mechanical substitutions:
     - `B₁ ↦ B1_val`, `Bcos ↦ Bcos_val`, `Bdiff ↦ Bdiff_val`,
       `B_H0' ↦ BH0_val`, `σ ↦ sigma_val`, `M_sin ↦ Msin_val`,
       `L₂ ↦ L2_val`.
     - Each `hB_…_bound` (a hypothesis in the original) becomes a direct
       use of the corresponding axiom.
     - `pr₀, p₃` remain as `.choose` of the existentials (matching the
       current `v0` `p3_val` pattern).

5. **Update `evaluate.py` axiom registry.** In
   [ProofRefinement/Lemma54/evaluate.py](../ProofRefinement/Lemma54/evaluate.py)
   the `AXIOM_REGISTRY` must learn about `hBH0_bound`:
   - Expected statement regex.
   - Exact Lean type for type-ascription check.
   - Oracle function: `certify_BH0_bound`.
   - Bound field: `BH0_val`.
   Update the `Cr` recomputation to use the new formula.

6. **Recompute the seed score.** Run
   `python evaluate.py --file Lemma54_proof_v0.lean`. The new score will
   be **higher (worse)** than the current `v0`'s ~14.3 because of the
   `B_H0′` term and `+ 1`. That is intentional — the agent's first wins
   should be:
   - Realize `Bcos · B_H0′ ≥ 1` is forced, so the `B_H0′` term can be
     replaced by `1/Bcos`, recovering the `B₁·Bdiff` form.
   - Realize the `+ 1` is just a positivity convenience; with concrete
     rationals, positivity is `norm_num`.

7. **Smoke-test the evolutionary loop.** Run a single Shinka iteration
   on the new seed to confirm the agent can edit and re-evaluate. The
   existing `evaluate.py` pipeline does compile + axiom audit + oracle
   verify + score, so no infrastructure changes beyond §5.5 above.

### 5.3 Files to add / change / leave alone

| Path | Action |
|---|---|
| `ProofRefinement/Lemma54/Lemma54_proof_v0.lean` | **Rewrite** to mirror LeanProof's `Cr` formula; 7 axioms. |
| `ProofRefinement/Lemma54/oracle/certify_bounds.py` | **Add** `certify_BH0_bound`. |
| `ProofRefinement/Lemma54/oracle/certify_lemma54.py` | **Add** call site for `BH0`. |
| `ProofRefinement/Lemma54/oracle/types.py` | **Add** `BH0` field to `Lemma54OracleOutput`. |
| `ProofRefinement/Lemma54/evaluate.py` | **Add** `hBH0_bound` to `AXIOM_REGISTRY`; update `Cr` recompute. |
| `ProofRefinement/Lemma54/README.md` | **Update** axiom table (6 → 7) and `Cr` formula. |
| `ProofRefinement/Lemma54/SearchConfig.lean` | **Leave alone.** |
| `ProofRefinement/Lemma54/legacy/` | **Leave alone** (already `#exit`'d). |
| `LeanProof/Lemma54.lean` | **Leave alone** for now. (See §6 if we ever want a parameterized version.) |
| `LeanProof.lean` | **No change** unless we decide ProofRefinement should be a built target. |

## 6. Effectivity work *not* required for this migration

The user asked whether the LeanProof/ proof is effective. Strictly: no.
But for ProofRefinement we don't need to fix that. The migration replaces
the abstract constants with axioms, which gives an effective `Cr` *for
the seed*. The non-constructive `pr₀` and `p₃` remain non-effective; that
is fine because the **score** is `Cr_val`, which is purely numeric.

If, downstream, we want a fully effective Lemma 5.4 with an effective
`pr` too, we'd need to:

- Replace `lemma_5_3` with an effective version (Rouché with explicit
  `m`, `M`, hence explicit `pr = m/(2M)`). The Arb pipeline at
  [grothendieck/proof/certified/certify_invertibility.py](../grothendieck/proof/certified/certify_invertibility.py)
  already does this computation; what's missing is a Lean-side proof
  that consumes the certified `m`, `M`.
- Replace `F_p_deriv_ne_zero_small_p` with an effective threshold from
  `‖H₀′‖`-lower-bound minus `p · ‖H_η′ − H₀′‖`-upper-bound > 0.

This is **out of scope** for the seed migration. Flag it as a separate
follow-up if desired.

## 7. Risks and open questions

1. **Does the v0 file compile today?** The imports
   `LeanProof.Lemma54_Proof_Search_ClaudeCode2.SearchConfig`,
   `LeanProof.Lemma54_Explicit`, `LeanProof.Lemma54_Cauchy` look stale.
   Step 1 of §5.2 must confirm or deny this. If the file is already
   broken, we are not "regressing" a working baseline — we are restoring
   a working seed for the first time.

2. **Is the `B_H0′` bound `1/√(1 − σ²)` the right formula?** The Lean
   axiom needs `‖H₀′(sin z′)‖ ≤ B_H0′` for `z′ ∈ disk(r)`. The
   *worst-case* point on `sin(disk(r))` is not necessarily real. We need
   the oracle to bound `|1/√(1 − w²)|` over a complex region, not just a
   real interval. The simplest rigorous answer: bound on
   `closedBall(0, M_sin) ∩ {|Re| ≤ σ}` via Arb interval evaluation.

3. **Score regression.** The new seed will score worse than the existing
   `v0` (we are stepping back). Confirm with the user that this is
   expected before overwriting `v0`. Alternative: name the new file
   `Lemma54_proof_v0_canonical.lean` and keep the tightened version as a
   reference candidate (e.g. `candidate_v_tight.lean`) so the search has
   a known-good upper bound.

4. **`evaluate.py` regex strictness.** The axiom registry uses tight
   regexes for statement matching. Adding `B_H0′` requires careful
   regex authorship; off-by-one parens or whitespace will reject the
   axiom as "unrecognized" (a critical failure). Test by running the
   evaluator on the *current* `v0` first (sanity check) and only then on
   the new file.

## 8. Suggested order of operations

1. Confirm `v0` compile status (`lake build ...Lemma54_proof_v0`).
2. Add `certify_BH0_bound` to the Python oracle; smoke-test it.
3. Write `Lemma54_proof_v0_canonical.lean` (don't overwrite `v0` yet).
4. Update `evaluate.py` `AXIOM_REGISTRY` with the new axiom.
5. Run the evaluator; confirm 7 axioms verified, new (looser) `Cr_val`
   computed.
6. Decide with the user: replace `v0` outright, or keep both files as
   "easy seed" and "hard seed".
7. Adjust the `README.md` to document whichever choice is made.
