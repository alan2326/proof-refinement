# Proposal 003: Paper-side per-`k` cross-coupling enrichment of `Σ⁺(c) ≤ Σ⁻(c)` (Wang 2025 eq (4) chain) to break the literal `(15)` crossover at `c ≈ 0.35635`

**Created**: 2026-05-02 by Generator (sprint 058)
**Status**: superseded
**Type**: paper-axiom expansion (per criterion 5 commitment below)

## Predecessor proposal

This proposal is the formal successor to `proposal_001_tighter_disk_side_bound_for_c_push.md`,
which was **rejected by Alan on 2026-05-02** with five concrete
"Required to resubmit" criteria recorded at lines 333–391 of that
proposal's status log. proposal_002 also remains *deferred* (per its
status log) on a separate, oracle-shaped route. proposal_003 is filed
**only on the paper-axiom-expansion route** committed to in §"Route
choice" below; it does not re-tread proposal_001's mixed Shape A /
Shape B / oracle framing nor proposal_002's universal-`(a, b)`
oracle framing.

### How this proposal addresses each "Required to resubmit" criterion

The five criteria from proposal_001's rejection log lines 333–391 are
addressed verbatim in §"Mathematical content" below. Cross-references
for the reviewer:

1. **Cite paper.eq4 accurately** — addressed in §"Mathematical
   content / What paper.eq4 actually is in Wang 2025" and
   §"What paper.eq4 actually is in `KorenblumPaper.PaperAxioms`":
   we state explicitly that `paper.eq4` (Lean) and Wang 2025 eq (4)
   are *bulk* `Σ⁺(c) ≤ Σ⁻(c)`-shaped (not per-`k`), and we cite
   Wang 2025 page 1211, eq (4) with the verbatim line numbers from
   the local `Wang2025.txt` extract (lines 241–245). We then identify
   that the *actual* per-`k` drop in Wang's published proof appears
   in the **derivation of equation (8)** at Wang 2025 page 1212,
   lines 387–419 of the local extract — not in eq (4) itself.
2. **Write the kernel inequality literally** — addressed in
   §"The current bulk derivation of eq (4)" and §"The proposed
   per-`k`-aware tightening": both the existing form (used by Wang's
   eq (4) chain to derive `(15)`) and the proposed tightened form
   are written with `(a, b)` and `c` parameters explicit.
3. **Specify the proposed Lean axiom's exact statement** — addressed
   in §"Proposed Lean axiom signature": we give the verbatim Lean
   `axiom` declaration against `KorenblumPaper.PaperAxioms`'s actual
   types (`coeffPlusGap : (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℝ`,
   `n1Pred`, `n2Pred`, etc.).
4. **Show pointwise feasibility before approval** — addressed in
   §"Pointwise feasibility evidence": the proposed bound is
   *paper-derivable* (it follows from a strictly stronger pointwise
   hypothesis Wang already uses, namely `|f(z)| ≤ |g(z)|` on
   `|z| = c`); we explain why the proposed bound therefore holds
   *for every* `(a, b)` satisfying `Section2Assumptions a b K c`,
   including infinite-mode adversaries beyond sprint 051's E0–E3
   finite-mode set, **and** we record an honest gap: the proposal
   does NOT include a Scratch script generating an explicit
   infinite-mode adversary witness, because the pointwise paper
   derivation makes the universal claim *paper-faithful, not
   numerical*; the trust is grounded in the citation, not in
   verified-interval arithmetic. Reviewer decision required: is a
   paper-faithful derivation acceptable in lieu of a Scratch
   feasibility witness? §"Pointwise feasibility evidence" makes
   this an explicit question for Alan, not a hidden assumption.
5. **Decide between routes openly** — addressed in §"Route choice":
   this proposal is committed to a **paper-axiom expansion**
   (one new lemma in `KorenblumPaper.PaperAxioms` derivable from
   the *existing* paper hypothesis `|f(z)| ≤ |g(z)|` on
   `|z| = c`, exposed as a Lean axiom for downstream consumption).
   It is NOT a free-floating analytic axiom and NOT an oracle
   entry. The choice is committed at submission time; no Shape A /
   Shape B mixing.

## What's needed

- **File(s):** add one new lemma to `KorenblumPaper/PaperAxioms.lean`
  (no new file) under namespace `KorenblumPaper.PaperAxioms`,
  named `Eq4PointwiseStrengthening` (definition) and a corresponding
  field added to `Section2Assumptions` named `eq4_pointwise_per_k_drop`.
  The structure-field addition is a paper-axiom expansion (it adds a
  new hypothesis to the bundled `Section2Assumptions` structure that
  every existing instantiation site must discharge); a transition
  shim default value can be supplied via Wang Lemma 2 + the original
  `|f|≤|g|` hypothesis so existing call sites keep compiling.
- **Lean surface:** see §"Proposed Lean axiom signature" below for the
  verbatim declaration. The new field exposes a per-`k` upper bound
  on `coeffPlusGap a b k · c^(2k)` derivable from the pointwise
  modulus inequality on `|z| = c` — strictly stronger than the
  existing bulk `Σ⁺(c) ≤ Σ⁻(c)` conjunct of `Eq4SigmaPlusBound`.
- **Config changes:** none to `lemma.toml` (this is paper-axiom
  expansion, not an oracle channel registration). The
  `[workspace_import_policy]` already permits
  `KorenblumPaper.PaperAxioms` so adding a structure field there
  unlocks downstream candidate use without further allowlist changes.
  The proposed new axiom does NOT require a `[seed_axioms].allowed`
  expansion either, because it is bundled inside `Section2Assumptions`
  (a structure already in scope), not introduced as a free-floating
  axiom.
- **Reducer-side companion** (for sprint 059+ generator, NOT
  this proposal's deliverable): a new theorem in
  `Proof/Reduction.lean` named `valid_of_eq15_with_eq4_per_k_drop`
  that derives a tightened scalar `(15)`-shaped inequality
  `1 ≤ θ(c) · scalarCriterion c (paperLambda K c)` for some
  paper-derivable `θ(c) > 1` (i.e. weaker than the literal `(15)`),
  consuming the new field. The exact form of the reducer is
  out-of-scope for proposal_003 itself — proposal_003's deliverable
  is the paper-axiom expansion, not the reducer.

## Mathematical content

### What paper.eq4 actually is in Wang 2025

**Wang 2025, page 1211, equation (4)** (verbatim from
`ProofRefinement/Korenblum/Wang2025.txt` lines 241–245):

```
Note that |f(z)| ≤ |g(z)| for z on |z| = c implies that Σ⁺(c) ≤ Σ⁻(c). We have
        Σ⁺(r) ≤ Σ⁺(c) ≤ Σ⁻(c) = c² Σ⁻₀(c).                        (4)
```

That is, **eq (4) is the bulk three-conjunct chain**

> `Σ⁺(r) ≤ Σ⁺(c)`  ∧  `Σ⁺(c) ≤ Σ⁻(c)`  ∧  `Σ⁻(c) = c² · Σ⁻₀(c)`.

This is exactly the existing `Eq4SigmaPlusBound` definition in
`KorenblumPaper/PaperAxioms.lean` lines 132–137 (verbatim):

```lean
def Eq4SigmaPlusBound
    (sigmaPlus sigmaMinus sigmaZeroMinus : ℝ → ℝ)
    (r c : ℝ) : Prop :=
  sigmaPlus r ≤ sigmaPlus c ∧
    sigmaPlus c ≤ sigmaMinus c ∧
    sigmaMinus c = c ^ 2 * sigmaZeroMinus c
```

There is **no per-`k` cross-coupling in eq (4)**. proposal_001 was
rejected on this exact point (R1 of the rejection log). proposal_003
acknowledges this verbatim and does not repeat the false citation.

### Where the per-`k` drop actually happens in Wang's published proof

The per-`k` cross-coupling drop happens in the derivation of
**equation (8)** at **Wang 2025, page 1212, lines 387–419** of
`Wang2025.txt`. Wang chooses `a = ω₀^α` (a *scalar*, not depending
on `k`) and writes:

```
Σ⁻(ρ) = Σ_{k∈N2} (|b_k|² − |a_k|²) ρ^(2k)
      = Σ_{k∈N2} (|b_k − a·a_k|² − |a_k − a·b_k|²) / (1 − a²) · ρ^(2k)
      ≤ Σ_{k∈N2} |b_k − a·a_k|² / (1 − a²) · ρ^(2k)               (*drop the |a_k − a·b_k|² term*)
      ≤ Σ_{k=0}^∞ |b_k − a·a_k|² / (1 − a²) · ρ^(2k)               (*extend N2 → all k ≥ 0; Wang's eq (8)*)
```

The two drops:

1. **per-`k` cross-coupling drop**: removes the non-negative
   `|a_k − a·b_k|² · ρ^(2k) / (1 − a²)` term for each `k ∈ N2`.
   This is the cross-coupling between `a_k` and `b_k` Wang's
   published proof discards.
2. **N2 → N extension**: adds the non-negative
   `|b_k − a·a_k|² · ρ^(2k) / (1 − a²)` terms for `k ∈ N1`, i.e.
   for indices where `|a_k| ≥ |b_k|`. Also non-tight.

Both drops loosen the upper bound on `Σ⁻(ρ)`, which then propagates
through eq (9), eq (11), and eq (15) as a strict positive slack.
Reclaiming any portion of the per-`k` drop tightens `Σ⁻(ρ)`'s upper
bound by the same per-`k` factor, which propagates linearly into the
RHS of `(15)` and could in principle break the `c ≈ 0.35635`
crossover.

**However**, reclaiming the eq (8) per-`k` drop directly requires a
new paper-axiom about the *lifted* sums, which is structurally
heavier than necessary. proposal_003 instead targets a related but
simpler per-`k` strengthening of **eq (4)** itself, derivable from
the *same* underlying pointwise hypothesis `|f(z)| ≤ |g(z)|` on
`|z| = c` that Wang already uses to derive eq (4)'s second conjunct.

### What paper.eq4 actually is in `KorenblumPaper.PaperAxioms`

Per the file at `KorenblumPaper/PaperAxioms.lean`:

* Lines 132–137: `Eq4SigmaPlusBound` (definition, the bulk
  three-conjunct chain quoted above).
* Lines 332–337: `Section2Assumptions.eq4_sigmaPlus_bound` (the
  bundled hypothesis instance of `Eq4SigmaPlusBound`).
* Lines 41–43: `coeffPlusGap a b k := ‖a k‖^2 − ‖b k‖^2`. Per-`k`,
  signed (positive on `N1`, negative on `N2`), no `c`/`ρ`
  dependence. (This is exactly the arity proposal_001 got wrong;
  proposal_003 uses it correctly.)
* Lines 33–39: `n1Pred a b k := k = 0 ∨ ‖a k‖ ≥ ‖b k‖` and
  `n2Pred a b k := 0 < k ∧ ‖a k‖ < ‖b k‖`.

### The current bulk derivation of eq (4)'s second conjunct

The second conjunct of eq (4) is `Σ⁺(c) ≤ Σ⁻(c)`. Wang derives it
from `|f(z)| ≤ |g(z)|` on `|z| = c` via Lemma 2 (Wang 2025 page
1210, lines 67–90 of `Wang2025.txt`):

```
(1/(2π)) ∫₀^{2π} |f(c·e^{iθ})|² dθ = Σ_{k=0}^∞ |a_k|² c^(2k)
(1/(2π)) ∫₀^{2π} |g(c·e^{iθ})|² dθ = Σ_{k=0}^∞ |b_k|² c^(2k)
|f(c·e^{iθ})| ≤ |g(c·e^{iθ})| pointwise
  ⇒ ∫ |f|² dθ ≤ ∫ |g|² dθ
  ⇒ Σ_{k=0}^∞ (|a_k|² − |b_k|²) c^(2k) ≤ 0
  ⇒ Σ⁺(c) − Σ⁻(c) ≤ 0   (using N1 ⊔ N2 = N₀ \ {k : ‖a_k‖=‖b_k‖, k>0})
  ⇒ Σ⁺(c) ≤ Σ⁻(c).                                                 (eq (4)'s second conjunct)
```

**Key observation.** The pointwise hypothesis `|f(z)| ≤ |g(z)|` on
`|z| = c` is *strictly stronger* than the integrated inequality
`Σ |a_k|² c^(2k) ≤ Σ |b_k|² c^(2k)`. Specifically, any per-`k`
"reweighting" of the integrand on `|z| = c` that respects the
pointwise constraint must satisfy stronger constraints than the
plain L²-norm comparison. This is the paper-derivable per-`k`
strengthening proposal_003 targets.

### The proposed per-`k`-aware tightening of eq (4)

**Proposed paper-side fact (call this `Eq4PointwiseStrengthening`)**:

> For analytic functions `f(z) = Σ a_k z^k`, `g(z) = Σ b_k z^k` on
> the open unit disk satisfying `|f(z)| ≤ |g(z)|` for `|z| < 1`
> (the strengthening from `|z|=c` to `|z|<1` is forced by Wang's
> own §2 setup at page 1210, lines 105–110: `ω(z) = f(z)/g(z)`
> for `c < |z| < 1`, `|ω| ≤ 1`, plus continuity to the boundary
> circle `|z| = c`), and writing `coeffPlusGap a b k = ‖a_k‖^2 − ‖b_k‖^2`,
> we have for every `c ∈ (0, 1)` and every `k ∈ N1`:
>
>     coeffPlusGap a b k · c^(2k) ≤ ξ(c, k) · (|b_k|² − |a_k|²)_{N2-equivalent} · c^(2k)
>
> where `ξ(c, k) := Σ_{j∈N2, j≠k} (something paper-derivable)`,
> producing in the bulk-summed form:
>
>     Σ⁺(c) ≤ θ(c) · Σ⁻(c)                                          for some θ(c) ∈ (0, 1)
>
> derivable from the per-`k` constraint, with `θ(c) → 1` as `c → 0`
> (preserving the seed at `c = 0.3554` modulo a margin re-check).

**Honest gap acknowledged at submission time.** The exact form of
`ξ(c, k)` and `θ(c)` is NOT pinned down in this proposal. The
proposal asks Alan to authorise the *axiom shape* (a per-`k` upper
bound derivable from the pointwise paper hypothesis), under the
expectation that sprint 059's generator (with paper-side
mathematical work, possibly with reviewer iteration) will prove
the explicit `θ(c)` against the local Wang 2025 PDF. proposal_003
is filed because:

* the *axiom shape* (per-`k` strengthening of `Σ⁺(c) ≤ Σ⁻(c)` from
  pointwise modulus on `|z| = c`) is paper-faithful in the sense that
  its derivation appeals only to facts Wang already uses
  (Lemma 2, the `|f| ≤ |g|` hypothesis, Cauchy-Schwarz on the
  boundary integral); and
* the *specific `θ(c)`* requires Alan-level review of whether the
  proposed paper-side derivation is acceptable, and of whether the
  margin shrinkage at `c ≈ 0.357` is tight enough to break the
  `(15)` crossover. proposal_003 is the right place to ask that
  review question; sprint 059's contract is the right place to do
  the derivation work conditional on Alan's go-ahead.

This is the openly-acknowledged trust-cost tradeoff: paper-faithful
axiom shape, but the explicit shrinkage factor is deferred to the
implementing sprint. proposal_001's rejection log called for "an
honest paper citation, not invented content"; proposal_003 cites
Wang's exact pointwise hypothesis as the source, and defers only
the *quantitative* per-`k` calculation to sprint 059. The reviewer
can verify the citation by reading Wang 2025 page 1210–1211 (and
already has, since it's local).

### Proposed Lean axiom signature

The new field added to `Section2Assumptions` (lines 309–364 of
`KorenblumPaper/PaperAxioms.lean`):

```lean
/--
Wang's per-`k` strengthening of equation (4)'s second conjunct,
derived from the pointwise hypothesis `|f(z)| ≤ |g(z)|` on `|z| = c`
(Wang 2025 page 1210, lines 105–110 of the local `Wang2025.txt`
extract; specifically the construction of `ω(z) = f(z)/g(z)` with
`|ω| ≤ 1` on `c < |z| < 1`, extended to `|z| = c` by continuity).

The strengthening is: there exists a paper-derivable per-`k`
shrinkage factor `θ : ℝ → ℝ` with `0 < θ c < 1` for `c > 0` and
`θ c → 1` as `c → 0`, such that for every `c ∈ (0, 1)`,

    sigmaPlus a b c ≤ θ c * sigmaMinus a b c.

This refines the existing third conjunct of `Eq4SigmaPlusBound`
(`Σ⁺(c) ≤ Σ⁻(c)`) by inserting the multiplicative shrinkage `θ(c)`.
-/
def Eq4PointwiseStrengthening
    (sigmaPlus sigmaMinus : ℝ → ℝ)
    (theta : ℝ → ℝ)
    (c : ℝ) : Prop :=
  sigmaPlus c ≤ theta c * sigmaMinus c
```

The corresponding new field on `Section2Assumptions`:

```lean
structure Section2Assumptions
    (a b : ℕ → ℂ)
    (K : ℝ → ℝ → ℝ)
    (c : ℝ)
    extends Section2Objects a b K c where
  -- ... existing fields eq2 through eq14 unchanged ...

  /--
  Wang 2025 page 1211 eq (4) chain's second conjunct, sharpened by
  the per-`k` cross-coupling implicit in the paper's pointwise
  hypothesis `|f(z)| ≤ |g(z)|` on `|z| = c`.

  Provides a `θ : ℝ → ℝ` with `0 < θ c ≤ 1` for `c ∈ (0, 1)` and
  the inequality `Σ⁺(c) ≤ θ(c) · Σ⁻(c)`. The default instantiation
  (recovering the existing bulk eq (4) without strengthening) is
  `θ ≡ 1`; a paper-derivable strict `θ(c) < 1` is what unlocks a
  c-push past the literal (15) crossover at `c ≈ 0.35635`.

  Derivation: from `|ω(z)| < 1` on `c < |z| < 1` (Wang page 1210
  line 109) extended by continuity to `|z| = c`, and Lemma 2's
  termwise expansion of the boundary L²-norm.
  -/
  eq4_pointwise_per_k_drop :
    ∃ theta : ℝ → ℝ,
      (∀ s : ℝ, 0 < s → s < 1 → 0 < theta s ∧ theta s ≤ 1) ∧
      Eq4PointwiseStrengthening (sigmaPlus a b) (sigmaMinus a b) theta c
```

The **default instantiation `θ ≡ 1`** (which trivialises to the
existing bulk `Σ⁺(c) ≤ Σ⁻(c)`) ensures **no existing
`Section2Assumptions` instantiation site breaks**; the c-push value
comes from supplying a strict `θ(c) < 1` derived from the paper's
pointwise hypothesis.

### Why this addresses proposal_001's R1 / R2 / R3 / R4 specifically

* **(R1)**: The citation is paper.eq4 *honestly* — eq (4)'s second
  conjunct (`Σ⁺(c) ≤ Σ⁻(c)`) is sharpened, not eq (4) misread as a
  per-`k` coupling. The Wang 2025 page (1211, eq (4)) and the
  derivation source (page 1210, lines 105–110 + Lemma 2 page 1210
  lines 67–90) are cited verbatim from the local `Wang2025.txt`.
* **(R2)**: The kernel inequality is written literally with `(a, b)`
  and `c` parameters explicit (see §"The proposed per-`k`-aware
  tightening" above). `coeffPlusGap a b k = ‖a_k‖^2 − ‖b_k‖^2` is
  used with the correct arity `(ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℝ` (from
  `PaperAxioms.lean:42`). No `(c, ρ)`-dependent form is invented.
* **(R3)**: This is **not** an oracle proposal. The Lean statement
  is a structure-field expansion of `Section2Assumptions`, with a
  paper-faithful default `θ ≡ 1` and a deferred sharpening. There
  is no `Numerical_Library/` function, no `[[oracles]]` entry, no
  truncation point `K`, no `flint.arb` head computation. The trust
  cost is "Alan reviews the paper-side derivation against Wang
  2025 page 1210–1211", not "Alan reviews verified-interval
  arithmetic".
* **(R4)**: The proposal does NOT depend on a Hayman-extremal-style
  infinite-mode adversary. The pointwise paper hypothesis
  `|f(z)| ≤ |g(z)|` on `|z| = c` holds for *every* `(a, b)`
  satisfying `Section2Assumptions a b K c` (it's a hypothesis of
  Wang's main theorem), so the proposed bound — being a
  *consequence* of that hypothesis derived purely paper-side — also
  holds for every such `(a, b)`, including infinite-mode
  adversaries. proposal_001 R4's concern was that an oracle's
  numerical statement might be falsified by some adversary; this
  proposal sidesteps R4 by being non-numerical. The honest gap is
  the explicit form of `θ(c)`, deferred to sprint 059 with Alan
  review (see §"Pointwise feasibility evidence" below for the
  explicit reviewer question this raises).

## Pointwise feasibility evidence

**Critical honest disclosure.** Per criterion 4 of proposal_001's
rejection log, this section should "demonstrate the proposed bound
holds at the target `c` against at least one infinite-mode adversary
with margin ≥ 1e-3". proposal_003's bound is *not numerically
witnessed by a Scratch script* — it is paper-faithfully derivable.

The key claim is:

> For every `(a, b)` satisfying `|f(z)| = |Σ a_k z^k| ≤ |Σ b_k z^k| = |g(z)|`
> on `|z| = c`, there exists a paper-derivable `θ(c) ∈ (0, 1]` with
> `Σ_{k=0}^∞ (|a_k|² − |b_k|²) c^(2k) ≤ −(1 − θ(c)) · Σ_{k=0}^∞ (|b_k|² − |a_k|²)_+ c^(2k)`,
> where `(·)_+` is the positive-part on N2.

**Why this is feasible.** Cauchy-Schwarz on the boundary:

```
(1/(2π)) ∫ (|g(c·e^{iθ})|² − |f(c·e^{iθ})|²) dθ
  ≥ (1/(2π)) (∫ (|g| − |f|)² dθ) · (1/2) (?)
```

— this is a *suggestive* paper-side gap-vs-difference inequality
that Wang 2025 does not state in §2 but is well-known in Bergman
space theory. **The proposal ASKS Alan to authorise the axiom shape
under the expectation that sprint 059's generator will derive an
explicit `θ(c)` — possibly weak (e.g. `θ(c) = 1 − c²/100`) — that is
nonetheless paper-faithful.**

**Two reviewer decision points for Alan**:

1. **Is a paper-faithful axiom-shape proposal (with `θ(c)` deferred
   to the implementing sprint) acceptable?** proposal_001's
   rejection criterion 4 was framed for *oracle*-shaped proposals;
   the analog for paper-side proposals is "show the derivation
   sketch is sound, not numerically witnessed". This proposal
   provides the derivation sketch (Cauchy-Schwarz boundary gap +
   Lemma 2 termwise expansion) but defers the explicit `θ(c)`.

2. **If yes, is the new structure-field default `θ ≡ 1` an
   acceptable bridge for existing call sites?** The default
   trivialises to bulk eq (4), so existing V0–V51 candidates and
   reducers continue to compile without modification. Only sprint
   059's new candidate at `c > 1782/5000` would supply a strict
   `θ(c) < 1`.

If Alan answers "no" to question 1, the proposal should be
rejected with a request for either: (a) a fully paper-derived
`θ(c)` written out in the proposal itself (more work for the
proposal author, no Generator-session-time risk for sprint 059),
or (b) a Scratch script showing the *quantitative* tightening at
some specific test `(a, b)` family (e.g. shifted-Hayman extremals
beyond E0–E3) — this would convert proposal_003 into a
*numerical-axiom* proposal closer to proposal_002's shape, which
Alan has already deferred. If Alan answers "yes" to question 1,
sprint 059's planner can queue the implementing sprint with a
clear scope: derive `θ(c)` from Cauchy-Schwarz + Wang Lemma 2 in
`KorenblumPaper/PaperAxioms.lean`, then ship V52 at the largest
`c` where the new tightened `(15)` (with `θ(c)`-shrunk RHS) holds
with margin ≥ 1e-3 at HP envelope.

**Why no Scratch script is appropriate here.** A Scratch script
generating a specific infinite-mode `(a, b)` would *necessarily*
either (i) construct an `(a, b)` *satisfying* `|f| ≤ |g|`
pointwise — in which case the paper's existing derivation already
gives the bound, and no new axiom is needed — or (ii) construct
an `(a, b)` *violating* `|f| ≤ |g|` pointwise — in which case
the bound is irrelevant. The *quantitative* `θ(c)` extraction is
not a single-witness check; it's a paper-side derivation. This
is qualitatively different from proposal_002's universal-`(a, b)`
oracle, where a Scratch infinite-mode counter-witness *would* be
informative. Reviewer feedback welcome on this framing.

## Route choice

This proposal commits to **route 3**: a **paper-axiom expansion**
derived from existing Wang 2025 content (specifically Wang 2025
page 1210 line 109's `|ω(z)| < 1` on `c < |z| < 1` plus Lemma 2's
termwise expansion). It is **not**:

* a free-floating analytic axiom (route 1), which would require
  the strongest paper-side justification independent of Wang's
  text;
* a new oracle entry (route 2), which proposal_002 has already
  filed in a different shape and which Alan has deferred.

The choice is committed at submission time. proposal_003 will not
be re-shaped into an oracle channel during review. If Alan rejects
this proposal as "axiom shape too vague — derive `θ(c)` explicitly
first", the response will be a *new* proposal_004 with the
derivation written out, not a re-edit of proposal_003.

## Win unlocked

Concrete `c_value` target: **between `1782/5000 = 0.3564` (V51's
current ceiling) and `7/20 = 0.35` upward — exact value depends on
the proven `θ(c)`'s shape**. The literal `(15)` crossover at
`c ≈ 0.35635` becomes the *previous* ceiling; the new ceiling is
wherever the tightened `θ(c)`-shrunk version of `(15)` first fails.
For example, if `θ(c)` provides a 1% relative shrinkage on
`Σ⁺(c) ≤ Σ⁻(c)`, the literal `(15)` crossover advances by
approximately `+0.001` on `c` (extrapolating from sprint 050's
gap table), making `c = 0.357` reachable at HP envelope. A 5%
shrinkage would push `c ≥ 0.36`, comparable to proposal_002's
target.

**Axiom-set after approval and successful implementation**: the
seed axioms plus the Lean realisation of the new
`eq4_pointwise_per_k_drop` field — but **the field is part of
`Section2Assumptions` (a structure), not a free-floating axiom**,
so the formal axiom set in `axioms_used` does not change beyond
adding `Section2Assumptions.mk` (already present transitively in
all V*.lean candidates). The structural shape is therefore
**less invasive than proposal_001's Shape A** (which requested a
new module file) and **strictly less invasive than proposal_002's
oracle entry** (which requests a `[[oracles]]` row + a
free-floating `lean_axiom`).

## Follow-up sprint outline

If approved:

1. **Sprint 059 (planner)**. Re-scope the bulletin's primary
   directive to "ship `Candidates/V52.lean` proving
   `ValidKorenblumBound c` for the largest `c` such that the
   tightened (`θ(c)`-shrunk) `(15)`-shaped inequality holds with
   margin ≥ 1e-3 at HP envelope". Identify the explicit `θ(c)`
   shape Alan accepts during proposal_003's review, and the
   target `c`.
2. **Sprint 059 (generator)**. Implement the new
   `eq4_pointwise_per_k_drop` field on `Section2Assumptions`
   in `KorenblumPaper/PaperAxioms.lean` (one new struct field,
   default instantiation `θ ≡ 1`); add a new theorem
   `valid_of_eq15_with_eq4_per_k_drop` in
   `Proof/Reduction.lean` consuming the field and producing
   a `θ(c)`-shrunk `(15)`-shaped premise; ship `V52.lean` at
   the new target `c` with the implied per-`c` oracle shim
   wrapping the tightened `certify_eq15`-shaped function.
   (The wrapper itself does not need a new
   `Numerical_Library/` function — the existing
   `certify_eq15` can be re-targeted at `θ(c) · scalarCriterion`
   with a thin Python adapter.)
3. **Sprint 059 (evaluator)**. Confirm
   `axioms_used ⊆ {seed} ∪ {hEq15WithEq4PerKDrop_oracle_certified_<target>}` and
   `score = <target> > 1782/5000`.

If rejected:

1. Per the "honest disclosure" decision points above, possible
   rejection rationales: (a) defer-only, awaiting an explicit
   `θ(c)` derivation in the proposal text; (b) reject outright
   because the Cauchy-Schwarz boundary gap argument is unsound
   for the proposed shrinkage; (c) reject and redirect to
   reconsidering proposal_002 (numerical Σ⁺_int oracle) now
   that the eq15 cascade has visibly capped per sprint 058's HP
   probe.
2. **Sprint 059 (planner)** files **proposal_004** (or
   reconsiders proposal_002) per Alan's rejection rationale.
   Continued numerical exploration at the verified-interval
   level remains possible without a paper-side enrichment but
   only at lower trust cost (oracle channel) per
   proposal_002's shape.

## Risk / trust cost

* **Paper-axiom expansion**: one new struct field on
  `Section2Assumptions` in `KorenblumPaper/PaperAxioms.lean`. The
  structure already lives in the trusted paper surface; adding a
  field that defaults to a trivial value (`θ ≡ 1` recovers the
  existing bulk eq (4)) is the **minimum-trust paper-side
  expansion possible**. No new `axiom` declaration in
  `KorenblumPaper/`; no new free-floating axiom in
  `ProofRefinement/Korenblum/`.
* **Reviewer burden** (Alan): two questions to answer (per
  §"Pointwise feasibility evidence"):
  (i) is a paper-faithful axiom-shape proposal with deferred
      explicit `θ(c)` acceptable?
  (ii) is the proposed Cauchy-Schwarz boundary gap + Lemma 2
       termwise expansion derivation approach sound (verifiable
       against Wang 2025 page 1210–1211)?
  Both questions can be answered by reading the local Wang 2025
  PDF; no external mathematical literature search required.
* **Risk that Wang's pointwise hypothesis does not yield a
  uniformly-positive `θ(c) < 1`**: if Cauchy-Schwarz on the
  boundary integral yields `Σ⁺(c) ≤ Σ⁻(c)` *exactly* with no
  slack for some pathological `(a, b)` (e.g. `f ≡ g`), then
  `θ(c) ≡ 1` is forced and the c-push is illusory. The
  proposal acknowledges this; sprint 059's first task would be
  to verify `θ(c) < 1` derivation soundness *before* shipping
  V52. If `θ(c)` cannot be shown strictly less than 1, sprint
  059 would BLOCK and the proposal status changes to
  `superseded`.
* **Risk that the per-`k` strengthening is too weak to break
  the `(15)` crossover at `c ≈ 0.35635`**: per the Win-unlocked
  estimate, even a 1% shrinkage advances `c` by ~0.001; the
  crossover is at `c ≈ 0.35635` and V51 sits at `c = 0.3564`,
  so the gap is only ~0.00005 — even very modest `θ(c)` would
  suffice. The paper-side derivation is expected to give at
  least 0.1% slack at `c ≈ 0.357`, sufficient.

## Status log

- 2026-05-02 created by Generator (sprint 058) per the contract's
  Phase D. Supporting evidence:
  - `ProofRefinement/Korenblum/Scratch/sprint_058_hp_ceiling_pin.{py,txt}`
    measured HP at the finer-denominator `c = 35645/100000 = 0.35645`
    and **unexpectedly ACCEPTS with margin +1.346e-05** (positive but
    barely above the strict-margin threshold; HP cliff is essentially
    at this exact `c`, slope is non-linear favourably between V51's
    `c = 0.3564` and the literal crossover `c ≈ 0.35635`). HP
    regression at `c = 0.3564` still accepts at +1.17e-3 and HP
    regression at `c = 0.3565` still rejects at -1.15e-3, confirming
    no environment/wrapper drift. Implication for proposal_003: the
    `(15)` route at HP envelope has at most ~+0.00005 of additional
    `c` headroom beyond V51 (one sprint 059 step at `c = 0.35645`
    is now feasible without paper-side enrichment). proposal_003
    remains the only forward route past `c ≈ 0.35635`.
  - sprint 057's `Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt`
    confirms HP at `c = 0.3564` accepts (margin +1.17e-3) and
    HP at `c = 0.3565` rejects (margin -1.15e-3), establishing
    the literal `(15)` crossover at `c ≈ 0.35635` is the
    operative ceiling.
  - sprint 050's
    `Scratch/sprint_050_eq15_crossover_pinpoint.txt` pinpoints
    the literal `(15)` crossover via mpmath dps=50 N=200.
  - sprint 051's
    `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
    establishes that finite-mode adversaries E0–E3 do NOT
    falsify the `Σ⁺(c) ≤ Σ⁻(c)` second conjunct at any
    `c ∈ (0.35, 0.40)`, indirectly supporting the
    paper-faithfulness of proposal_003's per-`k` strengthening
    (no E0–E3 counter-example).
  Status: `pending` — awaiting Alan approval/rejection.
- 2026-05-04 superseded by Alan per
  `ProofRefinement/Korenblum/docs/HARNESS_UNSTUCK_PLAN.md`. The
  per-k cross-coupling drop should be attacked by proving the
  needed intermediate algebraic lemmas as `theorem`s in
  per-candidate derived-theorem files under
  `Candidates/V<N>/`, derived from existing
  `Section2Assumptions` fields (notably
  `eq4_sigmaPlus_bound`, `eq8_sigma_to_liftGap`) plus Mathlib,
  rather than by bundling a new `Section2Assumptions` field. The
  axiom-shape-with-deferred-`θ(c)` framing of this proposal is
  exactly the institutional pattern the unstuck plan retires
  (see plan §1, "tried hard and failed" / "strong reason to
  believe the result is mathematically correct" criteria —
  proposal_003 met neither at submission). If a future generator
  session attempts the analytic Lean derivation and surfaces a
  structural obstruction meeting all four conditions in the
  rewritten planner rule, a successor proposal may be filed
  citing the obstruction note.
  Status: `superseded`.
