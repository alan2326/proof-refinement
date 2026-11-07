# Sprint 077: Phase 0 mpmath sweep — per-`k` α-varying cross-coupling kernel above `7129/20000`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V59.lean` (high-water-tied; `c_value = 7129/20000 = 0.35645`)
**Target file**: `Candidates/V60.lean` (V59-tied, byte-for-byte axiom envelope identical) plus a new Scratch sweep producing a concrete witness or NO-GO for the per-`k` α-varying kernel
**Direction**: scratch-numerical-witness + section2-proof (Phase 0 sweep gating a future c-push; tying V59 with the **first non-uniform-α sign-positivity probe** in workspace history)

## Goal

Run the **first numerical Phase 0 sweep** of the per-`k`
**α-varying** cross-coupling kernel above the V52 high-water mark
`c = 7129/20000 = 0.35645`. The output is one of:

1. **GO**: a concrete `(c, α : ℕ → ℝ, [E_canonical_extremals])` triple with
   `c > 7129/20000` such that the per-`k` α-varying kernel at α = α(·) is
   non-negative on every canonical extremal `E_j` (`j = 1, 2, 3, 4, 5`)
   and on every linear combination tested, with positive margin
   `≥ 1e-4`. This becomes the witness gating sprint 078's V60+ Lean
   c-push attempt.

2. **NO-GO**: a documented falsifying coefficient adversary `E_*` such
   that for every α(·) family in the sweep grid, the per-`k` kernel at
   `E_*` is negative at every `c > 7129/20000` tested. This becomes
   evidence that the α-varying generalisation does not unblock E1
   saturation, and the next planner pivots to a different chain (Wang
   Lemma 2 / Fourier orthogonality, Wang's `(5)` higher-mode pocket,
   eq-15 oracle's HP-precision push, etc.) **without** a wasted Lean
   attempt sprint.

The candidate-side deliverable is `Candidates/V60.lean`, V59-tied at
`c_value = 7129/20000 = 0.35645` via `valid_of_eq15` discharged by
`hEq15_oracle_certified_hp_35645`. V60's sole purpose at the candidate
level is to **freeze the planner-named "next" target** (per
sprint 076's Experience.md "What would unblock a c-push faster" entry)
into the workspace's structural layer by shipping a **stub
per-candidate derived-theorem file**
`Candidates/V60/PerKAlphaVaryingLiftIdentity.lean` that wraps V54's
existing `lift_identity_per_k` per-index — i.e. the trivial
generalisation step from `α : ℝ` to `α : ℕ → ℝ` — so the next planner
has a Lean-side handle pointing at the right structural location, with
the Phase 0 numerical investigation directly answering whether this
handle has a chance of supporting a real c-push or whether the next
planner should pivot.

**This sprint does NOT attempt a c-push.** The Phase 0 output gates
whether sprint 078 attempts one.

## Why

### The strategic gap

The standing high-water `V52` (`c = 7129/20000`, HP-35645 oracle) has
been tied by `V53–V59` for 7 consecutive sprints, each shipping a
structural advance (5 per-candidate derived-theorem files, 2
reducer/identity additions to `Proof/Reduction.lean`). The Bulletin's
2026-05-02 directive is unambiguous: *"tying V0's c is no longer
acceptable; the success criterion is `c_value > 7129/20000`."* The
harness has shipped seven structural ties and **zero c-pushes** since
that directive. A pivot to genuine c-push attempts is overdue.

The per-`k` α-varying cross-coupling lift identity is the route the
recent bulletin entries, sprints 075/076, and the V58 derived theorems
have repeatedly named as the unblock direction. V58.Theorem 3 makes
the obstruction completely explicit: at uniform α = c, the per-`k`
kernel `(1 − c²)·(annulusExcess − diskExcess)(c) = ∑' k, coeffPlusGap_k
·(1 − 2c^(2k+2))/(k+1)` falsifies on the E1 single-mode adversary
(`b_1 = 1`, all other coefficients zero) because `coeffPlusGap_1 = −1`
and the weight `(1 − 2c⁴)/2 > 0` at `c ≈ 0.36`, giving a negative
per-`k` value. **The α-varying generalisation lets each mode `k` pick
its own α(k), which decouples the per-mode weights and may admit a
non-E1-falsifying configuration.** No one has computed whether such a
configuration exists.

### The kernel under generalisation

V54's per-`k` lift identity reads, at fixed real α and fixed `k`:

  `(1 − α²) · (‖b_k‖² − ‖a_k‖²) = ‖b_k − α·a_k‖² − ‖a_k − α·b_k‖²`.

The α-varying generalisation simply applies this at α = α(k) for each
`k` independently — purely algebraically valid because the identity
holds for *every* real α at *every* index. The Bergman-disk-weighted
integration on `[0, c]` gives the per-`k` disk piece weight
`c^(2k+2)/(k+1)`; on the annulus `[c, 1]`, weight `(1 − c^(2k+2))/(k+1)`.
At α = α(k) per-`k`, the resulting per-`k` representation of
`(annulusExcess − diskExcess)(c)` becomes (schematically; the contract
generator should verify the algebra in the sweep script):

  `annulusExcess(c) − diskExcess(c)
     = ∑' k, [ (‖a_k − α(k)·b_k‖² − ‖b_k − α(k)·a_k‖²) ·
                ((1 − c^(2k+2))/(k+1) − scaling for disk-side)
              + cross-terms involving (1 − α(k)²) ]`.

The exact closed form depends on the specific bookkeeping (whether
α(k) is read off the disk-side lift, the annulus-side lift, or a
weighted combination); the Phase 0 script should derive it cleanly
from V54's `lift_identity_per_k` plus V57.Theorem 1's disk-side
representation plus V58.Theorem 1's annulus-side representation, then
specialise to per-`k` α(k).

The **degree of freedom** is `α : ℕ → ℝ`. The sweep is to identify
whether some α(k) sequence simultaneously:

  - keeps the per-`k` kernel non-negative on **every** canonical
    extremal (E1: `b_1 = 1`; E2: `b_2 = 1`; E3: `b_3 = 1`; E4: `b_4 = 1`;
    E5: `b_5 = 1`), and on small linear combinations
    (`b = e_j + λ·e_k` for `λ ∈ {0.1, 0.5}`, `j ≠ k`);

  - achieves total positive margin `≥ 1e-4` when summed across the
    first `K = 20` modes;

  - works at some `c > 7129/20000` — ideally `c ≥ 0.357` (since V38's
    artifact at `c = 356401/1000000 ≈ 0.356401` is below the V52
    shoulder, the harness needs to clear the whole HP-35645 ceiling
    to claim a real push).

If such an α(·) exists, sprint 078 ships a Lean derivation of the
generalised per-`k` lift identity in `Candidates/V60/`, and a V61 (or
V60+ side lemma) attempts the c-push using that α(·) and the Phase 0
witness as the integral-mass-≥-1 check.

If no such α(·) exists at any tested `c > 7129/20000`, sprint 078
pivots to a different chain. Either way, the Phase 0 output is
load-bearing.

### Why this register is genuinely new

Every prior Phase 0 sweep in `Scratch/` (sprints 048–051, 056–060, 065,
067, 068, 071, 072) tested **uniform-α** kernels — i.e. the same scalar
parameter applies to all modes. The per-`k` α-varying generalisation
introduces a fundamentally different optimisation: instead of finding
one α maximising a worst-case-mode bound, the planner picks α(k) per
mode and the kernel becomes a *sum* of per-mode contributions, each
with its own optimisable parameter. This is the same structural
distinction as moving from a single-window τ-partition (sprint 071) to
a multi-window τ-partition (V38's seven-window certificate): the
extra degrees of freedom can break the worst-case-mode adversary that
saturates the uniform-parameter envelope.

The Bulletin's 2026-05-04 directive update on per-mode reducers makes
this exact point in the structural-window dimension; sprint 077 is
its **per-coefficient-mode α** dual, applied to the disk/annulus
excess balance rather than to the τ-partition. Both registers expand
beyond the closed-form `(a, b)`-independent scalar kernel family the
Bulletin identifies as the harness's structural blind spot.

### Why Phase 0 must precede Lean

The AGENT_BRIEF "Honesty in Experience.md" rule and the Bulletin's
2026-05-02 directive are explicit: every sprint that proposes a
numerical headroom must include a `Scratch/` script confirming the
inequality holds at the proposed `(c, parameters)` with stated margin
**before** any Lean is written. Three of the last five non-tying
attempt sprints (065, 067, 068) falsified on canonical extremals
because no Phase 0 was run; the resulting `BLOCKED` exits cost
≈3–4 generator hours each.

The α-varying generalisation has up to 20 free real parameters (α(0),
α(1), …, α(19)) plus the choice of `c`. The search space is too large
for an unaided Lean attempt to discover a witness; mpmath / SciPy
optimisation is the right tool. **No Lean theorem should be attempted
until Phase 0 either confirms a witness with margin or rules out the
register.**

### Why this is not a proposal

The four-condition guide:

1. **"Tried hard and failed"**: the per-`k` α-varying kernel has
   never been numerically swept in this workspace. The V58.Theorem 3
   E1 falsification is for *uniform* α = c, not α(k); no extension
   has been computed.
2. **"Genuinely large derivation cost"**: the Lean-side derivation,
   if Phase 0 succeeds, is bounded — V54's `lift_identity_per_k`
   already covers the per-index algebra, and the integration weights
   are already built in V57/V58. The follow-up Lean sprint would be
   ≈300 lines, well within capacity.
3. **"Strong reason to believe correct"**: the algebra of the
   α-varying lift is provably valid for every α(·) (it is V54's
   identity per index); only the *sign positivity* of the resulting
   sum on canonical extremals requires numerical witness, which is
   exactly what Phase 0 produces.
4. **"Strong evidence of c improvement"**: this is what Phase 0 is
   computing. The sprint's pre-condition is uncertainty; its output
   resolves the uncertainty either way.

So: attempt-first (numerically), no proposal.

## Read this before starting

1. `ProofRefinement/Korenblum/Candidates/V54/LiftIdentity.lean` — the
   per-index lift identity that the α-varying generalisation
   instantiates (`lift_identity_per_k a b α k` for any real α and any
   k; the α-varying version is `lift_identity_per_k a b (α k) k` — i.e.
   the same theorem applied at α := α(k) for each k separately).
2. `ProofRefinement/Korenblum/Candidates/V57/DiskExcessLiftIntegrated.lean`
   — the integrated lift identity over the disk `[0, c]`, surfacing
   the disk-side polar Jacobian as a hypothesis (now discharged by
   sprint 042's `diskExcess_eq_tsum_via_termwise_integration` in
   `Proof/Reduction.lean`).
3. `ProofRefinement/Korenblum/Candidates/V58/AnnulusExcessLiftIntegrated.lean`
   — the integrated lift identity over the annulus `[c, 1]`, plus
   **Theorem 3** (`annulusMinusDiskExcess_per_k_at_alpha_eq_c`) which
   gives the explicit closed-form per-`k` kernel at uniform α = c:
   `(1 − c²)·(annulusExcess − diskExcess)(c) = ∑' k, coeffPlusGap_k ·
   (1 − 2c^(2k+2))/(k+1)`. This is the kernel the α-varying
   generalisation modifies.
4. `Scratch/sprint_058_hp_ceiling_pin.py` and
   `Scratch/sprint_060_finer_hp_probe_35646_35647_35648.py` — example
   mpmath script structures from prior Phase 0 sweeps; reuse the
   precision conventions (`mp.prec = 200` as a guard against
   floating-point loss near the V52 shoulder) and the canonical
   extremal taxonomy.
5. `Bulletin.md` "Directive update — 2026-05-04" sections — the
   structural framing for why per-mode/per-coefficient registers
   matter.

**Do not modify `KorenblumPaper/`, `Proof/`, `lemma.toml`, or any
existing `Candidates/V<K>.lean` for K ≤ 59.**

**Do not file a proposal.** Phase 0 must complete first, and even
then the four-condition guide says the next move is a Lean sprint
attempt, not a proposal.

## Concrete edits expected

### Phase A: Phase 0 mpmath sweep (the load-bearing deliverable)

- `Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.py` (NEW,
  ≈250–400 lines): the main sweep script. Required structure:

  1. **Imports and precision**: `mpmath` with `mp.prec = 200`, plus
     `numpy`/`scipy.optimize` for α-vector optimisation if needed.

  2. **Kernel derivation**: a function
     `per_k_alpha_varying_kernel(c, alpha_seq, b_coeffs, K=20)` that
     computes:

     `∑_{k=0}^{K-1} kernel_k(c, α(k), b_coeffs)`

     where `kernel_k` is the closed-form per-`k` contribution to
     `annulusExcess(c) − diskExcess(c)` evaluated under the
     α-varying lift identity. Specifically: derive the per-`k`
     contribution from V54's `lift_identity_per_k a b α k` instantiated
     at α := α(k), times the disk-side weight `c^(2k+2)/(k+1)` and
     the annulus-side weight `(1 − c^(2k+2))/(k+1)`, with the
     `(1 − α(k)²)` cross-multiplication. The script's docstring must
     state the formula explicitly and cite the lift identity it
     instantiates.

     **Critical sanity check before the sweep**: at `α(k) = c` for
     every `k` (i.e. uniform α = c), the kernel must reproduce
     V58.Theorem 3's closed form
     `∑_k coeffPlusGap_k · (1 − 2c^(2k+2))/(k+1)`. The script must
     assert this equality at `c = 0.35645` on E1 (where the value
     is `−(1 − 2·0.35645⁴)/2 ≈ −0.4839`) **before** any α-varying
     sweep. If the sanity check fails, the kernel formula is wrong;
     halt with `STATUS=BLOCKED` and document the discrepancy.

  3. **Canonical extremal taxonomy**:

     ```python
     EXTREMALS = {
         'E1': lambda K: [(0,1) if k == 1 else (0,0) for k in range(K)],
         'E2': lambda K: [(0,1) if k == 2 else (0,0) for k in range(K)],
         'E3': lambda K: [(0,1) if k == 3 else (0,0) for k in range(K)],
         'E4': lambda K: [(0,1) if k == 4 else (0,0) for k in range(K)],
         'E5': lambda K: [(0,1) if k == 5 else (0,0) for k in range(K)],
         # plus 6+ small linear combinations:
         'E1+0.5*E2': ...,
         'E1+0.5*E3': ...,
         'E2+0.5*E3': ...,
         'E1+E2+E3 (equal)': ...,
         'E1-0.5*E2': ...,  # sign-flipped to probe negative coeffs
         'E1+0.1*E5': ...,
     }
     ```

     Each entry returns the (a_k, b_k) pair sequence for `k ∈ [0, K)`.
     `coeffPlusGap_k = ‖a_k‖² − ‖b_k‖²` per V58's convention.

  4. **α(·) family grid**: at minimum, the following three families,
     each parameterised by 1–3 real scalars to keep the optimisation
     tractable:

     - **constant**: `α(k) = α_0` for all `k`. Sweep `α_0 ∈
       {0.1, 0.2, 0.3, 0.35645, 0.4, 0.5, 0.7, 0.9}`. (This includes
       the known-falsifying uniform `α_0 = c` as a sanity baseline.)

     - **geometric**: `α(k) = α_0 · r^k` for `α_0 ∈ {0.1, 0.3, 0.5}`,
       `r ∈ {0.5, 0.8, 1.0, 1.2, 2.0}`. (Captures the intuition that
       higher-`k` modes might want different α than mode 1.)

     - **mode-1-zeroing**: `α(0) = α_0`, `α(1) = 0`, `α(k) = α_0` for
       `k ≥ 2`, with `α_0 ∈ {0.1, 0.3, 0.5}`. (Targets the E1
       falsification by forcing α(1) = 0 so the `(1 − α(1)²) = 1`
       factor stays unit, breaking the V58.Th3 E1 sign issue.)

     - **(optional, run if budget permits) free-form
       `scipy.optimize.minimize`** over `α : ℝ^K` minimising the
       worst-extremal kernel at fixed `c`, started from each of the
       three structured families' best points. If the optimiser
       returns a witness, record it with full α-vector printout.

  5. **`c` grid**: at minimum,
     `c ∈ {0.35645, 0.35650, 0.35660, 0.35680, 0.35700, 0.35720,
            0.35740, 0.35760, 0.35780, 0.35800, 0.35820, 0.35840,
            0.35860, 0.35880, 0.35900, 0.36000, 0.36050}`. The
     `0.35645` and `0.35900` endpoints are sanity baselines.

  6. **Sweep output format**: a table indexed by
     `(c, α-family, α-params, extremal)`, recording the per-`k`
     kernel sum value (or per-`k` decomposition for diagnostic
     drilldown). The script writes:

     - `Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.txt` —
       a human-readable summary table of all `(c, α-family)` pairs
       and their worst-extremal kernel value, with margin column.

     - `Scratch/sprint_077_witness.txt` if any
       `(c, α(·), all extremals)` triple has worst-extremal margin
       `≥ 1e-4`: a precise `(c, α-vector, K, extremal-by-extremal
       margin)` dump suitable for a Lean-facing witness statement
       in sprint 078. **Do not write this file unless a witness
       exists.**

     - `Scratch/sprint_077_no_go.txt` if no witness is found: a
       precise documentation of which extremal saturates at every
       tested `(c, α-family)`, the saturation `c` value, and at
       least three optimisation directions tried. **This file is
       written if and only if no witness exists.**

  7. **Margin computation**: for each
     `(c, α-vector, extremal)`, kernel value `v`. Margin `m =
     v / |annulusExcess(c, this extremal)|` — i.e. the kernel sum
     normalised by the annulus excess scale at this extremal. A
     witness requires `m ≥ 1e-4` on every extremal **and** on every
     small-linear-combination probe.

  8. **Determinism**: the script is fully deterministic
     (no `random` calls except where explicitly seeded with
     `random.seed(42)` or `numpy.random.seed(42)`). Re-running it
     produces byte-identical outputs.

### Phase B: Lean stub freezing the structural location

If and only if Phase A produces **either** a `_witness.txt` or a
`_no_go.txt` file (i.e. the sweep ran to completion, regardless of
outcome), proceed to Phase B. **Do not skip Phase A or short-circuit
its output.**

- `Candidates/V60/PerKAlphaVaryingLiftIdentity.lean` (NEW, ≈80 lines):
  the trivial generalisation of V54's `lift_identity_per_k` from
  `α : ℝ` to `α : ℕ → ℝ`. The whole file is two theorems:

  ```text
  theorem lift_identity_per_k_alpha_varying
      (a b : ℕ → ℂ) (α : ℕ → ℝ) (k : ℕ) :
      (1 - (α k) ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
        = ‖b k - ((α k) : ℂ) * a k‖ ^ 2
            - ‖a k - ((α k) : ℂ) * b k‖ ^ 2 :=
    ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k
      a b (α k) k

  theorem lift_identity_per_k_alpha_varying_rearranged
      (a b : ℕ → ℂ) (α : ℕ → ℝ)
      (hα : ∀ k, (α k) ^ 2 < 1) (k : ℕ) :
      ‖b k‖ ^ 2 - ‖a k‖ ^ 2
        = (‖b k - ((α k) : ℂ) * a k‖ ^ 2
             - ‖a k - ((α k) : ℂ) * b k‖ ^ 2)
            / (1 - (α k) ^ 2) :=
    ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k_rearranged
      a b (α k) (hα k) k
  ```

  This is intentionally a one-line wrapper — the algebraic content is
  V54's, and the planner is **not** claiming structural novelty in
  the Lean derivation here. The file's purpose is to (a) freeze the
  α-varying signature into the workspace's import graph for sprint
  078's downstream use, and (b) make the next planner's task —
  consuming the signature and shipping a c-push if Phase 0 went GO,
  or pivoting if Phase 0 went NO-GO — a one-import affair. The Lean
  novelty is deferred to sprint 078.

- `Candidates/V60.lean` (NEW, ≈100 lines): V59-tied at `c_value =
  7129/20000 = 0.35645` via `valid_of_eq15` discharged by
  `hEq15_oracle_certified_hp_35645`. Body identical to V59.lean
  except:

  - the namespace is `ProofRefinement.Korenblum.Candidates.V60`;
  - the parent is V59;
  - imports `ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity`;
  - the side lemma is renamed
    `v60_per_k_alpha_varying_compiles_at_witness` and exercises
    `lift_identity_per_k_alpha_varying`'s signature against arbitrary
    `(a, b : ℕ → ℂ)`, `α : ℕ → ℝ`, `k : ℕ` input (statement-level
    non-vacuity check) — concretely a one-line application:

    ```text
    theorem v60_per_k_alpha_varying_compiles_at_witness
        (a b : ℕ → ℂ) (α : ℕ → ℝ) (k : ℕ) :
        (1 - (α k) ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
          = ‖b k - ((α k) : ℂ) * a k‖ ^ 2
              - ‖a k - ((α k) : ℂ) * b k‖ ^ 2 :=
      ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity
        .lift_identity_per_k_alpha_varying a b α k
    ```

- `lemma.toml` (one-line edit): add
  `"ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity"`
  to `[import_policy].allowed_exact`, mirroring the existing rows for
  `Candidates.V53.ThetaStep`, `Candidates.V54.LiftIdentity`,
  `Candidates.V55.LiftSeriesBridge`,
  `Candidates.V57.DiskExcessLiftIntegrated`,
  `Candidates.V58.AnnulusExcessLiftIntegrated`. **No other
  `lemma.toml` edits.**

- `Bulletin.md`: append one row under "Recent events":

  ```
  sprint_077 PASS: phase 0 mpmath sweep [GO|NO-GO] for per-k α-varying kernel; V60 ships stub α-varying lift identity tied to V59
  ```

  (Replace `[GO|NO-GO]` with the actual outcome.)

- `Experience.md`: append a sprint-077 section per the brief's
  "Honesty in Experience.md" rules. Required content:

  - **What was attempted**: the kernel derivation strategy, the α-family
    grid, the c-grid, the canonical extremal taxonomy.
  - **What numerical exploration was done**: the script's actual run
    output, including the sanity check at uniform α = c on E1
    confirming the V58.Theorem 3 closed form, the worst-extremal
    margin per `(c, α-family)` cell, the GO/NO-GO outcome.
  - **The current obstacle to `c > 7129/20000`**: if NO-GO, name the
    saturating extremal explicitly (e.g. "E2 saturates at every
    tested α-family at every c ≥ 0.357"); if GO, name the witness
    triple `(c, α-vector, K, margin)` and confirm the margin holds
    on every linear-combination probe.
  - **What is the next move**: if GO, sprint 078 ships a Lean
    derivation of the α-varying integrated lift identity in
    `Candidates/V60/`, tracking V57/V58's pattern, and a V61
    side lemma attempts the c-push using the witness as the
    integral-mass-≥-1 input. If NO-GO, sprint 078 pivots to a
    different chain (Wang Lemma 2 / Fourier orthogonality, the
    Wang `(5)` higher-mode pocket described in the Bulletin's V38
    directive update, or a multi-window τ-partition reattempt
    with the corrected motive handling from sprint 074).
  - **What would unblock a c-push faster**: refined per the actual
    sweep results — e.g. if a wider α-family grid is suggested
    by the sweep's marginal cells, or if the sweep reveals that a
    completely different free parameter (per-mode τ-window
    boundary, Wang `(5)` truncation index, etc.) is the right
    optimisation register.

## Acceptance criteria

1. **Phase A: sweep script runs cleanly.**
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   python ProofRefinement/Korenblum/Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.py`
   exits with code 0. The script's sanity check at uniform α = c on
   E1 confirms V58.Theorem 3's closed form to within mpmath's
   `prec=200` tolerance.

2. **Phase A: outputs.**
   - `Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.txt` exists
     and contains the full sweep summary table (every
     `(c, α-family, α-params, extremal)` cell from the grid).
   - **Exactly one** of `Scratch/sprint_077_witness.txt` or
     `Scratch/sprint_077_no_go.txt` exists, depending on the
     outcome. The presence of both, or of neither, is a sprint
     failure (rerun the script to disambiguate).

3. **Phase B: Lean stub builds.**
   `lake build ProofRefinement.Korenblum.Candidates.V60` succeeds.
   `Candidates/V60.lean` is V59-tied at `c_value = 7129/20000`,
   compiles without `sorry`/`admit`, and the side lemma exercises
   the new `Candidates.V60.PerKAlphaVaryingLiftIdentity` theorem.

4. **Phase B: evaluator passes.**
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V60.lean` reports
   `pass: true`. The score is `7129/20000 = 0.35645` (V59-tied).
   `axioms_used = {propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V60.hEq15_oracle_certified_hp_35645}`
   — byte-for-byte identical to V59's envelope modulo the
   namespace-prefix on the oracle axiom.

5. **Phase B: structural advance.** The new file
   `Candidates/V60/PerKAlphaVaryingLiftIdentity.lean` is the **first
   per-candidate derived-theorem file** in the workspace whose
   signature ranges over `α : ℕ → ℝ` (per-mode α(·)) rather than
   `α : ℝ` (uniform α). The next planner can consume this signature
   directly when building the α-varying integrated lift identity.

6. **No edits to read-only / out-of-scope surfaces.** No edits to
   `KorenblumPaper/*.lean`, no edits to `Numerical_Library/`, no
   edits to existing `Candidates/V<K>.lean` for K ≤ 59, no edits to
   any per-candidate derived-theorem file under `Candidates/V<N>/`
   for N ≤ 59, no edits to `Proof/CandidateContract.lean`,
   `Proof/Main.lean`, `Proof/Reduction.lean`, or any other
   `Proof/*.lean` file. Only `lemma.toml`, `Bulletin.md`,
   `Experience.md`, the new `Candidates/V60.lean`, the new
   `Candidates/V60/PerKAlphaVaryingLiftIdentity.lean`, and the
   `Scratch/sprint_077_*.{py,txt}` files are touched.

7. **No new paper axioms, no new oracles, no proposal filing.**

8. **Honesty in `Experience.md`.** All five honesty bullets above
   are satisfied with concrete content drawn from the actual sweep
   output (no boilerplate, no copy-paste from prior sprint
   Experience entries).

## Out of scope

- A c-push attempt in this sprint. **Sprint 077 ties V59 at
  `c = 7129/20000`.** The c-push attempt is sprint 078's contract,
  gated by Phase 0's outcome.
- A Lean derivation of the α-varying integrated lift identity. The
  Lean stub in Phase B is a one-line wrapper of V54; the actual
  α-varying integrated form (analogous to V57.Theorem 1 with α
  swapped for α(k) per index) is sprint 078's deliverable.
- Edits to `Candidates/V<K>.lean` for K ≤ 59, or to per-candidate
  derived-theorem files under `Candidates/V53/V54/V55/V57/V58/`.
- Edits to `KorenblumPaper/*.lean`, `Proof/*.lean`,
  `Numerical_Library/`.
- A `Proposals/` filing.
- A `Reduction.lean` edit. The α-varying integrated lift would, if
  productive, eventually merit a shared-trust-surface theorem in
  `Reduction.lean`; this is sprint 079+ territory if the Phase 0
  outcome is GO and sprint 078's c-push lands.
- Sweeping α-families beyond constant, geometric, mode-1-zeroing, and
  (optional) free-form scipy. If the planner's enumerated grid is
  exhausted with NO-GO on every cell, the next planner expands the
  grid in sprint 078 (or pivots).
- Sweeping at `c > 0.36050`. The Bulletin's V38 directive notes
  that `c ≈ 0.3564015` is the τ-window envelope's tight point;
  sweeping much beyond that is wasted compute.

## Time budget

≤ 90 minutes runtime.

- Phase A (mpmath sweep): 50–70 minutes. The dominant cost is the
  full grid sweep at `mp.prec = 200` over ≈18 c-values × ≈20 α-family
  cells × ≈11 extremals × `K = 20` modes ≈ 80,000 mpmath kernel
  evaluations. The script should be vectorisable per-`c` and
  per-extremal; if the runtime exceeds 70 min, drop the optional
  free-form scipy sweep and keep the structured-α-family grid.
  If the runtime still exceeds the budget after that, halve the
  c-grid resolution.

- Phase B (Lean stub + side lemma): 15–20 minutes. The whole file is
  one-line wrappers of V54.

- `lemma.toml` / `Bulletin.md` / `Experience.md`: 5 minutes.

The Lean side is intentionally small. The sprint's load-bearing work
is Phase A.

## Stop conditions

- **Acceptance criteria 1–8 met (Phase A and Phase B both ship)**:
  `STATUS=READY_FOR_EVALUATION`. Standard PASS-tie-with-Phase-0-witness-or-no-go
  outcome.

- **Phase A's sanity check fails** (kernel formula at uniform α = c
  on E1 disagrees with V58.Theorem 3's closed-form at `c = 0.35645`):
  `STATUS=BLOCKED` with an obstruction note at
  `Scratch/sprint_077_obstruction.md` documenting the discrepancy
  (script formula vs V58.Th3 expected value), the kernel-derivation
  step where the discrepancy enters, and at least three attempted
  fixes (sign convention, lift-identity instantiation order,
  per-`k` weight ordering). **Do not ship Phase B if Phase A's
  sanity check fails.**

- **Phase A runs but produces neither `_witness.txt` nor `_no_go.txt`**
  (e.g. the script crashes mid-sweep at some `(c, α)` cell):
  `STATUS=BLOCKED` with an obstruction note. Phase B is skipped.

- **Phase B builds fail because the V54 import is missing or because
  `lemma.toml`'s `[import_policy].allowed_exact` row is malformed**:
  `STATUS=BLOCKED` with an obstruction note. Phase A is preserved
  (it stands as the load-bearing deliverable regardless).

- **Phase A returns NO-GO and Phase B builds clean**: ship the
  contract as `STATUS=READY_FOR_EVALUATION`. The NO-GO outcome is
  not a sprint failure — it is a load-bearing input to the next
  planner's pivot decision. Document the NO-GO clearly and confirm
  the Bulletin's "Recent events" row reads
  `sprint_077 PASS: phase 0 mpmath sweep NO-GO for per-k α-varying
  kernel; V60 ships stub α-varying lift identity tied to V59`.

- **Phase A returns GO** (witness exists at some c > 7129/20000 with
  margin ≥ 1e-4 on every extremal and every linear-combination probe):
  ship the contract as `STATUS=READY_FOR_EVALUATION`. The next
  planner queues sprint 078 as the Lean c-push attempt consuming the
  witness, with α-vector and `c` value taken directly from
  `_witness.txt`.

## Sprint sequencing note (for the next planner)

If Phase A returns **GO** and Phase B ships:

  **Sprint 078 (GO branch)** — *Lean derivation of the α-varying
  integrated lift identity over `[c, 1] ∪ [0, c]`, plus V61 c-push
  attempt at the witness's `(c, α-vector)`*. This sprint ships a new
  per-candidate derived-theorem file
  `Candidates/V61/PerKAlphaVaryingIntegratedLift.lean` containing the
  α-varying analogues of V57.Theorem 1 and V58.Theorem 1 (each ≈300
  lines, transplanting the V57/V58 proof template with α(k) swapped
  for α per-index), plus a closing reducer in `Reduction.lean`
  consuming the witness's per-`k` kernel positivity and concluding
  `diskExcess(c) ≤ annulusExcess(c)` at the witness's `c`. The c-push
  is the candidate-side `Candidates/V61.lean` at the witness's `c`,
  with axioms_used = {seed} ∪ {witness's proof obligation, which is
  either a `norm_num` over rational α-vectors plus `c` or a
  finite-mode-truncation oracle if the witness's α-vector requires
  irrational components}.

If Phase A returns **NO-GO**:

  **Sprint 078 (NO-GO branch)** — *Pivot to a different chain*. The
  next planner reads the NO-GO output's saturating extremal and
  α-family direction, then chooses one of:

  - **Wang Lemma 2 boundary L² Parseval-at-radius-ρ** as a V61
    derived theorem (Fourier orthogonality register). High-value
    register that no sprint has touched; gives per-mode coefficient
    ↔ boundary-integral equivalences that are currently only
    surfaced as hypotheses.

  - **Multi-window τ-partition reducer (sprint 072 reattempt with
    sprint 074's motive-handling fix)**. Builds the V38 seven-window
    Lean infrastructure even if Phase 0 forecast was NO-GO; the
    infrastructure is necessary for the Wang `(5)` higher-mode pocket
    that the Bulletin's V38 directive identifies as the harness's
    structural blind spot.

  - **eq-15 oracle's HP-precision push** to HP-35648 / HP-35649.
    The Bulletin's "1.35e-05 HP shoulder" framing means the literal
    Wang-(15) crossover at `c ≈ 0.35635` is below the V52 shoulder
    by ~1.35e-05; pushing the HP precision further may recover
    a few more decimal places of `c`.

The Phase 0 outcome determines which of these routes the next
planner pursues. **Do not pre-decide.**
