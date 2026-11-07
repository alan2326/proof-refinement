#!/usr/bin/env python3
"""Build the sprint-016 Grothendieck Arm C'' workspace: agentic system kept,
partial formalization ablated, statement level = outermost (K_G).

Fork of make_arm_c_groth.py per design doc sect. 13.3. Differences from the
sect. 12.5 builder, all deliberate:

1. **Exact-real seed axiom.** The seed is
       axiom hKrivine : GrothendieckIneq KrivineBound
   at the exact real KrivineBound = pi/(2*log(1+sqrt 2)) -- the true K_G
   frontier at iteration start -- rather than a rational rounded UP from it.
   Sect. 12.8c showed the rounded-up seed leaves a 2.2e-8 window in which
   re-proving Krivine's own bound scores as a win; the exact-real seed
   eliminates that window structurally. Success (classifier-side) requires a
   certified rational K_val < KrivineBound, decided against a 50-digit
   certified interval; no such rational is derivable from the seed.

2. **The contract carries two study-infrastructure lemmas** (disclosed):
   * `GrothendieckIneq.mono` -- upward monotonicity in the constant (proven,
     sign-flip argument);
   * `KrivineBound_le_seed : KrivineBound <= 1782214/1000000` -- the
     kernel-checked numeric certificate, port of the sqrt/log/pi chain from
     the sect. 12 Arm C run's own `KrivineNumeric.lean` (that file was
     produced entirely inside the ablation study; lifting it leaks nothing
     about the sprint-016 anchor).
   Together they let the seed V0 still evaluate at score 1782214/1000000
   (identical seed score to the sect. 12 arm) while the axiom itself sits at
   the exact real.

3. **pyproject fix** (sect. 12.8e item 2): the deleted `grothendieck` python
   package is replaced by an EMPTY stub so `uv run` / harness_preflight.sh
   work; the sect. 12 run lost a gate to this.

Usage:  python3 harness/make_arm_c_groth016.py
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
WS = ROOT / "workspaces" / "groth16_armC"
L54 = WS / "ProofRefinement" / "Lemma54"
EVAL_SRC = (ROOT / "workspaces" / "S0_korenblum" / "ProofRefinement" /
            "Korenblum" / "Evaluator.py")
BRAVERMAN_PDF = WS / "assets" / "pdf" / "braverman.pdf"
BRAVERMAN_TXT = ROOT / "harness" / "braverman2011.txt"

SEED_K = "1782214 / 1000000"      # KrivineBound = 1.7822139781... < 1.782214


CONTRACT = '''/-
Candidate contract for Arm C'' (partial formalization ablated) of the
sprint-016 Grothendieck ablation study.

States the constant of record -- the Grothendieck constant K_G -- in Mathlib
terms only. `GrothendieckIneq` and `KrivineBound` are verbatim copies of the
production definitions; they are restated standalone because this workspace
carries no production formalization to import.

Two further declarations are STUDY INFRASTRUCTURE, shipped so that the seed
candidate can evaluate at a rational score while the seed axiom sits at the
exact real `KrivineBound`:

* `GrothendieckIneq.mono` -- the inequality is upward monotone in `K`;
* `KrivineBound_le_seed` -- a kernel-checked numeric certificate
  `KrivineBound <= 1782214/1000000` (rational-endpoint chain for sqrt 2,
  log(1+sqrt 2) and pi; margin ~4e-8).
-/
import Mathlib

open Real Set

noncomputable section

namespace ProofRefinement.Lemma54

/-- A constant K satisfies the Grothendieck inequality if for all finite
    bilinear forms defined by signs, the SDP relaxation ratio is at most K.

    Formally: for all n, m, matrix A, and unit vectors x, y in any
    real Hilbert space H,
      max_{eps,del in {+-1}^n x m} sum_ij a_ij eps_i del_j
        >= (1/K) * sum_ij a_ij <x_i, y_j> -/
def GrothendieckIneq (K : ℝ) : Prop :=
  0 < K ∧
  ∀ (n m : ℕ) (A : Fin n → Fin m → ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (_ : ∀ i, ‖x i‖ = 1) (_ : ∀ j, ‖y j‖ = 1),
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * ε i * δ j ≥
        (1 / K) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j)

/-- The Krivine bound: pi/(2*log(1+sqrt 2)) ~= 1.7822139781.
    The previous state of the art for K_G. -/
def KrivineBound : ℝ := Real.pi / (2 * Real.log (1 + Real.sqrt 2))

private theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos_of_pos (by norm_num)

theorem log_one_add_sqrt_two_pos : (0 : ℝ) < Real.log (1 + Real.sqrt 2) :=
  Real.log_pos (by linarith [sqrt_two_pos])

theorem KrivineBound_pos : 0 < KrivineBound := by
  unfold KrivineBound
  exact div_pos Real.pi_pos (mul_pos (by norm_num) log_one_add_sqrt_two_pos)

/-! ### Study infrastructure -/

/-- `GrothendieckIneq` is upward monotone in the constant: a bound at `K`
    implies a bound at any `K' ≥ K`. When the SDP value is negative the
    given signs may not do; flipping `ε` makes the sign sum nonnegative. -/
theorem GrothendieckIneq.mono.{u} {K K' : ℝ} (hKK' : K ≤ K')
    (h : GrothendieckIneq.{u} K) : GrothendieckIneq.{u} K' := by
  obtain ⟨hKpos, h⟩ := h
  have hK'pos : 0 < K' := lt_of_lt_of_le hKpos hKK'
  refine ⟨hK'pos, ?_⟩
  intro n m A H _ _ x y hx hy
  obtain ⟨ε, δ, hε, hδ, hineq⟩ := h n m A H x y hx hy
  set S := ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j) with hS
  rcases le_total 0 S with hS0 | hS0
  · -- 0 ≤ S: the same signs work, since 1/K' ≤ 1/K.
    refine ⟨ε, δ, hε, hδ, ?_⟩
    have h1 : (1 / K') * S ≤ (1 / K) * S :=
      mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le hKpos hKK') hS0
    linarith
  · -- S ≤ 0: (1/K')·S ≤ 0, so any sign choice with nonnegative sum works.
    have hnn : (0 : ℝ) ≤ 1 / K' := by positivity
    have hneg : (1 / K') * S ≤ 0 := by nlinarith
    rcases le_total 0 (∑ i, ∑ j, A i j * ε i * δ j) with hT | hT
    · exact ⟨ε, δ, hε, hδ, by linarith⟩
    · refine ⟨fun i => -ε i, δ, ?_, hδ, ?_⟩
      · intro i
        rcases hε i with h1 | h1
        · right; simp [h1]
        · left; simp [h1]
      · have hsum : (∑ i, ∑ j, A i j * (-ε i) * δ j)
            = -(∑ i, ∑ j, A i j * ε i * δ j) := by
          simp [mul_neg, neg_mul]
        rw [hsum]
        linarith

/-- A rational lower bound for `√2`, accurate to `2.7e-13`. -/
theorem sqrt_two_ge : (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 :=
  Real.le_sqrt_of_sq_le (by norm_num)

/-- A rational lower bound for `log (1 + √2)`, accurate to `2.0e-11`. The
exponential is bounded by its degree-12 Taylor polynomial plus the tail
estimate of `Real.exp_bound'`. -/
theorem le_log_one_add_sqrt_two :
    (881373587 / 1000000000 : ℝ) ≤ Real.log (1 + Real.sqrt 2) := by
  have hs : (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 := sqrt_two_ge
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2
    linarith
  rw [Real.le_log_iff_exp_le hpos]
  have hb := Real.exp_bound' (x := (881373587 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (n := 12) (by norm_num)
  refine hb.trans ?_
  have htail : (∑ m ∈ Finset.range 12,
        (881373587 / 1000000000 : ℝ) ^ m / m.factorial) +
      (881373587 / 1000000000 : ℝ) ^ 12 * (12 + 1) /
        ((Nat.factorial 12 : ℝ) * 12)
        ≤ 1 + 1414213562373 / 1000000000000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine htail.trans ?_
  linarith

/-- **Kernel-checked numeric certificate**: the Krivine bound is below the
rational seed `1782214/1000000`, with margin `~3.8e-8`. -/
theorem KrivineBound_le_seed : KrivineBound ≤ 1782214 / 1000000 := by
  have hlog := le_log_one_add_sqrt_two
  have h2 : (0 : ℝ) < 2 * Real.log (1 + Real.sqrt 2) := by
    linarith [log_one_add_sqrt_two_pos]
  unfold KrivineBound
  rw [div_le_iff₀ h2]
  have hpi : π < 3.14159265358979323847 := Real.pi_lt_d20
  linarith

end ProofRefinement.Lemma54
'''

V0 = f'''-- @parent seed
import ProofRefinement.Lemma54.Proof.CandidateContract

noncomputable section

namespace ProofRefinement.Lemma54.Candidates.V0

open ProofRefinement.Lemma54

/-- The rational score of the seed candidate: the Krivine bound rationalized
    one ulp up (KrivineBound ~= 1.7822139781 < 1782214/1000000). Smaller is
    better. -/
def K_val : ℝ := {SEED_K}

theorem K_val_pos : (0 : ℝ) < K_val := by
  norm_num [K_val]

/--
Seed external input: the previous state of the art for the Grothendieck
constant, asserted at the K_G level as a single axiom **at the exact real**
`KrivineBound = π / (2·log(1+√2))`.

This is the ONLY mathematical input in this arm. There is no IFT / F_inv
apparatus, no Lemma 5.4, no rounding-scheme chain and no numerical oracle.

Because `GrothendieckIneq` is upward monotone (`GrothendieckIneq.mono`,
proven in the contract), nothing below `KrivineBound` is derivable from this
axiom: certifying any rational `K < KrivineBound` requires new mathematics
beyond the published state of the art.
-/
axiom hKrivine : GrothendieckIneq KrivineBound

/-- Seed candidate: the previous best bound, evaluated at the rational
    ceiling `K_val`. Uses the contract's monotonicity lemma plus the
    kernel-checked certificate `KrivineBound ≤ K_val`. -/
theorem grothendieck_bound_search : GrothendieckIneq K_val := by
  have hle : KrivineBound ≤ K_val := by
    unfold K_val
    exact KrivineBound_le_seed
  exact GrothendieckIneq.mono hle hKrivine

end ProofRefinement.Lemma54.Candidates.V0
'''

LEMMA_TOML = '''name = "Grothendieck constant K_G (Arm C'' — no partial formalization, sprint-016 study)"
slug = "grothendieck016_armC_noPF"
paper_ref = "Braverman–Makarychev–Makarychev–Naor (2011); previous best K_G ≤ π/(2·log(1+√2)) = KrivineBound"

sink_theorem = "grothendieck_bound_search"
constant_def = "K_val"
score = "K_val"
score_direction = "minimize"

[search_constants]

[import_policy]
# Candidate-side surface. No LeanProof.* / ProofGraph.* — the partial
# formalization is the ablated factor in this arm. New derived-theorem modules
# the agent builds under ProofRefinement.Lemma54.* are admitted via prefixes.
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Lemma54",
  "Mathlib",
]

[workspace_import_policy]
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Lemma54",
  "Mathlib",
]

[seed_axioms]
allowed = [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
  "Lean.trustCompiler",

  # The previous state of the art, axiomatized at the K_G level AT THE EXACT
  # REAL KrivineBound. By the contract's monotonicity lemma this is the
  # weakest sound statement of the pre-iteration frontier: no rational below
  # KrivineBound is derivable from it.
  "hKrivine",
]

# No oracles at seed. If the agent builds its own numerical sub-claim it must
# register the wrapper here, exactly as the with-PF workspace does.
'''

BRIEF = '''# Agent brief — Grothendieck K_G, Arm C'' (partial formalization ablated)

## The contract

`Proof/CandidateContract.lean` defines, against Mathlib only:

* `GrothendieckIneq K` — the Grothendieck inequality at constant `K`: for
  every finite real matrix `A` and unit vectors in any real Hilbert space,
  some sign vectors achieve at least `(1/K)` of the SDP value;
* `KrivineBound = π / (2·log(1+√2)) ≈ 1.7822139781` — the previous state
  of the art;
* `GrothendieckIneq.mono` — upward monotonicity in `K` (proven);
* `KrivineBound_le_seed : KrivineBound ≤ 1782214/1000000` — a kernel-checked
  numeric certificate.

There is **no** IFT / analytic-inverse apparatus, **no** Lemma 5.4, **no**
rounding-scheme chain and **no** numerical oracle.

## The task

`Candidates/V0.lean` asserts the previous state of the art as one axiom at
the exact real:

```lean
axiom hKrivine : GrothendieckIneq KrivineBound
```

and evaluates at the rational ceiling `K_val = 1782214/1000000`.

Ship a candidate `Candidates/V<N>.lean` whose `grothendieck_bound_search`
proves `GrothendieckIneq K_val` for some rational
`K_val < 1782214/1000000` (smaller is better), and which the evaluator
accepts.

**What counts as a real advance.** By monotonicity, any rational
`K_val ≥ KrivineBound` is derivable from the seed by tightening the numeric
certificate (better rational endpoints for √2, log, π). Such candidates are
accepted by the gate and logged as progress, but the study scores them as
*re-certifications of the known frontier*, *not* as an improvement of the
Grothendieck constant. **Success for this arm means a certified
`K_val < KrivineBound`** — mathematics strictly beyond the published state
of the art (e.g. via an improved rounding scheme, as Braverman et al. did
for the exact constant). Spend your budget accordingly.

## What you have

* Mathlib, in full.
* Braverman–Makarychev–Makarychev–Naor (2011), at `Braverman2011.pdf` and
  `Braverman2011.txt` in this directory (also `assets/pdf/braverman.pdf`).
* Web search and web fetch.
* The Lean LSP and Lean search MCP tools.
* The standard harness: sprint contracts, `Refinement_Log/`, `Bulletin.md`,
  `Experience.md`, `Proposals/`, `Evaluator.py`, `scripts/`.

Building whatever Lean apparatus you need — including a partial
formalization of your own design — is **in scope and expected**.

## What does not count as progress

The evaluator gate: a candidate passes only if it compiles, its sink theorem
type-checks against `GrothendieckIneq K_val` exactly, its audited axiom set
is a subset of `[seed_axioms].allowed` (plus registered oracles), there is no
`sorryAx`, and `K_val` strictly improves on (is less than) the parent.

**A direct-conclusion axiom at a smaller `K` is not progress.** Adding, say,

```lean
axiom h : GrothendieckIneq (17 / 10)
```

and registering it in `[seed_axioms].allowed` would satisfy the letter of the
gate while asserting exactly the thing to be proved. Do not do this. If you
introduce a new axiom it must be a genuine sub-claim — strictly weaker than
the conclusion — and you must say in the sprint contract why it is weaker.

If you introduce a numerical sub-claim, register it as an `[[oracles]]` row
with a wrapper the evaluator can recompute (a function exported from a
`Numerical_Library/` package you create, returning an object with a rational
`.bound`), exactly as a with-PF workspace does.

## Evaluator

```
uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V<N>.lean
```

Build first: `lake build ProofRefinement.Lemma54.Candidates.V<N>`.
'''

BULLETIN = '''# Bulletin — Grothendieck K_G, Arm C''

Format: one line per sprint event, append-only, newest last.

## Current priority (human-set)

Improve the certified upper bound on the Grothendieck constant K_G strictly
below `KrivineBound = π/(2·log(1+√2))`. Rational re-certifications of the
Krivine frontier (K_val ≥ KrivineBound) are accepted by the gate but do not
meet the study's success criterion — see `AGENT_BRIEF.md`. Build whatever
Lean apparatus you need under `ProofRefinement.Lemma54.*`; expand the trust
base only through the `Proposals/` process.

## Events

(none yet)
'''

EXPERIENCE = '''# Experience — Grothendieck K_G, Arm C''

## Sticky note (read every time)

* The evaluator's TYPE gate requires `grothendieck_bound_search :
  GrothendieckIneq K_val` exactly, with `K_val` a rational literal def.
* New axioms outside `[seed_axioms].allowed` fail the audit. Trust-base
  growth goes through `Proposals/` + oracle registration.
* Candidates import only `ProofRefinement.Lemma54.*` and `Mathlib`.
* Success = certified `K_val < KrivineBound` (the exact real), not merely
  `< 1782214/1000000`. See AGENT_BRIEF "What counts as a real advance".

## Entries

(none yet)
'''

CLAUDE_MD = '''# Workspace

This is the Arm C'' (no partial formalization) ablation workspace for the
sprint-016 Grothendieck study. The only active project is
`ProofRefinement/Lemma54/` — read `ProofRefinement/Lemma54/AGENT_BRIEF.md`
first. The refinement loop is driven by the `/run-next-sprint` skill.
'''

PYSTUB = '''"""Stub package.

The real `grothendieck` numerics package is part of the ablated partial
formalization and is deliberately absent from this workspace. This empty
stub exists only so the uv/poetry editable install stays buildable
(design doc sect. 13.3, fixing sect. 12.8e item 2). It contains no proof
content.
"""
'''


def rm(p: Path):
    if p.is_dir() and not p.is_symlink():
        shutil.rmtree(p, ignore_errors=True)
    elif p.exists() or p.is_symlink():
        p.unlink(missing_ok=True)


def main():
    # 1. Fresh clone of S0^16.
    subprocess.run([str(ROOT / "harness" / "make_arm_ws_groth16.sh"),
                    "groth16_armC"], check=True)

    # 2. Repo-level ablation: the entire Grothendieck formalization + numerics
    #    surface, and everything outside the standardized kept-list.
    for name in ["LeanProof", "LeanProof.lean", "ProofGraph", "ProofGraph.lean",
                 "Runs", "blueprint", "grothendieck", "outputs", "docs",
                 "evaluator", "high_precision_evaluator", "neural_search",
                 "basis_optimization", "multicurve_pipeline", "notebooks",
                 "experiments", "archive", "home_page", "ShinkaEvolve",
                 "run_proof_pipeline.py", ".github", ".gitmodules"]:
        rm(WS / name)
    rm(WS / "ProofRefinement" / "Korenblum")

    # 2b. uv project fix (sect. 12.8e item 2): pyproject declares the
    #     `grothendieck` package (poetry-core build); with it deleted every
    #     `uv run` fails its editable build and harness_preflight.sh exits 1.
    #     Restore buildability with an EMPTY stub -- zero proof content.
    (WS / "grothendieck").mkdir()
    (WS / "grothendieck" / "__init__.py").write_text(PYSTUB)

    # assets: keep only the Braverman paper.
    pdf_bytes = BRAVERMAN_PDF.read_bytes()
    rm(WS / "assets")
    (WS / "assets" / "pdf").mkdir(parents=True)
    (WS / "assets" / "pdf" / "braverman.pdf").write_bytes(pdf_bytes)

    # scripts: keep only what the run-next-sprint skill invokes.
    keep = {"harness_preflight.sh", "runner_cache_check.sh", "harness_reset.sh"}
    for p in (WS / "scripts").iterdir():
        if p.name not in keep:
            rm(p)

    # 3. Lemma54 ablation: strip to contract + seed + harness files.
    for name in ["Proof", "Numerical_Library", "Cache", "oracle", "Scratch",
                 "__pycache__", "Candidates"]:
        rm(L54 / name)
    for p in (L54 / "Sprint_Contracts").glob("sprint_*.md"):
        rm(p)
    for p in (L54 / "Refinement_Log").iterdir():
        rm(p)
    for p in (L54 / "Proposals").glob("proposal_*.md"):
        rm(p)
    (L54 / "Scratch").mkdir()
    (L54 / "Scratch" / ".gitkeep").write_text("")
    (L54 / "Candidates").mkdir()
    (L54 / "Proof").mkdir()

    # 4. New Lean surface + config + briefs.
    (L54 / "Proof" / "CandidateContract.lean").write_text(CONTRACT)
    (L54 / "Candidates" / "V0.lean").write_text(V0)
    (L54 / "lemma.toml").write_text(LEMMA_TOML)
    (L54 / "AGENT_BRIEF.md").write_text(BRIEF)
    (L54 / "Bulletin.md").write_text(BULLETIN)
    (L54 / "Experience.md").write_text(EXPERIENCE)
    (L54 / "README.md").write_text(BRIEF)
    (L54 / "Refinement_Log" / "log.jsonl").write_text("")
    (WS / "CLAUDE.md").write_text(CLAUDE_MD)
    shutil.copy2(BRAVERMAN_PDF, L54 / "Braverman2011.pdf")
    shutil.copy2(BRAVERMAN_TXT, L54 / "Braverman2011.txt")

    # 5. Evaluator: the korenblum-generalized checker (TYPE gate +
    #    score_direction), four literals re-pointed at the Lemma54 contract.
    ev = EVAL_SRC.read_text()
    ev = ev.replace(".korenblum_evaluator_typecheck.lean",
                    ".lemma54_evaluator_typecheck.lean")
    ev = ev.replace(".korenblum_axioms_check.lean", ".lemma54_axioms_check.lean")
    ev = ev.replace("import ProofRefinement.Korenblum.Proof.CandidateContract",
                    "import ProofRefinement.Lemma54.Proof.CandidateContract")
    ev = ev.replace("ProofRefinement.Korenblum.ValidKorenblumBound",
                    "ProofRefinement.Lemma54.GrothendieckIneq")
    (L54 / "Evaluator.py").write_text(ev)

    # 6. lakefile: only the ProofRefinement lib remains; give it a root module.
    lf = (WS / "lakefile.toml").read_text()
    lf = lf.replace('defaultTargets = ["LeanProof"]',
                    'defaultTargets = ["ProofRefinement"]')
    for lib in ("LeanProof", "Runs", "ProofGraph"):
        lf = lf.replace(f'[[lean_lib]]\nname = "{lib}"\n', "")
    (WS / "lakefile.toml").write_text(lf)
    assert 'name = "LeanProof"' not in lf, "lakefile lib strip failed"
    (WS / "ProofRefinement.lean").write_text(
        "import ProofRefinement.Lemma54.Candidates.V0\n")

    # 7. Commit the ablated state (fresh history on top of the S0 commit).
    subprocess.run(["git", "-C", str(WS), "add", "-A"], check=True)
    subprocess.run(["git", "-C", str(WS), "-c", "user.name=ablation",
                    "-c", "user.email=ablation@local", "commit", "-qm",
                    "Arm C'' workspace: PF ablated, K_G statement level, "
                    "exact-real Krivine seed"], check=True)

    # 8. Gates.
    env_path = str(Path.home() / ".elan" / "bin")
    env = {**os.environ, "PATH": env_path + os.pathsep + os.environ["PATH"]}

    # 8a. uv project health (the sect. 12.8e regression test).
    u = subprocess.run(["uv", "run", "python", "-c", "print('uv-run OK')"],
                       cwd=WS, capture_output=True, text=True, env=env,
                       timeout=600)
    print("[gate] uv run python:", "PASS" if u.returncode == 0 else "FAIL")
    if u.returncode != 0:
        print((u.stdout + u.stderr)[-2000:])
        sys.exit(1)

    pf = subprocess.run(["bash", "scripts/harness_preflight.sh"],
                        cwd=WS, capture_output=True, text=True, env=env,
                        timeout=600)
    print("[gate] harness_preflight.sh:",
          "PASS" if pf.returncode == 0 else "FAIL",
          (pf.stdout + pf.stderr).strip()[-200:])
    if pf.returncode != 0:
        sys.exit(1)

    # 8b. Seed builds and evaluates at the seed score.
    b = subprocess.run(["lake", "build", "ProofRefinement.Lemma54.Candidates.V0"],
                       cwd=WS, capture_output=True, text=True, env=env,
                       timeout=3600)
    print("[gate] lake build V0:", "PASS" if b.returncode == 0 else "FAIL")
    if b.returncode != 0:
        print((b.stdout + b.stderr)[-4000:])
        sys.exit(1)

    e = subprocess.run([str(WS / ".venv" / "bin" / "python"),
                        "ProofRefinement/Lemma54/Evaluator.py", "--file",
                        "ProofRefinement/Lemma54/Candidates/V0.lean",
                        "--no-log"],
                       cwd=WS, capture_output=True, text=True, env=env,
                       timeout=1800)
    out = e.stdout + e.stderr
    ok = e.returncode == 0 and "status: PASS" in out
    print("[gate] Evaluator V0:", "PASS" if ok else "FAIL")
    print(out[-2500:])
    if not ok:
        sys.exit(1)
    print("[make_arm_c_groth016] done.")


if __name__ == "__main__":
    main()
