import ProofRefinement.Korenblum.Proof.ProblemAxioms

noncomputable section

namespace ProofRefinement.Korenblum.ShinkaTrustedSeed

open ProofRefinement.Korenblum.ProblemAxioms

/--
Trusted seed axiom for the ShinkaAblation evolutionary run.

This file pins Wang's equation `(15)` to the literal rational
`3554 / 10000`, not to a re-bindable `c_value`. The agent harness's
own V0 candidate declares an analogous axiom locally inside the
candidate file, scoped to a `c_value` that the candidate is free to
redefine. The local-redeclaration trick lets an adversarial search
loop "prove" `ValidKorenblumBound c` for any `c < 1` simply by
overriding `c_value`. The local axiom passes the candidate-side
audit because the audit only checks the axiom's short name against
`seed_axioms.allowed`, not its type.

Pinning the type to the literal `(3554 / 10000 : ℝ)` here, in a
trusted file outside the candidate, closes that loophole for the
ablation: candidates that import this axiom only get Wang's `(15)`
at the published seed `c`, regardless of how the candidate defines
its own `c_value`. Combined with the parse-time gate in
`ShinkaAblation/evaluate.py` (which rejects any candidate that
declares a fresh `axiom`), this prevents the LLM from re-deriving
the cheat by redeclaring the axiom locally with a different type.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) :
    Eq15ScalarBound K ((3554 : ℝ) / 10000)

end ProofRefinement.Korenblum.ShinkaTrustedSeed
