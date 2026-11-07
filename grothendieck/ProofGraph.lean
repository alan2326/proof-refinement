/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ProofGraph — root module

Aggregates the effective companion theorems that bridge the Lean
formalization (`LeanProof/`, `ProofRefinement/Lemma54/`) with the
certified-arb pipeline (`grothendieck/proof/certified/`).

See `docs/PROOF_GRAPH_DESIGN.md` for the full design.
-/

import ProofGraph.Effective.Lemma54Effective
import ProofGraph.Effective.Lemma54PaperBridge
import ProofGraph.Effective.Lemma53Effective
import ProofGraph.Effective.Theorem44Effective
import ProofGraph.Effective.Theorem51PaperEffective
import ProofGraph.Effective.Theorem51Effective
import ProofGraph.Effective.KGBound
