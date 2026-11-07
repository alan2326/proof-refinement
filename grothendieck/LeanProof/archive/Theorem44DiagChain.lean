/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core

/-!
# Theorem 4.4 Diagonal chain rule

Only the order-2 and order-4 diagonal formulas for Φ(η) = F44(η,η).

## Strategy (from the plan)
1. Define g(η) = F44(η,η)
2. Prove first derivative formula for g
3. Differentiate again for order 2
4. Push to order 4

## What NOT to do
- Do not prove a general nth-order diagonal chain rule
- Do not prove a fully abstract theorem for all smooth symmetric F
- Only expand orders 2 and 4
-/


open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## C1. Order 2 diagonal formula -/

/-- d²/dη² F44(η,η)|₀ = 2·(∂²F44/∂u₁²)(0,0) + 2·(∂²F44/∂u₁∂u₂)(0,0).
    Uses the chain rule for η ↦ F44(η,η) and F44_swap to identify
    (∂²F44/∂u₂²)(0,0) = (∂²F44/∂u₁²)(0,0). -/
theorem Phi_iteratedDeriv2_formula :
    iteratedDeriv 2 (fun η => F44 η η) 0 =
      2 * d20_F44 0 0 + 2 * d11_F44 0 0 := by
  sorry

/-! ## C2. Order 4 diagonal formula -/

/-- d⁴/dη⁴ F44(η,η)|₀ = 2·d40 + 8·d13 + 6·d22.
    The full multinomial expansion of order 4 for η ↦ F44(η,η),
    using F44_swap to reduce the number of independent terms. -/
theorem Phi_iteratedDeriv4_formula :
    iteratedDeriv 4 (fun η => F44 η η) 0 =
      2 * d40_F44 0 0 + 8 * d13_F44 0 0 + 6 * d22_F44 0 0 := by
  sorry

end Braverman
