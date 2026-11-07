"""sprint_013 BLOCKER analysis — the contract's mathematical premise is wrong.

The contract claims that the recentred Cauchy radius can be lifted from
(1-r)/2 to (1-r)·k for any k < 1 (e.g. k = 9/10), based on the assertion
that "the recentered ball still lies inside disk r₁ = ball 0 1".

This is false. The actual analyticity domain of `F_inv_paper` is
`disk (r1 r) = ball 0 ((1+r)/2)`, NOT `ball 0 1`. The axiom
`F_inv_paper_analytic` (Lemma54_Paper.lean line 297) provides analyticity
on `disk (r1 r)` only.

Definitions:
    disk r        := Metric.ball (0 : ℂ) r          (LeanProof/Defs/Strip.lean:26)
    r1 r          := (1 + r) / 2                    (Lemma54_Paper.lean:56)

So `disk (r1 r) = ball 0 ((1+r)/2)` — radius (1+r)/2, NOT 1.

The recentred ball at z₀ ∈ disk r with radius ρ requires
    ‖z₀‖ + ρ < r1 r   (i.e., the recentred closedBall lies inside
                       the OPEN ball of radius r1 r).
Worst case ‖z₀‖ → r⁻, so we need
    r + ρ ≤ r1 r = (1+r)/2,
i.e., ρ ≤ (1+r)/2 - r = (1-r)/2.

The current radius (1-r)/2 is therefore ALREADY MAXIMAL, not conservative.
The contract's k = 9/10 corresponds to ρ = (1-r)·9/10, which would require
analyticity on a strictly larger disk. At V9 parameters (r = 23/25):
    Original radius: (1-r)/2 = 1/25 = 0.04
    Contract radius: (1-r)·(9/10) = 9/125 = 0.072
    Maximum (z₀ → r): r + ρ = 23/25 + 9/125 = 124/125 = 0.992
    But r1 r = (1+23/25)/2 = 24/25 = 0.96 < 0.992 ✗

I attempted the contract's edits and the Lean compiler immediately
flagged the broken triangle inequality at the `add_mem_disk_r1_phi2`
helper:
    > 1 < (1 + r) / 2   (i.e., 1 < r1 r)
which is FALSE for r < 1.

CONCLUSIONS:
1. The contract's "Mathematical insight" Sec 13's claim "disk r₁ = ball 0 1"
   is incorrect. r1 r = (1+r)/2, so disk r₁ = ball 0 ((1+r)/2).
2. The Cauchy step ‖u_zz‖ ≤ 8R/(1-r)² is OPTIMAL given the existing
   F_inv analyticity domain `disk (r1 r)`. There is no slack to exploit
   here without first ENLARGING the analyticity domain (which requires a
   new axiom or a refined IFT statement on `disk r₂` or larger).
3. To recover the contract's intent, one would need:
   (a) A new (larger) analyticity domain for F_inv — e.g.,
       `AnalyticOnNhd ℂ F_inv (disk (r2 r))` where r2 = (3+r)/4,
       which would permit recentred radius up to r2 r - r = (3-3r)/4 =
       3(1-r)/4. That gives a 3/2× lift on the Cauchy radius (vs the
       contract's claimed 9/5×), but the new analyticity claim is itself
       a new axiom — explicitly forbidden by the harness.
   (b) Or a *different* IFT axiom that bundles analyticity on a fully
       open extension. Same issue: new axiom required.

This is a structural blocker, not a tactical one. The contract's
direction is mathematically not achievable within the existing trust
base.
"""
from fractions import Fraction

r = Fraction(23, 25)
r1 = (1 + r) / 2
print(f"r       = {r} = {float(r)}")
print(f"r1 r    = {r1} = {float(r1)}")
print(f"Max recentred radius from disk(r) given disk(r1 r):")
print(f"  ρ_max = r1 r - r = {r1 - r} = {float(r1 - r)} = (1-r)/2 ✓")
print()
print(f"Contract claims k = 9/10 works.")
k = Fraction(9, 10)
rho_contract = (1 - r) * k
print(f"  ρ_contract = (1-r)·{k} = {rho_contract} = {float(rho_contract)}")
print(f"  Worst case z₀: ‖z₀+w‖ < r + ρ_contract = {r + rho_contract} = {float(r + rho_contract)}")
print(f"  Required: ‖z₀+w‖ < r1 r = {r1} = {float(r1)}")
print(f"  Feasible? {r + rho_contract <= r1}  (NO — recentred ball escapes analyticity domain)")
