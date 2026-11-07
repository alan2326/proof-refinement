import KorenblumProofSearch3.AnnulusIntegralReduction
import KorenblumProofSearch3.WangPaperSideConditions

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace KorenblumProofSearch3

namespace PaperAxioms

/-- Wang's branch split `sqrt(4/3) c`. -/
def branchSplit (c : ℝ) : ℝ :=
  c * Real.sqrt (4 / 3)

/-- The branch-1 coefficient kernel from Wang's equation `(5)`. -/
def branch1SigmaKernel (c ρ : ℝ) : ℝ :=
  c ^ 6 / (6 * ρ ^ 2 * (ρ ^ 2 - c ^ 2))

/-- The branch-2 coefficient kernel from Wang's equation `(6)`. -/
def branch2SigmaKernel (c ρ : ℝ) : ℝ :=
  c ^ 4 / (2 * ρ ^ 2)

/-- The pointwise factor in Wang's equation `(10)`. -/
def branch1PointwiseFactor (c : ℝ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  6 * ρ ^ 2 * (ρ ^ 2 - c ^ 2) / (c ^ 6 * Λ ρ)

/-- The pointwise factor in Wang's equation `(11)`. -/
def branch2PointwiseFactor (c : ℝ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  2 * ρ ^ 2 / (c ^ 4 * Λ ρ)

/-- Wang's `N1 = {k ∈ N : |a_k| ≥ |b_k|} ∪ {0}`. -/
def n1Pred (a b : ℕ → ℂ) (k : ℕ) : Prop :=
  k = 0 ∨ ‖a k‖ ≥ ‖b k‖

/-- Wang's `N2 = {k ∈ N : |a_k| < |b_k|}`. -/
def n2Pred (a b : ℕ → ℂ) (k : ℕ) : Prop :=
  0 < k ∧ ‖a k‖ < ‖b k‖

/-- The coefficient gap `|a_k|^2 - |b_k|^2`. -/
def coeffPlusGap (a b : ℕ → ℂ) (k : ℕ) : ℝ :=
  ‖a k‖ ^ 2 - ‖b k‖ ^ 2

/-- The coefficient gap `|b_k|^2 - |a_k|^2`. -/
def coeffMinusGap (a b : ℕ → ℂ) (k : ℕ) : ℝ :=
  ‖b k‖ ^ 2 - ‖a k‖ ^ 2

/--
Wang's definition

`Σ⁺(s) = ∑_{k∈N1} (|a_k|^2 - |b_k|^2) s^(2k)`.
-/
def sigmaPlus (a b : ℕ → ℂ) (s : ℝ) : ℝ :=
  by
    classical
    exact ∑' k : ℕ, if n1Pred a b k then coeffPlusGap a b k * s ^ (2 * k) else 0

/--
Wang's definition

`Σ⁻(s) = ∑_{k∈N2} (|b_k|^2 - |a_k|^2) s^(2k)`.
-/
def sigmaMinus (a b : ℕ → ℂ) (s : ℝ) : ℝ :=
  by
    classical
    exact ∑' k : ℕ, if n2Pred a b k then coeffMinusGap a b k * s ^ (2 * k) else 0

/--
Wang's definition

`Σ⁻₀(s) = ∑_{k∈N2} (|b_k|^2 - |a_k|^2) s^(2k-2)`.
-/
def sigmaZeroMinus (a b : ℕ → ℂ) (s : ℝ) : ℝ :=
  by
    classical
    exact ∑' k : ℕ, if n2Pred a b k then coeffMinusGap a b k * s ^ (2 * k - 2) else 0

/--
The normalized circle excess appearing on the left side of Wang's equation `(3)`.
-/
def circleGapSeries (a b : ℕ → ℂ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, coeffPlusGap a b k * r ^ (2 * k)

/--
The concrete Section 2 circle-gap quantity attached to the coefficient data.

This is Wang's normalized boundary excess

`(1 / (2π)) ∫ (|g(ρe^{iθ})|^2 - |f(ρe^{iθ})|^2) dθ`,

expressed via the coefficient series from equation `(3)`.
-/
def circleGap (a b : ℕ → ℂ) : ℝ → ℝ :=
  circleGapSeries a b

/--
The concrete lifted-gap series appearing on the right side of Wang's equation
`(8)` for a chosen scale parameter `scale ρ = a(ρ)`.

This is the coefficient-side expression corresponding to

`(1 / (2π)) ∫ |g(ρe^{iθ}) - a(ρ) f(ρe^{iθ})|^2 / (1 - a(ρ)^2) dθ`.
-/
def liftGapSeries
    (a b : ℕ → ℂ)
    (scale : ℝ → ℝ)
    (ρ : ℝ) : ℝ :=
  ∑' k : ℕ, (‖b k - (scale ρ : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)) / (1 - scale ρ ^ 2)

/--
Wang's displayed equation `(2)`.
-/
def Eq2SigmaZeroMinusLower
    (sigmaZeroMinus : ℝ → ℝ)
    (r c ρ : ℝ) : Prop :=
  sigmaZeroMinus r ≥
    ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * sigmaZeroMinus c -
      ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * sigmaZeroMinus ρ

/--
Wang's displayed equation `(3)`.
-/
def Eq3CircleGapDecomposition
    (circleGap sigmaPlus sigmaZeroMinus : ℝ → ℝ)
    (r : ℝ) : Prop :=
  circleGap r = sigmaPlus r - r ^ 2 * sigmaZeroMinus r

/--
Wang's displayed equation `(4)`.
-/
def Eq4SigmaPlusBound
    (sigmaPlus sigmaMinus sigmaZeroMinus : ℝ → ℝ)
    (r c : ℝ) : Prop :=
  sigmaPlus r ≤ sigmaPlus c ∧
    sigmaPlus c ≤ sigmaMinus c ∧
    sigmaMinus c = c ^ 2 * sigmaZeroMinus c

/--
Wang's equation `(5)`, with `innerExcess` denoting the paper integral over
`D(c)` and `sigmaMinus ρ` denoting `Σ⁻(ρ)`.
-/
def Eq5Branch1SigmaReduction
    (c innerExcess : ℝ)
    (sigmaMinus : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < branchSplit c →
    innerExcess ≤ branch1SigmaKernel c ρ * sigmaMinus ρ

/--
Wang's equation `(6)`, with `innerExcess` denoting the paper integral over
`D(c)` and `sigmaMinus ρ` denoting `Σ⁻(ρ)`.
-/
def Eq6Branch2SigmaReduction
    (c innerExcess : ℝ)
    (sigmaMinus : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, branchSplit c < ρ → ρ < 1 →
    innerExcess ≤ branch2SigmaKernel c ρ * sigmaMinus ρ

/--
Wang's displayed product formula `(7)` for the kernel quantity `K(c, ρ)`.

This is the exact paper-side interface currently implemented by
`WangKernelExact.PaperKFormula`.
-/
def Eq7PaperKFormula
    (K : ℝ → ℝ → ℝ)
    (c : ℝ) : Prop :=
  WangKernelExact.PaperKFormula K c

/--
Wang's equation `(8)`, with `sigmaMinus ρ = Σ⁻(ρ)` and `liftGap ρ` denoting
the normalized circle integral

`(1 / (2π)) ∫ |g(ρe^{iθ}) - a f(ρe^{iθ})|^2 / (1 - a^2) dθ`.
-/
def Eq8SigmaToLiftGap
    (c : ℝ)
    (sigmaMinus liftGap : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 → sigmaMinus ρ ≤ liftGap ρ

/--
Wang's equation `(9)`, with `liftGap ρ` denoting the normalized integral from
equation `(8)` and `circleGap ρ` denoting the normalized boundary excess

`(1 / (2π)) ∫ (|g(ρe^{iθ})|^2 - |f(ρe^{iθ})|^2) dθ`.
-/
def Eq9LiftGapToCircleGap
    (K : ℝ → ℝ → ℝ)
    (c : ℝ)
    (liftGap circleGap : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
    liftGap ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ

/-- Wang's printed equation `(10)`. -/
def Eq10Branch1Pointwise
    (K : ℝ → ℝ → ℝ)
    (c innerExcess : ℝ)
    (circleGap : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < branchSplit c →
    branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess ≤ circleGap ρ

/-- Wang's printed equation `(11)`. -/
def Eq11Branch2Pointwise
    (K : ℝ → ℝ → ℝ)
    (c innerExcess : ℝ)
    (circleGap : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, branchSplit c < ρ → ρ < 1 →
    branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess ≤ circleGap ρ

/--
Wang's printed equation `(12)`, with `innerExcess` denoting the paper integral
over `D(c)` and `annulusLeftExcess` denoting the paper integral over the left
annulus slice `c ≤ |z| < sqrt(4/3) c`.
-/
def Eq12Branch1Integrated
    (K : ℝ → ℝ → ℝ)
    (c innerExcess annulusLeftExcess : ℝ) : Prop :=
  (∫ ρ in c..branchSplit c, Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) *
      innerExcess ≤ annulusLeftExcess

/--
Wang's printed equation `(13)`, with `innerExcess` denoting the paper integral
over `D(c)` and `annulusRightExcess` denoting the paper integral over the right
annulus slice `sqrt(4/3) c ≤ |z| < 1`.
-/
def Eq13Branch2Integrated
    (K : ℝ → ℝ → ℝ)
    (c innerExcess annulusRightExcess : ℝ) : Prop :=
  (∫ ρ in branchSplit c..1, Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) *
      innerExcess ≤ annulusRightExcess

/--
Wang's printed equation `(14)`, with `annulusExcess` denoting the paper integral
over `A(c,1)`.
-/
def Eq14Combined
    (K : ℝ → ℝ → ℝ)
    (c innerExcess annulusExcess : ℝ) : Prop :=
  Korenblum.scalarCriterion c (WangOuter.paperLambda K c) * innerExcess ≤ annulusExcess

/--
Wang's displayed scalar inequality `(15)`. This is a definition, not an axiom:
future candidates are expected to prove it in Lean.
-/
def Eq15ScalarBound
    (K : ℝ → ℝ → ℝ)
    (c : ℝ) : Prop :=
  1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c)

/--
The paper integral over `D(c)`, expressed as the radial integral of the circle
gap.
-/
def diskExcess (circleGap : ℝ → ℝ) (c : ℝ) : ℝ :=
  AnnulusIntegralReduction.annulusSlice circleGap 0 c

/--
The paper integral over `c ≤ |z| < sqrt(4/3) c`.
-/
def annulusLeftExcess (circleGap : ℝ → ℝ) (c : ℝ) : ℝ :=
  AnnulusIntegralReduction.annulusSlice circleGap c (branchSplit c)

/--
The paper integral over `sqrt(4/3) c ≤ |z| < 1`.
-/
def annulusRightExcess (circleGap : ℝ → ℝ) (c : ℝ) : ℝ :=
  AnnulusIntegralReduction.annulusSlice circleGap (branchSplit c) 1

/--
The paper integral over `A(c,1)`.
-/
def annulusExcess (circleGap : ℝ → ℝ) (c : ℝ) : ℝ :=
  AnnulusIntegralReduction.annulusSlice circleGap c 1

/--
Fixed paper objects used in Wang's Section 2 argument.

These are intentionally bundled into a structure rather than introduced as
global axioms over arbitrary functions. This prevents the paper equations from
being instantiated against unrelated placeholders.
-/
structure Section2Objects
    (a b : ℕ → ℂ)
    (K : ℝ → ℝ → ℝ)
    (c : ℝ) where
  /--
  The paper lifted-gap quantity from equation `(8)`:

  `(1 / (2π)) ∫ |g(ρe^{iθ}) - a(ρ) f(ρe^{iθ})|^2 / (1 - a(ρ)^2) dθ`.
  -/
  liftGap : ℝ → ℝ

/-- The concrete circle-gap function attached to a Section 2 context. -/
def Section2Objects.circleGap
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    {c : ℝ}
    (_paper : Section2Objects a b K c) : ℝ → ℝ :=
  PaperAxioms.circleGap a b

/--
Section 2 assumptions from Wang's paper, attached to a fixed family of paper
objects.

This is the corrected replacement for the old global axiom surface: the paper
equations are now hypotheses about the specific objects used in the argument,
not universally quantified facts about arbitrary functions.
-/
structure Section2Assumptions
    (a b : ℕ → ℂ)
    (K : ℝ → ℝ → ℝ)
    (c : ℝ)
    extends Section2Objects a b K c where
  /-- Wang's displayed kernel product formula `(7)`. -/
  eq7_paperK_formula :
    Eq7PaperKFormula K c
  /-- Paper equation `(2)`. -/
  eq2_sigmaZeroMinus_lower :
    ∀ {r ρ : ℝ},
      0 ≤ r →
      r < c →
      c < ρ →
      ρ < 1 →
      Eq2SigmaZeroMinusLower (sigmaZeroMinus a b) r c ρ
  /-- Paper equation `(3)`. -/
  eq3_circleGap_decomposition :
    ∀ {r : ℝ},
      0 ≤ r →
      r < 1 →
      Eq3CircleGapDecomposition (PaperAxioms.circleGap a b) (sigmaPlus a b) (sigmaZeroMinus a b) r
  /-- Paper equation `(4)`. -/
  eq4_sigmaPlus_bound :
    ∀ {r : ℝ},
      0 ≤ r →
      r < c →
      c < 1 →
      Eq4SigmaPlusBound (sigmaPlus a b) (sigmaMinus a b) (sigmaZeroMinus a b) r c
  /-- Paper equation `(5)`. -/
  eq5_branch1_sigmaReduction :
    Eq5Branch1SigmaReduction c (diskExcess (PaperAxioms.circleGap a b) c) (sigmaMinus a b)
  /-- Paper equation `(6)`. -/
  eq6_branch2_sigmaReduction :
    Eq6Branch2SigmaReduction c (diskExcess (PaperAxioms.circleGap a b) c) (sigmaMinus a b)
  /-- Paper equation `(8)`. -/
  eq8_sigma_to_liftGap :
    Eq8SigmaToLiftGap c (sigmaMinus a b) liftGap
  /-- Paper equation `(9)`. -/
  eq9_liftGap_to_circleGap :
    Eq9LiftGapToCircleGap K c liftGap (PaperAxioms.circleGap a b)
  /-- Paper equation `(10)`. -/
  eq10_branch1_pointwise :
    Eq10Branch1Pointwise K c (diskExcess (PaperAxioms.circleGap a b) c) (PaperAxioms.circleGap a b)
  /-- Paper equation `(11)`. -/
  eq11_branch2_pointwise :
    Eq11Branch2Pointwise K c (diskExcess (PaperAxioms.circleGap a b) c) (PaperAxioms.circleGap a b)
  /-- Paper equation `(12)`. -/
  eq12_branch1_integrated :
    Eq12Branch1Integrated K c (diskExcess (PaperAxioms.circleGap a b) c) (annulusLeftExcess (PaperAxioms.circleGap a b) c)
  /-- Paper equation `(13)`. -/
  eq13_branch2_integrated :
    Eq13Branch2Integrated K c (diskExcess (PaperAxioms.circleGap a b) c) (annulusRightExcess (PaperAxioms.circleGap a b) c)
  /-- Paper equation `(14)`. -/
  eq14_combined :
    Eq14Combined K c (diskExcess (PaperAxioms.circleGap a b) c) (annulusExcess (PaperAxioms.circleGap a b) c)

/-- Derived convenience bridge from the printed equations `(8)` and `(9)`. -/
def Eq8Eq9SigmaToCircleBridge
    (K : ℝ → ℝ → ℝ)
    (c : ℝ)
    (sigmaMinus circleGap : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
    sigmaMinus ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ

/--
Pure Lean composition of Wang's printed equations `(8)` and `(9)`.
-/
theorem eq8eq9_sigma_to_circleBridge_of_eq8_eq9
    {K : ℝ → ℝ → ℝ}
    {c : ℝ}
    {sigmaMinus liftGap circleGap : ℝ → ℝ}
    (h8 : Eq8SigmaToLiftGap c sigmaMinus liftGap)
    (h9 : Eq9LiftGapToCircleGap K c liftGap circleGap) :
    Eq8Eq9SigmaToCircleBridge K c sigmaMinus circleGap := by
  intro ρ hcr hρ1
  exact le_trans (h8 hcr hρ1) (h9 hcr hρ1)

/--
Pure Lean derivation of Wang's equation `(10)` from printed equations `(5)`,
`(8)`, and `(9)`.
-/
theorem eq10_of_eq5_eq8_eq9
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    {sigmaMinus liftGap circleGap : ℝ → ℝ}
    (hc : 0 < c)
    (hsplit1 : branchSplit c < 1)
    (h5 : Eq5Branch1SigmaReduction c innerExcess sigmaMinus)
    (h8 : Eq8SigmaToLiftGap c sigmaMinus liftGap)
    (h9 : Eq9LiftGapToCircleGap K c liftGap circleGap) :
    Eq10Branch1Pointwise K c innerExcess circleGap := by
  intro ρ hcr hρ
  have hρ1 : ρ < 1 := lt_trans hρ hsplit1
  have h5ρ : innerExcess ≤ branch1SigmaKernel c ρ * sigmaMinus ρ := h5 hcr hρ
  have h89ρ : sigmaMinus ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ :=
    eq8eq9_sigma_to_circleBridge_of_eq8_eq9 h8 h9 hcr hρ1
  have hρpos : 0 < ρ := lt_trans hc hcr
  have hDiffPos : 0 < ρ ^ 2 - c ^ 2 := by
    nlinarith
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hFactorNonneg : 0 ≤ branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ := by
    unfold branch1PointwiseFactor
    positivity
  have hc6 : c ^ 6 ≠ 0 := by positivity
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  have hDiff : ρ ^ 2 - c ^ 2 ≠ 0 := ne_of_gt hDiffPos
  have hΛ : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hFactorKernel :
      branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ *
        branch1SigmaKernel c ρ =
        1 / WangOuter.paperLambda K c ρ := by
    unfold branch1PointwiseFactor branch1SigmaKernel
    field_simp [hc6, hρ2, hDiff, hΛ]
  have hScaled :
      branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        sigmaMinus ρ / WangOuter.paperLambda K c ρ := by
    calc
      branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess
          ≤ branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ *
              (branch1SigmaKernel c ρ * sigmaMinus ρ) := by
              exact mul_le_mul_of_nonneg_left h5ρ hFactorNonneg
      _ = (branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ *
            branch1SigmaKernel c ρ) * sigmaMinus ρ := by ring
      _ = (1 / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
        rw [hFactorKernel]
      _ = sigmaMinus ρ / WangOuter.paperLambda K c ρ := by ring
  have hDiv :
      sigmaMinus ρ / WangOuter.paperLambda K c ρ ≤ circleGap ρ := by
    exact (div_le_iff₀ hΛpos).2 (by simpa [mul_comm] using h89ρ)
  exact le_trans hScaled hDiv

/--
Pure Lean derivation of Wang's equation `(11)` from printed equations `(6)`,
`(8)`, and `(9)`.
-/
theorem eq11_of_eq6_eq8_eq9
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    {sigmaMinus liftGap circleGap : ℝ → ℝ}
    (hc : 0 < c)
    (h6 : Eq6Branch2SigmaReduction c innerExcess sigmaMinus)
    (h8 : Eq8SigmaToLiftGap c sigmaMinus liftGap)
    (h9 : Eq9LiftGapToCircleGap K c liftGap circleGap) :
    Eq11Branch2Pointwise K c innerExcess circleGap := by
  intro ρ hρ hρ1
  have hsqrt : 1 < Real.sqrt (4 / 3) := by
    have hsq : (1 : ℝ) ^ 2 < 4 / 3 := by norm_num
    have hsqrt_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (4 / 3), hsqrt_sq, hsq]
  have hsplit : c < branchSplit c := by
    unfold branchSplit
    nlinarith
  have hcr : c < ρ := lt_trans hsplit hρ
  have h6ρ : innerExcess ≤ branch2SigmaKernel c ρ * sigmaMinus ρ := h6 hρ hρ1
  have h89ρ : sigmaMinus ρ ≤ WangOuter.paperLambda K c ρ * circleGap ρ :=
    eq8eq9_sigma_to_circleBridge_of_eq8_eq9 h8 h9 hcr hρ1
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hFactorNonneg : 0 ≤ branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ := by
    unfold branch2PointwiseFactor
    positivity
  have hc4 : c ^ 4 ≠ 0 := by positivity
  have hρne : ρ ≠ 0 := ne_of_gt (lt_trans hc hcr)
  have hΛ : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hFactorKernel :
      branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ *
        branch2SigmaKernel c ρ =
        1 / WangOuter.paperLambda K c ρ := by
    unfold branch2PointwiseFactor branch2SigmaKernel
    field_simp [hc4, hρne, hΛ]
  have hScaled :
      branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess ≤
        sigmaMinus ρ / WangOuter.paperLambda K c ρ := by
    calc
      branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ * innerExcess
          ≤ branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ *
              (branch2SigmaKernel c ρ * sigmaMinus ρ) := by
              exact mul_le_mul_of_nonneg_left h6ρ hFactorNonneg
      _ = (branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ *
            branch2SigmaKernel c ρ) * sigmaMinus ρ := by ring
      _ = (1 / WangOuter.paperLambda K c ρ) * sigmaMinus ρ := by
        rw [hFactorKernel]
      _ = sigmaMinus ρ / WangOuter.paperLambda K c ρ := by ring
  have hDiv :
      sigmaMinus ρ / WangOuter.paperLambda K c ρ ≤ circleGap ρ := by
    exact (div_le_iff₀ hΛpos).2 (by simpa [mul_comm] using h89ρ)
  exact le_trans hScaled hDiv

end PaperAxioms

end KorenblumProofSearch3
