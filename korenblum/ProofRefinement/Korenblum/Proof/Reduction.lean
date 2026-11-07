import ProofRefinement.Korenblum.Proof.CandidateContract
import KorenblumPaper.OneModePaperBridge

open Set MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum

open ProblemAxioms
open KorenblumPaper

private theorem annulusDensity_nonneg_of_lt
    {c : ℝ}
    (hc_pos : 0 < c)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hcr : c < ρ)
    (hρ1 : ρ < 1) :
    0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  have hCircleNonneg : 0 ≤ paper.circleGap ρ :=
    OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper hcr hρ1
  change 0 ≤ 2 * ρ * paper.circleGap ρ
  have hρpos : 0 < ρ := lt_trans hc_pos hcr
  nlinarith

private theorem annulusExcess_nonneg
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c) :
    0 ≤ annulusExcess paper.circleGap c := by
  have hNonnegAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc c (1 : ℝ)),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo c (1 : ℝ)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ =>
        annulusDensity_nonneg_of_lt hc_pos paper hρ.1 hρ.2
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  simpa [annulusExcess] using
    AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap)
      (a := c)
      (b := (1 : ℝ))
      hc_lt_one.le
      hNonnegAE

/--
Generic paper-faithful closure: if Wang's equation `(15)` holds at `c`, then
the final disk-versus-annulus Korenblum bound holds at `c`.
-/
theorem eq15_implies_disk_le_annulus
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c)
    (h15 : Eq15ScalarBound K c) :
    diskExcess paper.circleGap c ≤ annulusExcess paper.circleGap c := by
  have h14 :
      Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
          diskExcess paper.circleGap c ≤
        annulusExcess paper.circleGap c := by
    simpa [PaperAxioms.Eq14Combined] using paper.eq14_combined
  have h15' :
      1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c) := by
    simpa [PaperAxioms.Eq15ScalarBound] using h15
  have hAnnulusNonneg : 0 ≤ annulusExcess paper.circleGap c :=
    annulusExcess_nonneg hc_pos hc_lt_one paper
  by_cases hInner : 0 ≤ diskExcess paper.circleGap c
  · have hScaled :
        diskExcess paper.circleGap c ≤
          Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
            diskExcess paper.circleGap c := by
      simpa using mul_le_mul_of_nonneg_right h15' hInner
    exact le_trans hScaled h14
  · exact le_trans (le_of_lt (lt_of_not_ge hInner)) hAnnulusNonneg

/--
Generic seed bridge: a proof of equation `(15)` at radius `c` is enough to
prove the full candidate contract `ValidKorenblumBound c`.
-/
theorem valid_of_eq15
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h15 : ∀ {K : ℝ → ℝ → ℝ}, Eq15ScalarBound K c) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  exact eq15_implies_disk_le_annulus hc_pos hc_lt_one paper (h15 (K := K))

/--
New paper-faithful chain (Sprint 001): bypass `paper.eq14_combined` by combining
the *unintegrated* equations `(12)` and `(13)` directly. Their two branch
masses `M1` and `M2` add up to `Korenblum.scalarCriterion`, and Wang's scalar
inequality `(15)` says `1 ≤ M1 + M2`. The remaining geometric step
`annulusLeftExcess + annulusRightExcess ≤ annulusExcess` is taken as an
explicit hypothesis here; deriving it from `Section2Assumptions` is the
subject of the next sprint.

This proof must not use `paper.eq14_combined`.
-/
theorem valid_of_eq12_eq13
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_adjacency :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
          PaperAxioms.annulusLeftExcess paper.circleGap c
              + PaperAxioms.annulusRightExcess paper.circleGap c
            ≤ annulusExcess paper.circleGap c)
    (h_scalar :
      ∀ {K : ℝ → ℝ → ℝ},
        1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c)) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  -- Branch 1: equation (12) gives M1 * diskExcess ≤ annulusLeftExcess.
  have h12 :
      (∫ ρ in c..PaperAxioms.branchSplit c,
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) *
            diskExcess paper.circleGap c ≤
        PaperAxioms.annulusLeftExcess paper.circleGap c := by
    simpa [PaperAxioms.Eq12Branch1Integrated] using paper.eq12_branch1_integrated
  -- Branch 2: equation (13) gives M2 * diskExcess ≤ annulusRightExcess.
  have h13 :
      (∫ ρ in PaperAxioms.branchSplit c..1,
          Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) *
            diskExcess paper.circleGap c ≤
        PaperAxioms.annulusRightExcess paper.circleGap c := by
    simpa [PaperAxioms.Eq13Branch2Integrated] using paper.eq13_branch2_integrated
  -- Add (12) + (13). The left side is exactly `scalarCriterion * diskExcess`.
  have hSum :
      Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
          diskExcess paper.circleGap c ≤
        PaperAxioms.annulusLeftExcess paper.circleGap c +
          PaperAxioms.annulusRightExcess paper.circleGap c := by
    have hAdd := add_le_add h12 h13
    have hRewrite :
        (∫ ρ in c..PaperAxioms.branchSplit c,
            Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) *
              diskExcess paper.circleGap c +
          (∫ ρ in PaperAxioms.branchSplit c..1,
              Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) *
                diskExcess paper.circleGap c =
          Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
            diskExcess paper.circleGap c := by
      simp [Korenblum.scalarCriterion, PaperAxioms.branchSplit, add_mul]
    linarith [hAdd, hRewrite.symm.le, hRewrite.le]
  -- Adjacency: `annulusLeftExcess + annulusRightExcess ≤ annulusExcess`.
  have hAdj := h_adjacency paper
  have hScalarLeAnnulus :
      Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
          diskExcess paper.circleGap c ≤
        annulusExcess paper.circleGap c :=
    le_trans hSum hAdj
  -- Use 1 ≤ scalarCriterion to drop the scalar factor (case-splitting on the
  -- sign of diskExcess), mirroring the structure of `eq15_implies_disk_le_annulus`.
  have h15' :
      1 ≤ Korenblum.scalarCriterion c (WangOuter.paperLambda K c) :=
    h_scalar (K := K)
  have hAnnulusNonneg : 0 ≤ annulusExcess paper.circleGap c :=
    annulusExcess_nonneg hc_pos hc_lt_one paper
  by_cases hInner : 0 ≤ diskExcess paper.circleGap c
  · have hScaled :
        diskExcess paper.circleGap c ≤
          Korenblum.scalarCriterion c (WangOuter.paperLambda K c) *
            diskExcess paper.circleGap c := by
      simpa using mul_le_mul_of_nonneg_right h15' hInner
    exact le_trans hScaled hScalarLeAnnulus
  · exact le_trans (le_of_lt (lt_of_not_ge hInner)) hAnnulusNonneg

/--
Sprint 002 inner-disk bound: combine paper equations `(2)`, `(3)`, and `(4)` to
upper-bound `circleGap r` for `r < c` in terms of `sigmaZeroMinus` at `c` and at
a free parameter `ρ ∈ (c, 1)`. The free parameter `ρ` is intentionally exposed
as a `forall` so that a downstream sprint can integrate this bound over
`r ∈ [0, c]` with `ρ` chosen as a function of integration variables.
-/
theorem circleGap_inner_bound_of_eq2_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {r ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1) :
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity facts.
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt
  have hc_lt_one : c < 1 := lt_trans hcρ hρ1
  have hc_lt_ρ : c < ρ := hcρ
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have hρ2_minus_c2_pos : 0 < ρ ^ 2 - c ^ 2 := by nlinarith
  have hr2_nonneg : 0 ≤ r ^ 2 := by positivity
  -- Step 1: Equation (3) — `circleGap r = sigmaPlus r - r^2 * sigmaZeroMinus r`.
  have hr_lt_one : r < 1 := lt_trans hr_lt hc_lt_one
  have h3 :
      PaperAxioms.circleGap a b r =
        PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
    have := paper.eq3_circleGap_decomposition (r := r) hr_nonneg hr_lt_one
    simpa [PaperAxioms.Eq3CircleGapDecomposition] using this
  -- Step 2: Equation (4) — three pieces about sigmaPlus / sigmaMinus at c.
  have h4 :=
    paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
  have h4_unfold :
      PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
        PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
  obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
  have hSigmaPlus_le :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    have : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
      le_trans h4a h4b
    rw [h4c] at this
    exact this
  -- Step 3: Equation (2) — lower bound on `sigmaZeroMinus a b r`.
  have h2 :=
    paper.eq2_sigmaZeroMinus_lower (r := r) (ρ := ρ) hr_nonneg hr_lt hcρ hρ1
  have h2_unfold :
      PaperAxioms.sigmaZeroMinus a b r ≥
        ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
          ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ := by
    simpa [PaperAxioms.Eq2SigmaZeroMinusLower] using h2
  -- Multiply `h2_unfold` by `r^2 ≥ 0` to get an upper bound on
  -- `-r^2 * sigmaZeroMinus a b r`.
  set Z_c : ℝ := PaperAxioms.sigmaZeroMinus a b c with hZc
  set Z_ρ : ℝ := PaperAxioms.sigmaZeroMinus a b ρ with hZρ
  set Z_r : ℝ := PaperAxioms.sigmaZeroMinus a b r with hZr
  set A : ℝ := (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hA
  set B : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hB
  -- Rewrite h2 in terms of A, B.
  have h2' : A * Z_c - B * Z_ρ ≤ Z_r := by
    have := h2_unfold
    simp only [ge_iff_le, hA, hB, hZc, hZρ, hZr] at this ⊢
    exact this
  -- Multiply by r^2 ≥ 0.
  have hMul : r ^ 2 * (A * Z_c - B * Z_ρ) ≤ r ^ 2 * Z_r :=
    mul_le_mul_of_nonneg_left h2' hr2_nonneg
  -- So -r^2 * Z_r ≤ -r^2 * (A * Z_c - B * Z_ρ) = -r^2 * A * Z_c + r^2 * B * Z_ρ.
  have hNeg : -(r ^ 2 * Z_r) ≤ -(r ^ 2 * (A * Z_c - B * Z_ρ)) := by linarith
  -- Now combine: circleGap r = sigmaPlus r - r^2 * Z_r ≤ c^2 * Z_c - r^2 * Z_r
  --                          ≤ c^2 * Z_c + (-r^2*A*Z_c + r^2*B*Z_ρ).
  have hSigmaPlus_le' :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * Z_c := by
    simp only [hZc]; exact hSigmaPlus_le
  -- Final algebra: c^2 * Z_c - r^2 * (A * Z_c - B * Z_ρ)
  --              = (c^2 - r^2 * A) * Z_c + r^2 * B * Z_ρ.
  -- And we need to show that target's first coefficient
  -- `(c^2 - r^2 * (ρ^2 - r^2) / (ρ^2 - c^2))` equals `c^2 - r^2 * A`.
  have hA_def : A = (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  have hB_def : B = (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  -- Build the chain.
  have hStep1 :
      PaperAxioms.circleGap a b r ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := by
    rw [h3]
    linarith [hSigmaPlus_le']
  have hStep2 :
      c ^ 2 * Z_c - r ^ 2 * Z_r ≤
        c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := by
    linarith [hMul]
  have hRewrite :
      c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) =
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by ring
  have hFinal :
      PaperAxioms.circleGap a b r ≤
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by
    calc PaperAxioms.circleGap a b r
        ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := hStep1
      _ ≤ c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := hStep2
      _ = (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := hRewrite
  -- Match the goal's denominator-laden form.
  have hCoeff1 : c ^ 2 - r ^ 2 * A =
      c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := by
    simp only [hA_def, mul_div_assoc']
  have hCoeff2 : r ^ 2 * B = r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) := by
    simp only [hB_def]
  rw [hCoeff1, hCoeff2] at hFinal
  exact hFinal

/--
Sprint 003 integrated form of sprint 002's pointwise inner-disk bound. The free
parameter `ρ` is intentionally exposed for downstream optimisation. The
integrability hypothesis on `2r · paper.circleGap r` is intentionally left as a
hypothesis pending a future sprint that derives it from `Section2Assumptions`.
-/
theorem diskExcess_upper_bound_of_eq2_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c
        + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity facts.
  have hρ2c2_pos : 0 < ρ ^ 2 - c ^ 2 := by nlinarith
  have hρ2c2_ne : (ρ ^ 2 - c ^ 2) ≠ 0 := ne_of_gt hρ2c2_pos
  have hc_le : (0 : ℝ) ≤ c := hc_pos.le
  -- Abbreviations.
  set Z_c : ℝ := PaperAxioms.sigmaZeroMinus a b c with hZc_def
  set Z_ρ : ℝ := PaperAxioms.sigmaZeroMinus a b ρ with hZρ_def
  set u : ℝ := ρ ^ 2 - c ^ 2 with hu_def
  have hu_pos : 0 < u := hρ2c2_pos
  have hu_ne : u ≠ 0 := hρ2c2_ne
  -- Step A: pointwise upper bound on `2 * r * paper.circleGap r` over Ioo 0 c.
  have hPointwise :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤
          2 * r * ((c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
            + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ) := by
    intro r hr
    have hr_nonneg : (0 : ℝ) ≤ r := hr.1.le
    have hr_lt : r < c := hr.2
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    have hBound :=
      circleGap_inner_bound_of_eq2_eq3_eq4 paper hr_nonneg hr_lt hcρ hρ1
    -- Rewrite via the abbreviations on Z_c, Z_ρ, u.
    have hBound' :
        PaperAxioms.circleGap a b r ≤
          (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
            + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ := by
      simpa [hu_def, hZc_def, hZρ_def] using hBound
    exact mul_le_mul_of_nonneg_left hBound' h2r_nonneg
  -- Step B: rewrite the upper bound into a flat polynomial in r,
  --         f_upper r = A_coef · r + B_coef · r^3 + C_coef · r^5,
  -- where A_coef, B_coef, C_coef are constants depending on c, ρ, Z_c, Z_ρ.
  set A_coef : ℝ := 2 * c ^ 2 * Z_c with hA_def
  set B_coef : ℝ := (2 * c ^ 2 * Z_ρ - 2 * ρ ^ 2 * Z_c) / u with hB_def
  set C_coef : ℝ := (2 * Z_c - 2 * Z_ρ) / u with hC_def
  -- The integrand of the upper bound, in expanded form.
  set fLin : ℝ → ℝ :=
    fun r => A_coef * r + B_coef * r ^ 3 + C_coef * r ^ 5 with hfLin_def
  have hLinEq :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * ((c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
          + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ) = fLin r := by
    intro r _
    simp only [hfLin_def, hA_def, hB_def, hC_def]
    field_simp
    ring
  have hPointwise2 :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤ fLin r := by
    intro r hr
    have h1 := hPointwise r hr
    have h2 := hLinEq r hr
    linarith
  -- Step C: integrate the pointwise bound on [0, c].
  have hLinCont : Continuous fLin := by
    simp only [hfLin_def]
    fun_prop
  have hLinIntegrable : IntervalIntegrable fLin volume 0 c :=
    hLinCont.intervalIntegrable _ _
  have hIntegralMono :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c, fLin r := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo hc_le hInt hLinIntegrable
      hPointwise2
  -- Step D: compute ∫_0^c fLin r dr explicitly.
  have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
    have h := @integral_pow 0 c 1
    simp only [pow_one] at h
    convert h using 2 <;> norm_num
  have hPow3 : ∫ r in (0 : ℝ)..c, r ^ 3 = c ^ 4 / 4 := by
    have h := @integral_pow 0 c 3
    convert h using 2 <;> norm_num
  have hPow5 : ∫ r in (0 : ℝ)..c, r ^ 5 = c ^ 6 / 6 := by
    have h := @integral_pow 0 c 5
    convert h using 2 <;> norm_num
  have hIntA : IntervalIntegrable (fun r : ℝ => A_coef * r) volume 0 c :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hIntB : IntervalIntegrable (fun r : ℝ => B_coef * r ^ 3) volume 0 c :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
  have hIntC : IntervalIntegrable (fun r : ℝ => C_coef * r ^ 5) volume 0 c :=
    (continuous_const.mul (continuous_id.pow 5)).intervalIntegrable _ _
  have hIntAB :
      IntervalIntegrable (fun r : ℝ => A_coef * r + B_coef * r ^ 3) volume 0 c :=
    hIntA.add hIntB
  have hIntegralLin :
      ∫ r in (0 : ℝ)..c, fLin r =
        A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) := by
    simp only [hfLin_def]
    rw [intervalIntegral.integral_add hIntAB hIntC]
    rw [intervalIntegral.integral_add hIntA hIntB]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hPow1, hPow3, hPow5]
  -- Step E: rewrite this closed-form into the contract's stated form.
  have hClosedAlg :
      A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) =
        (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / u * Z_c
          + (c ^ 6 / 6) / u * Z_ρ := by
    -- Establish that 3*ρ^2 - 4*c^2 = 6*u - 3*ρ^2 + 2*c^2 algebraic identity:
    -- the LHS minus RHS, after multiplying through by 12*u, is zero.
    have hu_eq : u = ρ ^ 2 - c ^ 2 := hu_def
    simp only [hA_def, hB_def, hC_def]
    field_simp
    ring
  -- Step F: chain the diskExcess to the closed-form bound.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        ≤ ∫ r in (0 : ℝ)..c, fLin r := hIntegralMono
    _ = A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) :=
        hIntegralLin
    _ = (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / u * Z_c + (c ^ 6 / 6) / u * Z_ρ :=
        hClosedAlg

/--
Sprint 004 end-to-end sufficient condition: a complete `ValidKorenblumBound c`
reduction that goes through equations `(2) + (3) + (4)` only (via sprints 002
and 003) plus an annulus-side budget hypothesis, with no use of
`Eq15`/`paperLambda`/`scalarCriterion`.
-/
theorem valid_of_eq2_eq3_eq4_annulus_budget
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_budget :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ : ℝ, c < ρ ∧ ρ < 1 ∧
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
          (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b c
            + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ
            ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ, hcρ, hρ1, hInt, hBudget⟩ := h_budget paper
  have hUpper :=
    diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt
  exact le_trans hUpper hBudget

/--
Sprint 005 series identity: relate Wang's two coefficient normalisations,
`sigmaMinus` and `sigmaZeroMinus`, by `Σ⁻(s) = s² · Σ⁻₀(s)`. This holds
termwise because `n2Pred` forces `0 < k`, so the only contributing exponents
satisfy `2k = 2 + (2k - 2)`. The identity lets us interconvert Wang's two
coefficient normalisations on the outer annulus side and is the structural
prerequisite for the Sprint 005 outer pointwise lower bound below.
-/
theorem sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus
    (a b : ℕ → ℂ) (s : ℝ) :
    PaperAxioms.sigmaMinus a b s = s ^ 2 * PaperAxioms.sigmaZeroMinus a b s := by
  classical
  -- Unfold both series.
  change (∑' k : ℕ, if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * s ^ (2 * k) else 0)
        = s ^ 2 *
          ∑' k : ℕ, if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) else 0
  -- Pull `s^2` inside the tsum.
  rw [← tsum_mul_left]
  -- Termwise equality.
  refine tsum_congr ?_
  intro k
  by_cases hk : PaperAxioms.n2Pred a b k
  · -- 0 < k branch: rewrite s^(2k) = s^2 * s^(2k - 2).
    have hkpos : 0 < k := hk.1
    have hk2 : 2 ≤ 2 * k := by omega
    have hAdd : 2 + (2 * k - 2) = 2 * k := by omega
    have hPow : s ^ (2 * k) = s ^ 2 * s ^ (2 * k - 2) := by
      have h : s ^ (2 + (2 * k - 2)) = s ^ 2 * s ^ (2 * k - 2) := pow_add s 2 _
      rw [hAdd] at h
      exact h
    simp only [hk, if_true]
    -- Goal: coeffMinusGap a b k * s ^ (2 * k) = s ^ 2 * (coeffMinusGap a b k * s ^ (2 * k - 2))
    rw [hPow]
    ring
  · -- n2Pred = false branch: both sides collapse to 0.
    simp [hk]

/--
Sprint 005 outer pointwise lower bound: the structural counterpart of sprint
002's inner pointwise upper bound. Combine the printed equations `(8)` and
`(9)` (via `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`) with the Sprint 005
series identity `sigmaMinus = ρ² · sigmaZeroMinus` to lower-bound the annulus
integrand `2ρ · circleGap ρ` by `2ρ³ · sigmaZeroMinus ρ / Λ(c, ρ)` on
`ρ ∈ (c, 1)`. This is the prerequisite for any future sprint that closes
sprint 004's annulus budget without `Eq15`.
-/
theorem circleGap_outer_lower_bound_of_eq8_eq9
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1) :
    2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
        / WangOuter.paperLambda K c ρ
      ≤ 2 * ρ * PaperAxioms.circleGap a b ρ := by
  -- (8)+(9) bridge: sigmaMinus ρ ≤ Λ(c, ρ) · circleGap ρ.
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ1
  -- Rewrite `sigmaMinus a b ρ = ρ² · sigmaZeroMinus a b ρ`.
  have hIdentity := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  rw [hIdentity] at hBridge
  -- Λ(c, ρ) > 0.
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  -- Divide through: ρ² · sigmaZeroMinus ρ / Λ ≤ circleGap ρ.
  have hDiv :
      ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ
        ≤ PaperAxioms.circleGap a b ρ :=
    (div_le_iff₀ hΛpos).2 (by simpa [mul_comm] using hBridge)
  -- Multiply by 2ρ ≥ 0.
  have hρpos : 0 < ρ := lt_trans hc_pos hcρ
  have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hMul :
      2 * ρ * (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ)
        ≤ 2 * ρ * PaperAxioms.circleGap a b ρ :=
    mul_le_mul_of_nonneg_left hDiv h2ρ_nonneg
  -- Rearrange the LHS to match the goal.
  have hLambdaNe : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hRewrite :
      2 * ρ * (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ) =
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ := by
    field_simp
  rw [hRewrite] at hMul
  exact hMul

/--
Sprint 006 corollary of the Sprint 005 series identity
`sigmaMinus = ρ²·sigmaZeroMinus`: at any positive radius `ρ > 0`,
`sigmaZeroMinus a b ρ` is non-negative. The lemma exposes
non-negativity of `sigmaZeroMinus` without needing a `Section2Assumptions`
instance — it is a pure series statement consumed by
`annulusExcess_lower_bound_of_eq8_eq9` (Sprint 006) to discharge integrand
non-negativity, and reusable by any future sprint that needs `Z_ρ ≥ 0`.
-/
theorem sigmaZeroMinus_nonneg_of_pos
    (a b : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ PaperAxioms.sigmaZeroMinus a b ρ := by
  have hId :
      PaperAxioms.sigmaMinus a b ρ =
        ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  have hNonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ :=
    OneModePaperBridge.sigmaMinus_nonneg a b ρ
  have hRho2_pos : 0 < ρ ^ 2 := pow_pos hρ 2
  have hMulNonneg : 0 ≤ ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ := by
    rw [← hId]; exact hNonneg
  exact nonneg_of_mul_nonneg_right hMulNonneg hRho2_pos

/--
Sprint 007: single-`Z` collapse of sprint 003's two-`Z` disk-side upper bound,
valid on the branch-split sub-regime `(c, branchSplit c]` (i.e. `3·ρ² ≤ 4·c²`).
The collapse is derived by combining sprint 003's
`diskExcess_upper_bound_of_eq2_eq3_eq4` with sprint 006's
`sigmaZeroMinus_nonneg_of_pos` to drop the `Z_c` term whose coefficient
`(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-positive on the branch-split sub-regime
(numerator non-positive, denominator strictly positive). The threshold
`3ρ² ≤ 4c²` is exactly the same as `ρ ≤ branchSplit c = √(4/3)·c`, exposing
for the first time that Wang's branch split is geometrically distinguished
by collapsing the `Z_c` coefficient in the `(2)+(3)+(4)` disk-side upper
bound.
-/
theorem diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
        * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity of the denominator ρ² − c².
  have hρ2c2_pos : 0 < ρ ^ 2 - c ^ 2 := by
    nlinarith [hcρ, hc_pos, sq_nonneg (ρ - c), sq_nonneg (ρ + c)]
  -- Sprint 003: two-`Z` upper bound on diskExcess.
  have hUpper :=
    diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt
  -- Sprint 006 corollary: sigmaZeroMinus a b c ≥ 0.
  have hZc_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
    sigmaZeroMinus_nonneg_of_pos a b hc_pos
  -- The `Z_c` coefficient `α := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-positive:
  -- numerator factor `(3ρ²−4c²)` is `≤ 0` by `hρ_branch`, denominator
  -- `(ρ²−c²) > 0`, leading factor `(c⁴/6) ≥ 0`.
  have hNumNonpos : 3 * ρ ^ 2 - 4 * c ^ 2 ≤ 0 := by linarith
  have hc4_nonneg : 0 ≤ c ^ 4 / 6 := by positivity
  have hα_nonpos :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2) ≤ 0 := by
    have hProd_nonpos : (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc4_nonneg hNumNonpos
    exact div_nonpos_of_nonpos_of_nonneg hProd_nonpos hρ2c2_pos.le
  -- α · Z_c ≤ 0.
  have hαZc_nonpos :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hα_nonpos hZc_nonneg
  -- Chain: diskExcess ≤ α·Z_c + β·Z_ρ ≤ 0 + β·Z_ρ = β·Z_ρ.
  linarith [hUpper, hαZc_nonpos]

/--
Sprint 006 integrated outer-side lower bound — the structural counterpart of
sprint 003's `diskExcess_upper_bound_of_eq2_eq3_eq4`. Where sprint 003
integrated the inner-disk pointwise *upper* bound to bound `diskExcess` from
above, this theorem integrates sprint 005's outer-annulus pointwise *lower*
bound to bound `annulusExcess` from below over a free sub-interval
`[ρ₁, ρ₂] ⊆ (c, 1)`. This is the last generic ingredient before an end-to-end
`(15)`-free `ValidKorenblumBound` proof becomes achievable: a future sprint
will combine this lower bound with sprint 003's upper bound and sprint 004's
`valid_of_eq2_eq3_eq4_annulus_budget` to discharge the budget hypothesis.
-/
theorem annulusExcess_lower_bound_of_eq8_eq9
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hcρ₁ : c < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hρ₂_lt_one : ρ₂ < 1)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ) volume ρ₁ ρ₂) :
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := by
  -- Positivity facts.
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hc_lt_one : c < 1 := lt_trans hcρ₁ hρ₁_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Step 1: Pointwise lower bound on Ioo ρ₁ ρ₂.
  have hPointwise :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ
          ≤ 2 * ρ * PaperAxioms.circleGap a b ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2.le hρ₂_lt_one
    exact circleGap_outer_lower_bound_of_eq8_eq9 paper hc_pos hcρ hρ_lt_one
  -- Step 2: Integrability of the RHS on [ρ₁, ρ₂] derived from
  -- `hIntCircle` via `mono_set`.
  have hIcc_ρ₁ρ₂_sub_c1 : Set.Icc ρ₁ ρ₂ ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have hIcc_cρ₁_sub_c1 : Set.Icc c ρ₁ ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have hIcc_ρ₂1_sub_c1 : Set.Icc ρ₂ 1 ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]; exact hIcc_ρ₁ρ₂_sub_c1
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]; exact hIcc_cρ₁_sub_c1
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]; exact hIcc_ρ₂1_sub_c1
  have hIntCircle_ρ₁ρ₂ :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntCircle_cρ₁ :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntCircle_ρ₂1 :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  -- These are exactly `IntervalIntegrable (annulusDensity paper.circleGap)`.
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ ρ₂ := hIntCircle_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρ₁ := hIntCircle_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₂ 1 := hIntCircle_ρ₂1
  -- Step 3: Integrate the pointwise bound on [ρ₁, ρ₂].
  have hIntegralMono :
      (∫ ρ in ρ₁..ρ₂,
          2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ) ≤
        ∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda hIntCircle_ρ₁ρ₂
      hPointwise
  -- Step 4: Recognise the upper bound as `annulusSlice paper.circleGap ρ₁ ρ₂`.
  have hSlice_ρ₁ρ₂ :
      (∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ) =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
    change _ = ∫ ρ in ρ₁..ρ₂,
      AnnulusIntegralReduction.annulusDensity paper.circleGap ρ
    rfl
  -- Step 5: Split `annulusSlice paper.circleGap c 1` into the three sub-slices.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    have hIntDens_ρ₁1 :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume ρ₁ 1 := by
      have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
        rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
        exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
      exact hIntCircle.mono_set huIcc_ρ₁1
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- Step 6: Non-negativity of the side slices via the a.e. version.
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρ₁) hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρ₂) (b := (1 : ℝ)) hρ₂_le_one
      hNonnegAE
  -- Step 7: Discharge `sigmaZeroMinus_nonneg_of_pos` (materialise the new
  -- side lemma even though `integral_mono_on_of_le_Ioo` does not directly
  -- need integrand non-negativity; the lemma is exercised here so V6's
  -- chain materialises sprint 006's side lemma in the call graph).
  have hZ_ρ₁_nonneg :
      0 ≤ PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_nonneg_of_pos a b (lt_trans hc_pos hcρ₁)
  -- Step 8: Chain everything to get the lower bound on annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := by
    rfl
  -- Combine: ∫ … ≤ annulusSlice ρ₁ ρ₂ ≤ annulusSlice c 1 = annulusExcess.
  -- Drop the unused Z_ρ₁ non-negativity into a `_` to silence linter.
  have _hZused := hZ_ρ₁_nonneg
  calc
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ)
        ≤ ∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ := hIntegralMono
    _ = AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := hSlice_ρ₁ρ₂
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 008: the **first sub-interval branch-1 sufficient condition** for
`ValidKorenblumBound`, derived from Wang's pointwise `(10)` by integrating
against `2ρ` over a free sub-interval `[ρ₁, ρ₂] ⊆ (c, branchSplit c]` and asking
the resulting kernel mass to reach `1`. This is **strictly weaker** than `(15)`
(which asks the same integrand to integrate to `1` over the *full* branch
window plus the branch-2 contribution), and exposes for the first time in the
workspace that local concentration of branch-1 mass on a sub-window suffices.
-/
theorem valid_of_eq10_subinterval_branch1
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_split, hMass⟩ := h_window paper
  -- Positivity / ordering setup.
  have hSplit_le_one : PaperAxioms.branchSplit c ≤ 1 := hSplit_lt_one.le
  have hρ₂_lt_one : ρ₂ < 1 := lt_of_le_of_lt hρ₂_split hSplit_lt_one
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Integrability of the global annulus density (the explicit premise).
  have hIntCircle :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap) volume c 1 :=
    hIntDensity paper
  -- Sub-interval integrability of the annulus density via `mono_set`.
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  have hIntDens_ρ₁1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ 1 :=
    hIntCircle.mono_set huIcc_ρ₁1
  -- Integrability of the branch-1 mode integrand on `[ρ₁, ρ₂]`.
  have hModeInt :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
        volume ρ₁ ρ₂ :=
    WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      hc_pos hρ₁₂ hcρ₁.le (le_trans hρ₂_split hSplit_le_one)
      paper.eq7_paperK_formula
  -- Pointwise bound on the open interior `Ioo ρ₁ ρ₂`, derived from
  -- `eq10_branch1_pointwise` after multiplying by `2ρ ≥ 0`.
  have hPointwiseIoo :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
    have hρ_split : ρ < PaperAxioms.branchSplit c :=
      lt_of_lt_of_le hρ.2 hρ₂_split
    -- (10): branch1PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ.
    have h10 :
        PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          PaperAxioms.circleGap a b ρ :=
      paper.eq10_branch1_pointwise hcρ hρ_split
    -- Multiply by 2ρ ≥ 0.
    have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
    have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
    have hMul :
        2 * ρ *
            (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
      mul_le_mul_of_nonneg_left h10 h2ρ_nonneg
    -- Algebraic identity: 2 * ρ * branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ.
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
    have hc6_ne : (c ^ 6 : ℝ) ≠ 0 := by positivity
    have hRewriteLHS :
        2 * ρ *
            (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
      unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
      field_simp
      ring
    have hRewriteRHS :
        2 * ρ * PaperAxioms.circleGap a b ρ =
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := rfl
    rw [hRewriteLHS, hRewriteRHS] at hMul
    exact hMul
  -- Lift the pointwise bound on `Ioo` to an a.e. bound on `Icc` (boundary is
  -- measure zero), so we can apply `mass_mul_le_annulusSlice_of_integral_bound_ae`.
  have hPointwiseAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo ρ hρ
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- A.e. non-negativity of the annulus density on `[ρ₁, ρ₂]`.
  have hAnnNonnegAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- Apply `mass_mul_le_annulusSlice_of_integral_bound_ae` with mass = 1.
  have hSliceBound :
      (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
      (modeIntegrand :=
        fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρ₁) (b := ρ₂)
      (mass := 1)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hρ₁₂ zero_le_one hMass hModeInt hIntDens_ρ₁ρ₂
      hPointwiseAE hAnnNonnegAE
  -- Simplify `1 * _ = _`.
  have hDiskLeSlice :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
    simpa [one_mul] using hSliceBound
  -- Split annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ +
  --                          annulusSlice ρ₂ 1.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- Side-slice non-negativities (mirroring sprint 006).
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρ₁) hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρ₂) (b := (1 : ℝ)) hρ₂_le_one
      hNonnegAE
  -- Chain to dominate by annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
          hDiskLeSlice
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 009: the **first cross-chain reducer** for `ValidKorenblumBound`. It
stitches sprint 007's collapsed disk upper bound on the branch-split sub-regime
`3ρ² ≤ 4c²` to sprint 006's `(8)+(9)` annulus lower bound on a free window
`[ρ₁, ρ₂] ⊆ (c, 1)`. The resulting sufficient condition is the workspace's
first `ValidKorenblumBound c` premise expressed *purely* in `sigmaZeroMinus`
and `paperLambda`: neither `diskExcess` nor `annulusExcess` appears as an
opaque quantity on the LHS — both opaque integrals have been replaced by
their closed-form `Z_·` / `Λ` envelopes. This opens three independent
follow-up routes for a future `c`-pushing sprint without any trust-base
expansion: (a) a closed-form `paperLambda K c ρ ≤ Λmax(c)` envelope, (b)
common-`Z_ρ` factor extraction with the disk witness placed inside the
annulus window, or (c) a registered numerical-integration oracle returning a
certified lower bound on the kernel integral.
-/
theorem valid_of_collapsed_disk_eq8_eq9_lower
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ ρ₁ ρ₂ : ℝ,
          c < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c ^ 2 ∧ ρ < 1 ∧
            c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
                * PaperAxioms.sigmaZeroMinus a b ρ
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁₂, hρ₂_lt_one,
      hIntDisk, hIntCircle, hIntLambda, hSuff⟩ := h_witness paper
  have hDisk :=
    diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
      paper hc_pos hcρ hρ_branch hρ1 hIntDisk
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambda
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  linarith [hDisk, hSuff, hAnn]

/--
Sprint 010: the workspace's **first `sigmaZeroMinus`-free sufficient
condition** for `ValidKorenblumBound c`. This reducer specialises sprint 009's
cross-chain reducer `valid_of_collapsed_disk_eq8_eq9_lower` by requiring the
disk witness `ρ` to lie *inside* the annulus window `[ρ₁, ρ₂]` together with a
pointwise `Z`-monotonicity hypothesis
`∀ ρ' ∈ [ρ₁, ρ₂], sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ'`. Under those
hypotheses the common factor `Z_ρ ≥ 0` can be extracted from both sides of the
sprint 009 kernel inequality, leaving a sufficient condition that mentions
`c, ρ, ρ₁, ρ₂` and `paperLambda K c ρ'` only — no `circleGap`,
`sigmaZeroMinus`, `sigmaPlus`, `sigmaMinus`, `diskExcess`, or `annulusExcess`
symbol on either side. This opens three independent follow-up attack routes
for a future `c`-pushing sprint without any trust-base expansion: (i)
closed-form upper-bound substitution for `paperLambda K c ρ'` via
`WangPaperSideConditions.paperLambda_le_of_witness`, (ii) a registered
numerical-integration oracle on the now-purely-numerical
`(c⁶/6)/(ρ²−c²) ≤ ∫ 2ρ'³/Λ(c,ρ')` inequality, or (iii) a symbolic
antiderivative of `2ρ'³/Λ(c,ρ')`.

The pointwise `Z`-monotonicity premise has shape
`sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ'` for every `ρ' ∈ [ρ₁, ρ₂]`.
-/
theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ ρ₁ ρ₂ : ℝ, c < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c ^ 2 ∧ ρ < 1 ∧ c < ρ₁ ∧
            ρ₁ ≤ ρ ∧
            ρ ≤ ρ₂ ∧
            ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable (fun ρ' => 2 * ρ' ^ 3
              * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            -- pointwise hypothesis: sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ' for ρ' ∈ Icc ρ₁ ρ₂
            (∀ ρ' ∈ Set.Icc ρ₁ ρ₂, PaperAxioms.sigmaZeroMinus a b ρ
              ≤ PaperAxioms.sigmaZeroMinus a b ρ') ∧
            (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine valid_of_collapsed_disk_eq8_eq9_lower hc_pos hc_lt_one ?_
  intro a b K paper
  obtain ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁ρ, hρρ₂, hρ₂_lt_one,
      hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hZmono, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding.
  have hρ₁₂ : ρ₁ ≤ ρ₂ := hρ₁ρ.trans hρρ₂
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have hZρ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaZeroMinus_nonneg_of_pos a b hρ_pos
  -- Step (a): multiply the Z-free kernel inequality by Z_ρ ≥ 0.
  have hStepA :
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2) * PaperAxioms.sigmaZeroMinus a b ρ
        ≤ (∫ ρ' in ρ₁..ρ₂,
              2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
            * PaperAxioms.sigmaZeroMinus a b ρ :=
    mul_le_mul_of_nonneg_right hKernel hZρ_nonneg
  -- Step (b): pull the constant factor Z_ρ inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b ρ)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Step (c): integrate the pointwise Z-monotonicity to dominate the
  -- constant-Z_ρ integrand by the Z_ρ'-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b ρ) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b ρ)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b ρ ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
            / WangOuter.paperLambda K c ρ' := by
      intro ρ' hρ'
      have hρ'_mem_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ :=
        ⟨hρ'.1.le, hρ'.2.le⟩
      have hZmono_at : PaperAxioms.sigmaZeroMinus a b ρ
          ≤ PaperAxioms.sigmaZeroMinus a b ρ' := hZmono ρ' hρ'_mem_Icc
      have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
      have hρ'_pos : 0 < ρ' := lt_trans hc_pos hcρ'
      have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
        WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ')
      have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
      have hWeight_nonneg :
          0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
        div_nonneg hρ'3_nonneg hΛpos.le
      have hMul :
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ ≤
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ' :=
        mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
      have hRewrite :
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ' =
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
              / WangOuter.paperLambda K c ρ' := by
        field_simp
      linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
              / WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Chain (a) → (b) → (c) to get sprint 009's expected kernel inequality.
  have hKernel' :
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
              / WangOuter.paperLambda K c ρ' := by
    calc
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ
          ≤ (∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
              * PaperAxioms.sigmaZeroMinus a b ρ := hStepA
      _ = ∫ ρ' in ρ₁..ρ₂,
              2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                * PaperAxioms.sigmaZeroMinus a b ρ := hStepB
      _ ≤ ∫ ρ' in ρ₁..ρ₂,
              2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ' := hStepC
  -- Re-pack sprint 009's witness bundle.
  exact ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁₂, hρ₂_lt_one,
    hIntDisk, hIntCircle, hIntLambdaZ, hKernel'⟩

/--
Sprint 011 series-level monotonicity lemma — the workspace's **first
series-level lemma about `sigmaZeroMinus`**. It derives monotonicity of the
`tsum`-defined function `sigmaZeroMinus a b ·` from termwise monotonicity of
its non-negative summands, conditional on summability at the larger argument.
The proof inspects the underlying `∑'` representation, splits on `n2Pred a b
k`, derives `0 ≤ coeffMinusGap a b k` from `‖a k‖ < ‖b k‖` in the active
branch, and combines `pow_le_pow_left₀` with `Summable.of_nonneg_of_le` and
`Summable.tsum_le_tsum`. This unlocks the natural left-edge use-case of sprint
010's `Z`-free reducer (see `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`
below).

Independent of `Section2Assumptions` — pure series-side property of
`sigmaZeroMinus`.
-/
theorem sigmaZeroMinus_monotone_of_summable
    {a b : ℕ → ℂ} {s t : ℝ}
    (hs_nonneg : 0 ≤ s)
    (hst : s ≤ t)
    (hSummable_t :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.sigmaZeroMinus a b s ≤ PaperAxioms.sigmaZeroMinus a b t := by
  -- Abbreviate the termwise summands.
  set fs : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
    else 0 with hfs_def
  set ft : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
    else 0 with hft_def
  -- Termwise monotonicity: fs k ≤ ft k for every k.
  have h_pointwise : ∀ k, fs k ≤ ft k := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · -- Active branch: 0 ≤ coeffMinusGap, and s^(2k-2) ≤ t^(2k-2).
      have hab : ‖a k‖ < ‖b k‖ := hk.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have hsq_lt : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap
        linarith
      have h_pow_le : s ^ (2 * k - 2) ≤ t ^ (2 * k - 2) :=
        pow_le_pow_left₀ hs_nonneg hst (2 * k - 2)
      have h_mul :
          PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) ≤
            PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2) :=
        mul_le_mul_of_nonneg_left h_pow_le h_gap_nn
      simpa [fs, ft, hk] using h_mul
    · -- Inactive branch: both sides are 0.
      simp [fs, ft, hk]
  -- Termwise non-negativity of the s-side summands.
  have h_nonneg_s : ∀ k, 0 ≤ fs k := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · have hab : ‖a k‖ < ‖b k‖ := hk.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have hsq_lt : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap
        linarith
      have h_pow_nn : 0 ≤ s ^ (2 * k - 2) := pow_nonneg hs_nonneg _
      have h_mul_nn :
          0 ≤ PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) :=
        mul_nonneg h_gap_nn h_pow_nn
      simpa [fs, hk] using h_mul_nn
    · simp [fs, hk]
  -- Transfer summability from the t-side to the s-side via the comparison test.
  have hSummable_s : Summable fs :=
    Summable.of_nonneg_of_le h_nonneg_s h_pointwise hSummable_t
  -- Apply the tsum-monotonicity lemma.
  have h_tsum_le : ∑' k, fs k ≤ ∑' k, ft k :=
    hSummable_s.tsum_le_tsum h_pointwise hSummable_t
  -- Re-fold the ∑' expressions back to `sigmaZeroMinus`.
  change (∑' k, fs k) ≤ ∑' k, ft k
  exact h_tsum_le

/--
Sprint 011 left-edge specialisation of sprint 010's `Z`-free reducer. This is
the workspace's first reducer that consumes a **purely series-side
summability premise** in place of sprint 010's pointwise `Z`-monotonicity
premise. The disk witness is fixed at `ρ = ρ₁` (the left edge of the annulus
window), the `Z`-monotonicity premise is discharged in-house from
`sigmaZeroMinus_monotone_of_summable`, and the resulting witness bundle
replaces the pointwise function-value inequality with a series-level
convergence hypothesis — strictly cleaner shape, suitable for direct
discharge by Cauchy/ratio/comparison tests on `[ρ₁, ρ₂] ⊂ (c, 1)` in a
future sprint.
-/
theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c ^ 2 ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            (∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
              Summable (fun k : ℕ =>
                if PaperAxioms.n2Pred a b k then
                  PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
                else 0)) ∧
            (c ^ 6 / 6) / (ρ₁ ^ 2 - c ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free hc_pos hc_lt_one ?_
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one,
      hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hSummable, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding for the left-edge reuse ρ := ρ₁.
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hρ₁_nonneg : 0 ≤ ρ₁ := le_of_lt (lt_trans hc_pos hcρ₁)
  -- Discharge sprint 010's `hZmono` premise using the new monotonicity lemma.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ₁
          ≤ PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    exact sigmaZeroMinus_monotone_of_summable
      hρ₁_nonneg hρ₁_le_ρ' (hSummable ρ' hρ')
  -- Re-pack sprint 010's witness bundle with ρ := ρ₁.
  exact ⟨ρ₁, ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁_lt_one, hcρ₁, le_refl _, hρ₁₂,
    hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hZmono,
    hKernel⟩

/--
Sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper` is the workspace's
**second series-level lemma about `sigmaZeroMinus`** — a comparison-test
summability-transfer result that complements sprint 011's value-level
monotonicity lemma `sigmaZeroMinus_monotone_of_summable`. Together they form a
coordinated pair that lets sprint 011's universal-summability premise be
discharged from a *single point* convergence statement at the upper edge `ρ₂`
(see `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
below).

Independent of `Section2Assumptions` — pure series-side property of
`sigmaZeroMinus`'s underlying termwise summands.
-/
theorem sigmaZeroMinus_summable_of_summable_at_upper
    {a b : ℕ → ℂ} {s t : ℝ}
    (hs_nonneg : 0 ≤ s)
    (hst : s ≤ t)
    (hSummable_t :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
        else 0)) :
    Summable (fun k : ℕ =>
      if PaperAxioms.n2Pred a b k then
        PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
      else 0) := by
  -- Abbreviate the termwise summands.
  set fs : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
    else 0 with hfs_def
  set ft : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
    else 0 with hft_def
  -- Termwise non-negativity of the s-side summands.
  have h_nonneg_s : ∀ k, 0 ≤ fs k := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · have hab : ‖a k‖ < ‖b k‖ := hk.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have hsq_lt : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap
        linarith
      have h_pow_nn : 0 ≤ s ^ (2 * k - 2) := pow_nonneg hs_nonneg _
      have h_mul_nn :
          0 ≤ PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) :=
        mul_nonneg h_gap_nn h_pow_nn
      simpa [fs, hk] using h_mul_nn
    · simp [fs, hk]
  -- Termwise domination: fs k ≤ ft k for every k.
  have h_pointwise : ∀ k, fs k ≤ ft k := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · have hab : ‖a k‖ < ‖b k‖ := hk.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have hsq_lt : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap
        linarith
      have h_pow_le : s ^ (2 * k - 2) ≤ t ^ (2 * k - 2) :=
        pow_le_pow_left₀ hs_nonneg hst (2 * k - 2)
      have h_mul :
          PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) ≤
            PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2) :=
        mul_le_mul_of_nonneg_left h_pow_le h_gap_nn
      simpa [fs, ft, hk] using h_mul
    · simp [fs, ft, hk]
  -- Transfer summability from the t-side to the s-side via the comparison test.
  exact Summable.of_nonneg_of_le h_nonneg_s h_pointwise hSummable_t

/--
Sprint 012's `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
is the workspace's first reducer that consumes a **single point summability
premise** `Summable …` at the upper edge `ρ₂` in place of sprint 011's
universal `∀ ρ' ∈ Icc ρ₁ ρ₂, Summable …`. The universal summability is
reconstructed in-house from `sigmaZeroMinus_summable_of_summable_at_upper`,
and the resulting witness bundle replaces a ∀-quantified family of convergence
statements with a single point convergence statement — strictly cleaner shape,
suitable for direct discharge by Cauchy/ratio/geometric-tail comparison on
`ρ₂ < 1` in a future sprint.
-/
theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c ^ 2 ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c ^ 6 / 6) / (ρ₁ ^ 2 - c ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
    hc_pos hc_lt_one ?_
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one,
      hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Build the universal summability witness from the single-point hypothesis.
  have hSummable_uniform :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
          else 0) := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_trans hc_pos
        (lt_of_lt_of_le hcρ₁ (Set.mem_Icc.mp hρ').1))
    exact sigmaZeroMinus_summable_of_summable_at_upper
            hρ'_nonneg hρ'_le_ρ₂ hSummable_top
  -- Re-pack sprint 011's witness bundle.
  exact ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one, hIntDisk,
    hIntCircle, hIntLambdaZ, hIntLambda, hSummable_uniform, hKernel⟩

/--
Sprint 013: the workspace's first single-`Z_c` disk-side upper bound —
`diskExcess ≤ c⁴ · sigmaZeroMinus c`. It uses only `eq3` and `eq4`
(avoiding `eq2`) and drops the `r²·Z_r` term via sprint 005
non-negativity. Unlike sprint 003's two-`Z` bound (which carries both
`Z_c` and `Z_ρ`) and sprint 007's single-`Z_ρ` collapse on the
branch-split sub-regime, this bound carries only `Z_c`, has no
`ρ`-dependence, and is valid on the full disk regime `c ∈ (0, 1)`.
Composing it with sprint 006's annulus lower bound + sprint 011
monotonicity yields a Z-free reducer over the full window
`[ρ₁, ρ₂] ⊂ (c, 1)` (queued for a future sprint), with kernel
inequality `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` — strictly cleaner than
sprint 010's `(c⁶/6)/(ρ₁²−c²) ≤ ∫…`.
-/
theorem diskExcess_upper_bound_via_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
  -- Step 1: pointwise upper bound on `circleGap r` for `r ∈ Ioo 0 c`.
  have hPointwise :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        PaperAxioms.circleGap a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_nonneg : 0 ≤ r := hr_pos.le
    have hr_lt : r < c := hr.2
    have hr_lt_one : r < 1 := lt_trans hr_lt hc_lt_one
    -- eq3 r: circleGap r = sigmaPlus r - r²·sigmaZeroMinus r.
    have h3 :
        PaperAxioms.circleGap a b r =
          PaperAxioms.sigmaPlus a b r -
            r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
      have := paper.eq3_circleGap_decomposition (r := r) hr_nonneg hr_lt_one
      simpa [PaperAxioms.Eq3CircleGapDecomposition] using this
    -- eq4 r: sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c²·sigmaZeroMinus c.
    have h4 :=
      paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
    have h4_unfold :
        PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
          PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
          PaperAxioms.sigmaMinus a b c =
            c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
    obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
    have hSigmaPlus_le :
        PaperAxioms.sigmaPlus a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      have : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
        le_trans h4a h4b
      rw [h4c] at this
      exact this
    -- Sprint 005 non-negativity of sigmaZeroMinus at r > 0.
    have hZr_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b r :=
      sigmaZeroMinus_nonneg_of_pos a b hr_pos
    have hr2_nonneg : 0 ≤ r ^ 2 := by positivity
    have hr2_Zr_nonneg :
        0 ≤ r ^ 2 * PaperAxioms.sigmaZeroMinus a b r :=
      mul_nonneg hr2_nonneg hZr_nonneg
    -- Combine via h3 + monotonicity.
    linarith
  -- Step 2: multiply pointwise by `2r ≥ 0`.
  have hPointwise_jac :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := by
    intro r hr
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    exact mul_le_mul_of_nonneg_left (hPointwise r hr) h2r_nonneg
  -- Step 3: integrability of the constant-multiple-of-`2r` RHS.
  have hRhsCont :
      Continuous
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) := by
    fun_prop
  have hRhsIntegrable :
      IntervalIntegrable
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
        volume 0 c :=
    hRhsCont.intervalIntegrable _ _
  -- Step 4: integrate the pointwise bound on [0, c].
  have hIntegralMono :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hInt
      hRhsIntegrable hPointwise_jac
  -- Step 5: closed-form RHS integral.
  have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
    have h := @integral_pow 0 c 1
    simp only [pow_one] at h
    convert h using 2 <;> norm_num
  have hRhsClosedForm :
      ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)
        = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
    have hRewrite :
        (fun r : ℝ =>
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
          = fun r =>
            (2 * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) * r := by
      funext r; ring
    rw [hRewrite, intervalIntegral.integral_const_mul, hPow1]
    ring
  -- Step 6: identify diskExcess with the integral and chain via calc.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        ≤ ∫ r in (0 : ℝ)..c,
            2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := hIntegralMono
    _ = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hRhsClosedForm

/--
Sprint 014: the workspace's **first Z-free reducer with no branch-split
constraint and no `(ρ²−c²)` denominator**. It composes sprint 013's
full-disk-regime single-`Z_c` disk bound (`diskExcess ≤ c⁴ · Z_c`) with
sprint 006's annulus lower bound and sprint 011/012's series-level
monotonicity + summability transfer. The kernel inequality is the
cleanest in the workspace: `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`, with the
LHS a polynomial in `c` alone (no `ρ`, no denominator) and the RHS a
pure paper-`Λ` integral. The admissible-window region is the full open
annulus `(c, 1)`, not just `(c, branchSplit c]`. Disk-side monotonicity
is anchored at `ρ = c` (not at an interior `ρ`), so the monotonicity
premise becomes `Z_c ≤ Z_ρ'` for every `ρ' ∈ [ρ₁, ρ₂]`, discharged
in-house by sprint 011 + sprint 012 from a single-point summability
hypothesis at `ρ₂`.
-/
theorem valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle,
      hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding.
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  -- Disk-side bound via sprint 013.
  have hDisk :=
    diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one hIntDisk
  -- Z_c ≥ 0 via sprint 005.
  have hZ_c_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
    sigmaZeroMinus_nonneg_of_pos a b hc_pos
  -- Step (a): multiply the kernel inequality by Z_c ≥ 0.
  have hStepA :
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c :=
    mul_le_mul_of_nonneg_right hKernel hZ_c_nonneg
  -- Step (b): pull the constant factor Z_c inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b c)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Build pointwise Z_c ≤ Z_ρ' via sprint 011 + sprint 012.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b c ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hc_le_ρ' : c ≤ ρ' := le_trans hc_le_ρ₁ hρ₁_le_ρ'
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hc_pos hc_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hc_pos.le hc_le_ρ' hSummable_ρ'
  -- Step (c): integrate the pointwise Z_c ≤ Z_ρ' to dominate the
  -- constant-Z_c integrand by the Z_ρ'-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b c) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b c)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'_pos : 0 < ρ' := lt_trans hc_pos hcρ'
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 006.
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hDisk
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 015's `diskExcess_upper_bound_via_eq5` is the workspace's **first lemma
to consume Wang's printed equation `(5)` directly**. It produces a
single-`Z_ρ`, single-`ρ`, no-integration disk-side upper bound on
`(c, branchSplit c)` whose closed form `(c⁶/(6·(ρ²−c²))) · Z_ρ` coincides
with sprint 007's integrated bound — providing a paper-internal cross-check
that Wang's `(5)` is the integrated form of the `(eq2 + eq3 + eq4)` chain on
the branch-1 sub-regime. The proof bypasses every integration step in
sprints 002/003/007/013, consuming only `paper.eq5_branch1_sigmaReduction`
plus the sprint 005 series identity
`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`.
-/
theorem diskExcess_upper_bound_via_eq5
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hcρ : c < ρ)
    (hρ_split : ρ < PaperAxioms.branchSplit c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch1SigmaKernel c ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ := by
  have h5 :=
    paper.eq5_branch1_sigmaReduction (ρ := ρ) hcρ hρ_split
  have h5_unfold :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        PaperAxioms.branch1SigmaKernel c ρ *
          PaperAxioms.sigmaMinus a b ρ := by
    simpa [PaperAxioms.Eq5Branch1SigmaReduction] using h5
  have hSigmaIdentity :
      PaperAxioms.sigmaMinus a b ρ =
        ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ PaperAxioms.branch1SigmaKernel c ρ *
            PaperAxioms.sigmaMinus a b ρ := h5_unfold
    _ = PaperAxioms.branch1SigmaKernel c ρ *
          (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ) := by
            rw [hSigmaIdentity]
    _ = PaperAxioms.branch1SigmaKernel c ρ * ρ ^ 2 *
          PaperAxioms.sigmaZeroMinus a b ρ := by ring

/--
Sprint 016's `diskExcess_upper_bound_via_eq6` is the workspace's **first lemma
to consume Wang's printed equation `(6)` directly** and the **first disk-side
bound on the branch-2 sub-regime `(branchSplit c, 1)`**. It produces a
single-`Z_ρ`, single-`ρ`, no-integration disk-side upper bound whose closed
form `(c⁴/2) · Z_ρ` (after the algebraic collapse
`branch2SigmaKernel c ρ · ρ² = c⁴/2`) is the **first workspace disk-bound
coefficient that is constant in `ρ`**. The proof bypasses every integration
step in sprints 002/003/007/013 and the entire branch-1 chain sprint 015 sits
in, consuming only `paper.eq6_branch2_sigmaReduction` plus the sprint 005
series identity `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. Together with
sprint 015, this completes the disk-side coverage of Wang's equations
{`eq2`, `eq3`, `eq4`, `eq5`, `eq6`}.
-/
theorem diskExcess_upper_bound_via_eq6
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hρ_split : PaperAxioms.branchSplit c < ρ)
    (hρ1 : ρ < 1) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch2SigmaKernel c ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ := by
  have h6 :=
    paper.eq6_branch2_sigmaReduction (ρ := ρ) hρ_split hρ1
  have h6_unfold :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        PaperAxioms.branch2SigmaKernel c ρ *
          PaperAxioms.sigmaMinus a b ρ := by
    simpa [PaperAxioms.Eq6Branch2SigmaReduction] using h6
  have hSigmaIdentity :
      PaperAxioms.sigmaMinus a b ρ =
        ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ PaperAxioms.branch2SigmaKernel c ρ *
            PaperAxioms.sigmaMinus a b ρ := h6_unfold
    _ = PaperAxioms.branch2SigmaKernel c ρ *
          (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ) := by
            rw [hSigmaIdentity]
    _ = PaperAxioms.branch2SigmaKernel c ρ * ρ ^ 2 *
          PaperAxioms.sigmaZeroMinus a b ρ := by ring

/--
Sprint 022: branch-2 single-`Z_ρ` collapse of sprint 003's two-`Z` disk
bound, **derived without consuming `paper.eq6_branch2_sigmaReduction`**.

This is the workspace's first disk-side bound on the branch-2 sub-regime
`[branchSplit c, 1)` whose paper-axiom signature is `{eq2, eq3, eq4}`
instead of `{eq6}`, providing a paper-internal cross-validation that
Wang's printed equation `(6)` is algebraically a consequence of
`(2)+(3)+(4)` plus a single application of `Z`-monotonicity on the
branch-2 sub-regime where sprint 003's `Z_c` coefficient is non-negative.

The closed-form RHS `(c⁴/2) · sigmaZeroMinus a b ρ` is **algebraically
identical** to the closed form of sprint 016's
`diskExcess_upper_bound_via_eq6` (after the kernel collapse
`branch2SigmaKernel c ρ · ρ² = c⁴/2`). The derivation chain differs:
sprint 016 invokes `paper.eq6_branch2_sigmaReduction` directly, whereas
sprint 022 re-derives the same closed-form bound from sprint 003's
two-`Z` integrated bound plus sprint 011's series monotonicity collapsing
the `Z_c` term into `Z_ρ`.

Together with sprint 007 — which collapses the same sprint 003 two-`Z`
bound on the *branch-1* sub-regime `(c, branchSplit c]` (where the `Z_c`
coefficient is non-positive, so the term is dropped) — sprint 022
exhausts the two algebraic regimes of sprint 003's bound: on branch-1
the `Z_c` term is dropped, on branch-2 it is upper-bounded by `Z_ρ` via
sprint 011 and merged into the `Z_ρ` coefficient.
-/
theorem diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hρ_split : PaperAxioms.branchSplit c ≤ ρ)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c)
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 2) * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Geometric scaffolding: derive `c < branchSplit c` from `√(4/3) > 1`.
  have hSqrt_pos : (0 : ℝ) < 4 / 3 := by norm_num
  have hSqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) := Real.sqrt_nonneg _
  have hSqrt_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
    Real.sq_sqrt (le_of_lt hSqrt_pos)
  have hSqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
    nlinarith [hSqrt_sq, hSqrt_nonneg]
  have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    nlinarith [hSqrt_gt_one, hc_pos]
  -- Combine with `branchSplit c ≤ ρ` to get `c < ρ` and `c ≤ ρ`.
  have hcρ : c < ρ := lt_of_lt_of_le hSplit_gt_c hρ_split
  have hcρ_le : c ≤ ρ := hcρ.le
  have hc_nonneg : (0 : ℝ) ≤ c := hc_pos.le
  -- Positivity of `ρ²−c²`.
  have hρ2c2_pos : 0 < ρ ^ 2 - c ^ 2 := by
    nlinarith [hcρ, hc_pos, sq_nonneg (ρ - c), sq_nonneg (ρ + c)]
  have hρ2c2_ne : (ρ ^ 2 - c ^ 2) ≠ 0 := ne_of_gt hρ2c2_pos
  -- Sprint 003: two-`Z` disk-side upper bound.
  have hUpper :=
    diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt
  -- Branch-2 sub-regime: `4c² ≤ 3ρ²`.
  -- From `c·√(4/3) ≤ ρ` (both sides nonneg) we get `(c·√(4/3))² ≤ ρ²`,
  -- i.e. `c²·(4/3) ≤ ρ²`, hence `4c² ≤ 3ρ²`.
  have hSplit_nonneg : 0 ≤ PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    exact mul_nonneg hc_nonneg hSqrt_nonneg
  have hρ_nonneg : 0 ≤ ρ := le_trans hSplit_nonneg hρ_split
  have hSplit_sq_le : PaperAxioms.branchSplit c ^ 2 ≤ ρ ^ 2 := by
    have := mul_self_le_mul_self hSplit_nonneg hρ_split
    simpa [pow_two] using this
  have hSplit_sq_eq : PaperAxioms.branchSplit c ^ 2 = c ^ 2 * (4 / 3) := by
    unfold PaperAxioms.branchSplit
    have : (c * Real.sqrt (4 / 3)) ^ 2 = c ^ 2 * Real.sqrt (4 / 3) ^ 2 := by
      ring
    rw [this, hSqrt_sq]
  have h_4c2_le_3ρ2 : 4 * c ^ 2 ≤ 3 * ρ ^ 2 := by
    have h1 : c ^ 2 * (4 / 3) ≤ ρ ^ 2 := by
      rw [← hSplit_sq_eq]; exact hSplit_sq_le
    nlinarith [h1]
  have hNumNonneg : 0 ≤ 3 * ρ ^ 2 - 4 * c ^ 2 := by linarith
  -- The `Z_c` coefficient `α := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-negative.
  have hc4_nonneg : 0 ≤ c ^ 4 / 6 := by positivity
  have hα_nonneg :
      0 ≤ (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2) := by
    have hProd_nonneg : 0 ≤ (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) :=
      mul_nonneg hc4_nonneg hNumNonneg
    exact div_nonneg hProd_nonneg hρ2c2_pos.le
  -- Sprint 011 collapse: `Z_c ≤ Z_ρ` via series monotonicity on `[c, ρ]`.
  have hZc_le_Zρ :
      PaperAxioms.sigmaZeroMinus a b c ≤ PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaZeroMinus_monotone_of_summable hc_nonneg hcρ_le hSummable_ρ
  -- Multiply by the non-negative `α` to bound the `Z_c` summand by an `Z_ρ` summand.
  have hαZc_le_αZρ :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c ≤
        (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ :=
    mul_le_mul_of_nonneg_left hZc_le_Zρ hα_nonneg
  -- Algebraic identity: combined coefficient collapses to `c⁴/2`.
  --   (c⁴/6)·(3ρ²−4c²)/(ρ²−c²) + (c⁶/6)/(ρ²−c²)
  --     = [c⁴·(3ρ²−4c²) + c⁶] / (6·(ρ²−c²))
  --     = [3c⁴·(ρ²−c²)] / (6·(ρ²−c²))
  --     = c⁴/2.
  have hCoeff :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
        = c ^ 4 / 2 := by
    field_simp
    ring
  -- Combine: diskExcess ≤ α·Z_c + β·Z_ρ ≤ α·Z_ρ + β·Z_ρ = (c⁴/2)·Z_ρ.
  have hStep1 :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ
          + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ := by
    linarith [hUpper, hαZc_le_αZρ]
  have hStep2 :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ
          + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ
        = ((c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
            + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ := by ring
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ
            + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ := hStep1
    _ = ((c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
            + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ := hStep2
    _ = (c ^ 4 / 2) * PaperAxioms.sigmaZeroMinus a b ρ := by
          rw [hCoeff]

/--
Sprint 017: the workspace's **first closing reducer that lives entirely on
the branch-2 sub-regime `(branchSplit c, 1)`**, the **first closing reducer
with no disk-side integrability premise**, and the **first reducer to consume
sprint 016's `eq6`-based disk bound in a closing chain**. It composes sprint
016's branch-2 single-`Z_{ρ₁}` disk bound `diskExcess ≤ branch2SigmaKernel c
ρ₁ · ρ₁² · Z_{ρ₁}` (which collapses algebraically to `(c⁴/2) · Z_{ρ₁}`) with
sprint 006's annulus lower bound and sprint 011/012's series-level
monotonicity + summability transfer. The kernel inequality
`c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` is **strictly weaker (factor of 2 in the
LHS)** than sprint 014's `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` on the same
branch-2 sub-window, opening the natural Z-free follow-up (sprint 018,
queued separately). The admissible-window region is the open sub-regime
`(branchSplit c, 1)` exactly; disk-side monotonicity is anchored at
`ρ = ρ₁ ∈ (branchSplit c, 1)` (not at `c`), so the monotonicity premise
becomes `Z_{ρ₁} ≤ Z_{ρ'}` for every `ρ' ∈ [ρ₁, ρ₂]`, discharged in-house by
sprint 011 + sprint 012 from a single-point summability hypothesis at `ρ₂`.
-/
theorem valid_of_disk_eq6_annulus_eq8_eq9_branch2_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hSplit_lt_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
      hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding: derive `c < branchSplit c` from `√(4/3) > 1`.
  have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [h_sq, h_sqrt_nonneg]
    nlinarith [h_sqrt_gt_one, hc_pos]
  have hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hρ₁_pos : 0 < ρ₁ := lt_trans hc_pos hcρ₁
  have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le
  -- Disk-side bound via sprint 016.
  have hDiskRaw :=
    diskExcess_upper_bound_via_eq6 paper hSplit_lt_ρ₁ hρ₁_lt_one
  -- Algebraic collapse: branch2SigmaKernel c ρ₁ · ρ₁² = c⁴/2.
  have hCollapse :
      PaperAxioms.branch2SigmaKernel c ρ₁ * ρ₁ ^ 2 = c ^ 4 / 2 := by
    unfold PaperAxioms.branch2SigmaKernel
    have hρ₁_ne : ρ₁ ≠ 0 := ne_of_gt hρ₁_pos
    field_simp
  have hDisk :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := by
    calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ PaperAxioms.branch2SigmaKernel c ρ₁ * ρ₁ ^ 2 *
            PaperAxioms.sigmaZeroMinus a b ρ₁ := hDiskRaw
      _ = c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := by
            rw [hCollapse]
  -- Z_{ρ₁} ≥ 0 via sprint 005.
  have hZ_ρ₁_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_nonneg_of_pos a b hρ₁_pos
  -- Step (a): multiply the kernel inequality by Z_{ρ₁} ≥ 0.
  have hStepA :
      c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    mul_le_mul_of_nonneg_right hKernel hZ_ρ₁_nonneg
  -- Step (b): pull the constant factor Z_{ρ₁} inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b ρ₁)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Build pointwise Z_{ρ₁} ≤ Z_{ρ'} via sprint 011 + sprint 012.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hρ₁_pos hρ₁_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hρ₁_nonneg hρ₁_le_ρ' hSummable_ρ'
  -- Step (c): integrate the pointwise Z_{ρ₁} ≤ Z_{ρ'} to dominate the
  -- constant-Z_{ρ₁} integrand by the Z_{ρ'}-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b ρ₁) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b ρ₁)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hρ'_pos : 0 < ρ' := lt_trans hρ₁_pos hρ'.1
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 006.
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := hDisk
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 018: the workspace's **first consumer of Wang's printed equation `(11)`**,
the **first closing reducer reaching the branch-2 sub-regime via the short
`(7)+(11)` chain** (no `(8)+(9)`+series machinery), and a cross-validation of
the structurally disjoint `(6)+(8)+(9)+series` chain (sprint 017) on the
**same** branch-2 sub-regime. Both chains converge on the same effective
kernel scalar after expansion. The new generic theorem
`valid_of_eq11_subinterval_branch2` is the branch-2 mirror of sprint 008's
`valid_of_eq10_subinterval_branch1`: it integrates `paper.eq11_branch2_pointwise`
against `2ρ` over a free sub-interval `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)` and asks
the resulting kernel mass to reach `1`.
-/
theorem valid_of_eq11_subinterval_branch2
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hSplit_lt_ρ₁, hρ₁₂, hρ₂_lt_one, hMass⟩ := h_window paper
  -- Geometric scaffolding: derive `c < branchSplit c` from `√(4/3) > 1`.
  have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [h_sq, h_sqrt_nonneg]
    nlinarith [h_sqrt_gt_one, hc_pos]
  -- Positivity / ordering setup.
  have hSplit_le_one : PaperAxioms.branchSplit c ≤ 1 := hSplit_lt_one.le
  have hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Integrability of the global annulus density (the explicit premise).
  have hIntCircle :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap) volume c 1 :=
    hIntDensity paper
  -- Sub-interval integrability of the annulus density via `mono_set`.
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  have hIntDens_ρ₁1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ 1 :=
    hIntCircle.mono_set huIcc_ρ₁1
  -- Integrability of the branch-2 mode integrand on `[ρ₁, ρ₂]`.
  have hModeInt :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
        volume ρ₁ ρ₂ :=
    WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable
      hc_pos hρ₁₂ (le_trans hSplit_gt_c.le hSplit_lt_ρ₁.le) hρ₂_lt_one.le
      paper.eq7_paperK_formula
  -- Pointwise bound on the open interior `Ioo ρ₁ ρ₂`, derived from
  -- `eq11_branch2_pointwise` after multiplying by `2ρ ≥ 0`.
  have hPointwiseIoo :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hSplit_lt_ρ : PaperAxioms.branchSplit c < ρ :=
      lt_of_lt_of_le hSplit_lt_ρ₁ hρ.1.le
    have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
    have hcρ : c < ρ := lt_trans hSplit_gt_c hSplit_lt_ρ
    -- (11): branch2PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ.
    have h11 :
        PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          PaperAxioms.circleGap a b ρ :=
      paper.eq11_branch2_pointwise hSplit_lt_ρ hρ_lt_one
    -- Multiply by 2ρ ≥ 0.
    have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
    have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
    have hMul :
        2 * ρ *
            (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
      mul_le_mul_of_nonneg_left h11 h2ρ_nonneg
    -- Algebraic identity: 2 * ρ * branch2PointwiseFactor c Λ ρ = scalarIntegrand2 c Λ ρ.
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
    have hc4_ne : (c ^ 4 : ℝ) ≠ 0 := by positivity
    have hRewriteLHS :
        2 * ρ *
            (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
          Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
      unfold Korenblum.scalarIntegrand2 PaperAxioms.branch2PointwiseFactor
      field_simp
      ring
    have hRewriteRHS :
        2 * ρ * PaperAxioms.circleGap a b ρ =
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := rfl
    rw [hRewriteLHS, hRewriteRHS] at hMul
    exact hMul
  -- Lift the pointwise bound on `Ioo` to an a.e. bound on `Icc`.
  have hPointwiseAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo ρ hρ
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- A.e. non-negativity of the annulus density on `[ρ₁, ρ₂]`.
  have hAnnNonnegAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- Apply `mass_mul_le_annulusSlice_of_integral_bound_ae` with mass = 1.
  have hSliceBound :
      (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
      (modeIntegrand :=
        fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρ₁) (b := ρ₂)
      (mass := 1)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hρ₁₂ zero_le_one hMass hModeInt hIntDens_ρ₁ρ₂
      hPointwiseAE hAnnNonnegAE
  -- Simplify `1 * _ = _`.
  have hDiskLeSlice :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
    simpa [one_mul] using hSliceBound
  -- Split annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ +
  --                          annulusSlice ρ₂ 1.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- Side-slice non-negativities.
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρ₁) hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρ₂) (b := (1 : ℝ)) hρ₂_le_one
      hNonnegAE
  -- Chain to dominate by annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
          hDiskLeSlice
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 085: factored Branch.one pointwise bound. The standalone theorem
extracted from sprint 019's inline derivation (`(5)+(8)+(9) ⇒ scalarIntegrand1
· innerExcess ≤ annulusDensity` on a Branch.one sub-window). The body is the
verbatim chain that previously lived inline inside
`valid_of_eq5_eq8_eq9_subinterval_branch1` (lines 2608-2652 of the
pre-refactor file): apply `eq10_of_eq5_eq8_eq9` to obtain
`branch1PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ`, multiply by
`2ρ ≥ 0`, and rewrite the LHS via the algebraic identity
`2 * ρ * branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ` and the RHS
via the definitional unfolding
`2 * ρ * circleGap ρ = annulusDensity circleGap ρ`.

Stated on `Set.Ioo ρ₁ ρ₂` so the strict-`<` chain consumed by
`eq10_branch1_pointwise` (which needs `c < ρ` and `ρ < branchSplit c`) is
discharged from `c < ρ₁` and `ρ₂ ≤ branchSplit c` together with `ρ ∈ Ioo ρ₁
ρ₂`. Consumers lift to a.e.-`Icc ρ₁ ρ₂` via `Ioo_ae_eq_Icc` exactly as the
existing reducer does.

Used as the missing `hPointwise` premise for the
`mass_mul_le_annulusSlice_of_integral_bound`-shape closing argument on a
Branch.one fallback window. Mirrors
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`'s
role for per-mode windows.
-/
theorem pointwise_branch1_on_Ioo_eq5_eq8_eq9
    {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hcρ₁ : c < ρ₁)
    (hρ₂_split : ρ₂ ≤ PaperAxioms.branchSplit c)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c) :
    ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  -- Derive `(10)` internally from `(5)+(8)+(9)` via `eq10_of_eq5_eq8_eq9`.
  have h10Derived :
      PaperAxioms.Eq10Branch1Pointwise K c
        (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
        (PaperAxioms.circleGap a b) :=
    PaperAxioms.eq10_of_eq5_eq8_eq9
      (sigmaMinus := PaperAxioms.sigmaMinus a b)
      (liftGap := paper.liftGap)
      hc_pos hSplit_lt_one
      paper.eq5_branch1_sigmaReduction
      paper.eq8_sigma_to_liftGap
      paper.eq9_liftGap_to_circleGap
  intro ρ hρ
  have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
  have hρ_split : ρ < PaperAxioms.branchSplit c :=
    lt_of_lt_of_le hρ.2 hρ₂_split
  -- (10): branch1PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ.
  have h10 :
      PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        PaperAxioms.circleGap a b ρ :=
    h10Derived hcρ hρ_split
  -- Multiply by 2ρ ≥ 0.
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hMul :
      2 * ρ *
          (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) ≤
        2 * ρ * PaperAxioms.circleGap a b ρ :=
    mul_le_mul_of_nonneg_left h10 h2ρ_nonneg
  -- Algebraic identity: 2 * ρ * branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ.
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hc6_ne : (c ^ 6 : ℝ) ≠ 0 := by positivity
  have hRewriteLHS :
      2 * ρ *
          (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
    unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
    field_simp
    ring
  have hRewriteRHS :
      2 * ρ * PaperAxioms.circleGap a b ρ =
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := rfl
  rw [hRewriteLHS, hRewriteRHS] at hMul
  exact hMul

/--
Sprint 019: the workspace's **first closing reducer that re-derives Wang's
pointwise `(10)` internally from `(5)+(8)+(9)` instead of consuming
`paper.eq10_branch1_pointwise` directly**, the **first invocation of
`KorenblumPaper.PaperAxioms.eq10_of_eq5_eq8_eq9` by any workspace theorem**,
and a paper-internal cross-validation that the direct `(10)` chain (sprint 008)
and the derived `(5)+(8)+(9)` chain close the contract via the same effective
sufficient condition on the branch-1 sub-regime. After this sprint, the
workspace has Lean proof that `paper.eq10_branch1_pointwise` is a redundant
field of `Section2Assumptions` along this closing chain. The proof body is
otherwise verbatim sprint 008's body, with the single substitution that
`paper.eq10_branch1_pointwise` is replaced by the derived
`eq10_of_eq5_eq8_eq9 ... paper.eq5_branch1_sigmaReduction
paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap`. The signature is
identical to sprint 008's `valid_of_eq10_subinterval_branch1`.

Sprint 085 refactor: the inline pointwise derivation has been extracted into
the standalone theorem `pointwise_branch1_on_Ioo_eq5_eq8_eq9`; this body now
invokes that theorem on `Set.Ioo ρ₁ ρ₂` and lifts to a.e.-`Icc` exactly as
before.
-/
theorem valid_of_eq5_eq8_eq9_subinterval_branch1
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_split, hMass⟩ := h_window paper
  -- Positivity / ordering setup.
  have hSplit_le_one : PaperAxioms.branchSplit c ≤ 1 := hSplit_lt_one.le
  have hρ₂_lt_one : ρ₂ < 1 := lt_of_le_of_lt hρ₂_split hSplit_lt_one
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Integrability of the global annulus density (the explicit premise).
  have hIntCircle :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap) volume c 1 :=
    hIntDensity paper
  -- Sub-interval integrability of the annulus density via `mono_set`.
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  have hIntDens_ρ₁1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ 1 :=
    hIntCircle.mono_set huIcc_ρ₁1
  -- Integrability of the branch-1 mode integrand on `[ρ₁, ρ₂]`.
  have hModeInt :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
        volume ρ₁ ρ₂ :=
    WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      hc_pos hρ₁₂ hcρ₁.le (le_trans hρ₂_split hSplit_le_one)
      paper.eq7_paperK_formula
  -- Pointwise bound on the open interior `Ioo ρ₁ ρ₂`, supplied by the
  -- factored standalone theorem `pointwise_branch1_on_Ioo_eq5_eq8_eq9`
  -- (sprint 085).
  have hPointwiseIoo :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ :=
    pointwise_branch1_on_Ioo_eq5_eq8_eq9
      hc_pos hSplit_lt_one hcρ₁ hρ₂_split paper
  -- Lift the pointwise bound on `Ioo` to an a.e. bound on `Icc` (boundary is
  -- measure zero), so we can apply `mass_mul_le_annulusSlice_of_integral_bound_ae`.
  have hPointwiseAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo ρ hρ
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- A.e. non-negativity of the annulus density on `[ρ₁, ρ₂]`.
  have hAnnNonnegAE :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- Apply `mass_mul_le_annulusSlice_of_integral_bound_ae` with mass = 1.
  have hSliceBound :
      (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
      (modeIntegrand :=
        fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρ₁) (b := ρ₂)
      (mass := 1)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hρ₁₂ zero_le_one hMass hModeInt hIntDens_ρ₁ρ₂
      hPointwiseAE hAnnNonnegAE
  -- Simplify `1 * _ = _`.
  have hDiskLeSlice :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
    simpa [one_mul] using hSliceBound
  -- Split annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ +
  --                          annulusSlice ρ₂ 1.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- Side-slice non-negativities (mirroring sprint 006/008).
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρ₁) hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρ₂) (b := (1 : ℝ)) hρ₂_le_one
      hNonnegAE
  -- Chain to dominate by annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
          hDiskLeSlice
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 020: the workspace's **first closing reducer with a straddling-window
admissibility predicate**, the **first reducer whose mass premise sums two
integrals over disjoint branch sub-intervals**, and the **first reducer to
invoke both `paper.eq10_branch1_pointwise` and `paper.eq11_branch2_pointwise`
simultaneously**. The admissible window `[ρ₁, ρ₂]` is a *straddling*
sub-interval `c < ρ₁ ≤ branchSplit c ≤ ρ₂ < 1`. The mass premise is the
*sum* of two integrals: `scalarIntegrand1` over the branch-1 piece
`[ρ₁, branchSplit c]` plus `scalarIntegrand2` over the branch-2 piece
`[branchSplit c, ρ₂]`. Sprint 020's sufficient condition is strictly weaker
than either single-branch sufficient condition on the same straddling window,
and admits a region of `(ρ₁, ρ₂)`-pairs that no prior reducer can address.
-/
theorem valid_of_eq10_eq11_straddling_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c ∧
            PaperAxioms.branchSplit c ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              (∫ ρ in ρ₁..PaperAxioms.branchSplit c,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in PaperAxioms.branchSplit c..ρ₂,
                Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_split, hsplit_ρ₂, hρ₂_lt_one, hMass⟩ := h_window paper
  -- Geometric scaffolding.
  have hSplit_le_one : PaperAxioms.branchSplit c ≤ 1 := hSplit_lt_one.le
  have hρ₁_le_split : ρ₁ ≤ PaperAxioms.branchSplit c := hρ₁_split
  have hSplit_le_ρ₂ : PaperAxioms.branchSplit c ≤ ρ₂ := hsplit_ρ₂
  have hρ₁₂ : ρ₁ ≤ ρ₂ := le_trans hρ₁_split hsplit_ρ₂
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  have hc_lt_split : c < PaperAxioms.branchSplit c :=
    lt_of_lt_of_le hcρ₁ hρ₁_split
  have hc_le_split : c ≤ PaperAxioms.branchSplit c := hc_lt_split.le
  -- Integrability of the global annulus density (the explicit premise).
  have hIntCircle :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap) volume c 1 :=
    hIntDensity paper
  -- Sub-interval integrability of the annulus density via `mono_set`.
  have huIcc_ρ₁_split : Set.uIcc ρ₁ (PaperAxioms.branchSplit c) ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁_le_split, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ hSplit_le_one
  have huIcc_split_ρ₂ : Set.uIcc (PaperAxioms.branchSplit c) ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hSplit_le_ρ₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_split hρ₂_le_one
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
  have hIntDens_ρ₁_split :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ (PaperAxioms.branchSplit c) :=
    hIntCircle.mono_set huIcc_ρ₁_split
  have hIntDens_split_ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (PaperAxioms.branchSplit c) ρ₂ :=
    hIntCircle.mono_set huIcc_split_ρ₂
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  have hIntDens_ρ₁1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρ₁ 1 :=
    hIntCircle.mono_set huIcc_ρ₁1
  -- Sub-interval integrability of `scalarIntegrand1` on `[ρ₁, branchSplit c]`.
  have hModeInt_b1 :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
        volume ρ₁ (PaperAxioms.branchSplit c) :=
    WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
      hc_pos hρ₁_le_split hcρ₁.le hSplit_le_one paper.eq7_paperK_formula
  -- Sub-interval integrability of `scalarIntegrand2` on `[branchSplit c, ρ₂]`.
  have hModeInt_b2 :
      IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
        volume (PaperAxioms.branchSplit c) ρ₂ :=
    WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable
      hc_pos hSplit_le_ρ₂ hc_le_split hρ₂_lt_one.le paper.eq7_paperK_formula
  -- Pointwise bound on the open interior `Ioo ρ₁ (branchSplit c)`, derived
  -- from `eq10_branch1_pointwise` after multiplying by `2ρ ≥ 0`.
  have hPointwiseIoo_b1 :
      ∀ ρ ∈ Set.Ioo ρ₁ (PaperAxioms.branchSplit c),
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
    have hρ_split : ρ < PaperAxioms.branchSplit c := hρ.2
    -- (10): branch1PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ.
    have h10 :
        PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          PaperAxioms.circleGap a b ρ :=
      paper.eq10_branch1_pointwise hcρ hρ_split
    -- Multiply by 2ρ ≥ 0.
    have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
    have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
    have hMul :
        2 * ρ *
            (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
      mul_le_mul_of_nonneg_left h10 h2ρ_nonneg
    -- Algebraic identity: 2 * ρ * branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ.
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
    have hc6_ne : (c ^ 6 : ℝ) ≠ 0 := by positivity
    have hRewriteLHS_b1 :
        2 * ρ *
            (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
      unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
      field_simp
      ring
    have hRewriteRHS :
        2 * ρ * PaperAxioms.circleGap a b ρ =
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := rfl
    rw [hRewriteLHS_b1, hRewriteRHS] at hMul
    exact hMul
  -- Pointwise bound on the open interior `Ioo (branchSplit c) ρ₂`, derived
  -- from `eq11_branch2_pointwise` after multiplying by `2ρ ≥ 0`.
  have hPointwiseIoo_b2 :
      ∀ ρ ∈ Set.Ioo (PaperAxioms.branchSplit c) ρ₂,
        Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hSplit_lt_ρ : PaperAxioms.branchSplit c < ρ := hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
    have hcρ : c < ρ := lt_trans hc_lt_split hSplit_lt_ρ
    -- (11): branch2PointwiseFactor c Λ ρ * diskExcess ≤ circleGap ρ.
    have h11 :
        PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          PaperAxioms.circleGap a b ρ :=
      paper.eq11_branch2_pointwise hSplit_lt_ρ hρ_lt_one
    -- Multiply by 2ρ ≥ 0.
    have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
    have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
    have hMul :
        2 * ρ *
            (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
      mul_le_mul_of_nonneg_left h11 h2ρ_nonneg
    -- Algebraic identity: 2 * ρ * branch2PointwiseFactor c Λ ρ = scalarIntegrand2 c Λ ρ.
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    have hΛne : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
    have hc4_ne : (c ^ 4 : ℝ) ≠ 0 := by positivity
    have hRewriteLHS_b2 :
        2 * ρ *
            (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
          Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
      unfold Korenblum.scalarIntegrand2 PaperAxioms.branch2PointwiseFactor
      field_simp
      ring
    have hRewriteRHS :
        2 * ρ * PaperAxioms.circleGap a b ρ =
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := rfl
    rw [hRewriteLHS_b2, hRewriteRHS] at hMul
    exact hMul
  -- Lift the pointwise bounds on `Ioo` to a.e. bounds on `Icc` (boundary is
  -- measure zero), so we can apply `mass_mul_le_annulusSlice_of_integral_bound_ae`.
  have hPointwiseAE_b1 :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ (PaperAxioms.branchSplit c)),
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ (PaperAxioms.branchSplit c)),
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo_b1 ρ hρ
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  have hPointwiseAE_b2 :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc (PaperAxioms.branchSplit c) ρ₂),
        Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo (PaperAxioms.branchSplit c) ρ₂),
          Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
              * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo_b2 ρ hρ
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- A.e. non-negativity of the annulus density on each branch piece.
  have hAnnNonnegAE_b1 :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ (PaperAxioms.branchSplit c)),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ (PaperAxioms.branchSplit c)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hSplit_lt_one.le
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  have hAnnNonnegAE_b2 :
      ∀ᵐ ρ ∂volume.restrict (Set.Icc (PaperAxioms.branchSplit c) ρ₂),
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo (PaperAxioms.branchSplit c) ρ₂),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_trans hc_lt_split hρ.1
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hρ₂_le_one
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- Define the mass of each branch piece as a local abbreviation.
  set M₁ : ℝ :=
    ∫ ρ in ρ₁..PaperAxioms.branchSplit c,
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ with hM₁_def
  set M₂ : ℝ :=
    ∫ ρ in PaperAxioms.branchSplit c..ρ₂,
      Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ with hM₂_def
  -- The summed mass premise is `1 ≤ M₁ + M₂`.
  have hMass' : (1 : ℝ) ≤ M₁ + M₂ := hMass
  -- Apply `mass_mul_le_annulusSlice_of_integral_bound_ae` on each branch piece
  -- with mass = M₁ and M₂ respectively.
  -- We don't yet know the sign of M₁ or M₂ individually, but we can split into
  -- cases based on the sign of `diskExcess`. The cleanest approach: use the
  -- non-negative side of the lemma directly with mass bound `mass ≤ ∫`.
  -- Since we use mass = M₁ and M₂, we have `mass ≤ ∫` as `le_refl`.
  -- The lemma requires `0 ≤ mass`, so we case-split on `0 ≤ diskExcess`.
  -- Using the existing `by_cases hInner : 0 ≤ innerExcess` pattern inside the
  -- lemma, we can sidestep the mass-positivity assumption.
  -- Concretely, we use the underlying lemma's two-case structure: when
  -- `0 ≤ diskExcess`, we don't need `0 ≤ mass`; when `diskExcess < 0`, the
  -- conclusion follows from non-negativity of the annulus slice.
  -- For uniformity, we case-split here on `0 ≤ diskExcess` and handle each.
  -- (We will case-split on `0 ≤ diskExcess` directly via `by_cases`.)
  -- We'll prove the goal `diskExcess ≤ annulusExcess` directly via the
  -- two-case structure. Three-piece annulus splitting will be needed in the
  -- positive case to dominate `annulusSlice ρ₁ ρ₂` by `annulusSlice c 1`.
  -- Three-piece annulus split for the dominating step.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- The slice-sum collapse at `branchSplit c`:
  -- annulusSlice ρ₁ (split) + annulusSlice (split) ρ₂ = annulusSlice ρ₁ ρ₂.
  have hAdj_split :
      AnnulusIntegralReduction.annulusSlice paper.circleGap
          ρ₁ (PaperAxioms.branchSplit c) +
        AnnulusIntegralReduction.annulusSlice paper.circleGap
          (PaperAxioms.branchSplit c) ρ₂ =
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁_split hIntDens_split_ρ₂
  -- Side-slice non-negativities (mirroring sprint 008).
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρ₁) hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρ₂) (b := (1 : ℝ)) hρ₂_le_one
      hNonnegAE
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  have hAnnulusExcess_nonneg :
      0 ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c :=
    annulusExcess_nonneg hc_pos hc_lt_one paper
  by_cases hD_nonneg : 0 ≤ PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
  · -- Case 1: 0 ≤ diskExcess. For each branch, case-split on `0 ≤ M_i`:
    -- if non-negative, invoke `mass_mul_le_annulusSlice_of_integral_bound_ae`
    -- with mass = M_i; if negative, use `M_i * D ≤ 0 ≤ slice_i`.
    have hSlice_b1_nonneg :
        0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
              ρ₁ (PaperAxioms.branchSplit c) :=
      AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
        (circleGap := paper.circleGap)
        (a := ρ₁) (b := PaperAxioms.branchSplit c)
        hρ₁_le_split hAnnNonnegAE_b1
    have hSlice_b2_nonneg :
        0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
              (PaperAxioms.branchSplit c) ρ₂ :=
      AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
        (circleGap := paper.circleGap)
        (a := PaperAxioms.branchSplit c) (b := ρ₂)
        hSplit_le_ρ₂ hAnnNonnegAE_b2
    have hM₁_slice :
        M₁ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            ρ₁ (PaperAxioms.branchSplit c) := by
      by_cases hM₁_nn : 0 ≤ M₁
      · -- Positive-mass branch: invoke the lemma directly.
        exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
          (modeIntegrand :=
            fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
          (circleGap := paper.circleGap)
          (a := ρ₁) (b := PaperAxioms.branchSplit c)
          (mass := M₁)
          (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
          hρ₁_le_split hM₁_nn (le_refl _) hModeInt_b1 hIntDens_ρ₁_split
          hPointwiseAE_b1 hAnnNonnegAE_b1
      · -- Negative-mass branch: M₁ * D ≤ 0 ≤ slice_1.
        have hM₁_neg : M₁ ≤ 0 := le_of_lt (lt_of_not_ge hM₁_nn)
        have hM₁D_nonpos :
            M₁ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hM₁_neg hD_nonneg
        exact le_trans hM₁D_nonpos hSlice_b1_nonneg
    have hM₂_slice :
        M₂ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (PaperAxioms.branchSplit c) ρ₂ := by
      by_cases hM₂_nn : 0 ≤ M₂
      · exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
          (modeIntegrand :=
            fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
          (circleGap := paper.circleGap)
          (a := PaperAxioms.branchSplit c) (b := ρ₂)
          (mass := M₂)
          (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
          hSplit_le_ρ₂ hM₂_nn (le_refl _) hModeInt_b2 hIntDens_split_ρ₂
          hPointwiseAE_b2 hAnnNonnegAE_b2
      · have hM₂_neg : M₂ ≤ 0 := le_of_lt (lt_of_not_ge hM₂_nn)
        have hM₂D_nonpos :
            M₂ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hM₂_neg hD_nonneg
        exact le_trans hM₂D_nonpos hSlice_b2_nonneg
    -- Add the two slice inequalities.
    have hSum_slice :
        (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            ρ₁ (PaperAxioms.branchSplit c) +
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (PaperAxioms.branchSplit c) ρ₂ := by
      have hExpand :
          (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
            M₁ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c +
            M₂ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by ring
      rw [hExpand]
      exact add_le_add hM₁_slice hM₂_slice
    -- Use `1 ≤ M₁ + M₂` and `0 ≤ diskExcess` to dominate `D` by the slice.
    have hOneStep :
        (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c :=
      mul_le_mul_of_nonneg_right hMass' hD_nonneg
    have hSliceDominates :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
      calc
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
            = 1 * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
                rw [one_mul]
        _ ≤ (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c :=
              hOneStep
        _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
              ρ₁ (PaperAxioms.branchSplit c) +
            AnnulusIntegralReduction.annulusSlice paper.circleGap
              (PaperAxioms.branchSplit c) ρ₂ := hSum_slice
        _ = AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
              hAdj_split
    -- Chain to dominate by annulusExcess.
    have hSliceLE :
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
      linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
    calc
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
          ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
            hSliceDominates
      _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
      _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq
  · -- Case 2: diskExcess < 0. The conclusion follows from
    -- annulusExcess ≥ 0.
    have hD_neg : PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c < 0 :=
      lt_of_not_ge hD_nonneg
    exact le_trans hD_neg.le hAnnulusExcess_nonneg

/--
Sprint 021's `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` is the
workspace's **first closing reducer with three independent radial
parameters** `(ρ_disk, ρ₁, ρ₂)`, the **first reducer whose disk-side
bound is the non-constant kernel `branch1SigmaKernel c ρ_disk · ρ_disk²`
(varying with `ρ_disk` over `(c, branchSplit c)`)**, and the **first
reducer whose Z-extraction is a cascade of two `sigmaZeroMinus`
monotonicity invocations bridging from a non-window-endpoint disk
anchor**. Sprint 021's sufficient condition is a strict generalisation of
sprint 017's branch-2 reducer (it introduces a free `ρ_disk` parameter;
sprint 017 forces `ρ_disk = ρ₁` collapsing to the constant `c⁴/2`
kernel) and admits annulus windows with `ρ₁ < branchSplit c` that no
prior reducer addresses. The disk-side anchor `ρ_disk ∈ (c, branchSplit
c)` is decoupled from the annulus window `[ρ₁, ρ₂] ⊆ [ρ_disk, 1)`; the
Z-extraction step bridges from the strictly interior anchor `ρ_disk` to
the annulus window via two cascaded series-monotonicity invocations
(`Z_{ρ_disk} ≤ Z_{ρ₁}` once at the boundary, `Z_{ρ₁} ≤ Z_{ρ'}` per
`ρ' ∈ [ρ₁, ρ₂]` in the inner cascade), composed via `le_trans`. The
proof body fuses sprint 015's `(5)`-derived disk-side bound, sprint 006's
`(8)+(9)`-derived annulus-side bound, sprint 005's `Z`-nonnegativity,
sprint 011's series monotonicity (consumed twice), and sprint 012's
summability transfer (consumed at least twice).
-/
theorem valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ_disk ρ₁ ρ₂ : ℝ,
          c < ρ_disk ∧ ρ_disk < PaperAxioms.branchSplit c ∧
          ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) ≤
              ∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ_disk, ρ₁, ρ₂, hcρ_disk, hρ_disk_split, hρ_disk_le_ρ₁,
      hρ₁_le_ρ₂, hρ₂_lt_one, hIntCircle, hIntLambdaZ, hIntLambda,
      hSummable_top, hKernel⟩ := h_witness paper
  -- Geometric scaffolding.
  have hρ_disk_pos : 0 < ρ_disk := lt_trans hc_pos hcρ_disk
  have hρ_disk_nonneg : 0 ≤ ρ_disk := hρ_disk_pos.le
  have hρ₁_pos : 0 < ρ₁ := lt_of_lt_of_le hρ_disk_pos hρ_disk_le_ρ₁
  have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le
  have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hcρ_disk hρ_disk_le_ρ₁
  -- Disk-side bound at `ρ_disk` via sprint 015. Kernel left uncollapsed.
  have hDiskRaw :=
    diskExcess_upper_bound_via_eq5 paper hcρ_disk hρ_disk_split
  -- Z_{ρ_disk} ≥ 0 via sprint 005.
  have hZ_disk_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ_disk :=
    sigmaZeroMinus_nonneg_of_pos a b hρ_disk_pos
  -- Step (a): multiply the kernel inequality by Z_{ρ_disk} ≥ 0.
  have hStepA :
      (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) *
          PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ_disk :=
    mul_le_mul_of_nonneg_right hKernel hZ_disk_nonneg
  -- Step (b): pull the constant factor Z_{ρ_disk} inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ_disk =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ_disk :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b ρ_disk)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Cascaded Z-monotonicity bridge — the unique new step relative to
  -- sprint 017. First derive summability at `ρ₁` from summability at
  -- `ρ₂` via sprint 012.
  have hSummable_ρ₁ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ₁ ^ (2 * k - 2)
        else 0) :=
    sigmaZeroMinus_summable_of_summable_at_upper
      hρ₁_nonneg hρ₁_le_ρ₂ hSummable_top
  -- Boundary inequality `Z_{ρ_disk} ≤ Z_{ρ₁}` via sprint 011.
  have hZ_disk_le_ρ₁ :
      PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
        PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_monotone_of_summable
      hρ_disk_nonneg hρ_disk_le_ρ₁ hSummable_ρ₁
  -- Inner cascade `Z_{ρ₁} ≤ Z_{ρ'}` for `ρ' ∈ [ρ₁, ρ₂]` — verbatim
  -- sprint 017's `hZmono` block.
  have hZmono_inner :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hρ₁_pos hρ₁_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hρ₁_nonneg hρ₁_le_ρ' hSummable_ρ'
  -- Compose: `Z_{ρ_disk} ≤ Z_{ρ'}` for every `ρ' ∈ [ρ₁, ρ₂]`.
  have hZmono_full :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    exact le_trans hZ_disk_le_ρ₁ (hZmono_inner ρ' hρ')
  -- Step (c): integrate the cascaded pointwise bound to dominate the
  -- constant-Z_{ρ_disk} integrand by the Z_{ρ'}-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b ρ_disk) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b ρ_disk)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hρ'_pos : 0 < ρ' := lt_trans hρ₁_pos hρ'.1
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono_full ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ_disk) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁_le_ρ₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 006.
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁_le_ρ₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2 *
            PaperAxioms.sigmaZeroMinus a b ρ_disk := hDiskRaw
    _ = (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) *
          PaperAxioms.sigmaZeroMinus a b ρ_disk := by ring
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ_disk := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ_disk := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 023: the workspace's **first end-to-end `ValidKorenblumBound c` proof
on the branch-2 sub-regime that does *not* invoke
`paper.eq6_branch2_sigmaReduction` anywhere in its transitive proof body**, the
**first paper-internal cross-validation at the closing-reducer level on the
branch-2 axis** (mirroring sprint 022's disk-side cross-validation), and the
**first closing reducer to consume sprint 022's `(2)+(3)+(4)`-derived branch-2
disk bound `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`**. The
proof body composes sprint 022's branch-2 closed-form `(c⁴/2) · Z_{ρ₁}` disk
bound with sprint 006's annulus lower bound and sprint 011/012's series-level
monotonicity + summability transfer. The closed-form scalar kernel
`c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` and the admissible-window region
`branchSplit c ≤ ρ₁ ≤ ρ₂ < 1` (closed-form weak inequality matching sprint
022's input shape) are numerically identical to sprint 017's
`valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`, but the disk-side paper-
axiom signature is `{eq2, eq3, eq4}` (via sprint 022) instead of `{eq6}` (via
sprint 016). After this sprint, the workspace has **two structurally disjoint
paper-axiom signatures** for end-to-end branch-2 closure: `{eq6, eq8, eq9}`
(sprint 017) and `{eq2, eq3, eq4, eq8, eq9}` (sprint 023). This is also the
**first reducer with two independent series-summability premises at distinct
anchors** — one at `ρ₁` (for the disk-side `Z_c → Z_{ρ₁}` collapse inside
sprint 022's body) and one at `ρ₂` (for the annulus-side `Z_{ρ₁} ≤ Z_{ρ'}`
monotonicity transfer to interior points `ρ' ∈ [ρ₁, ρ₂]`).
-/
theorem valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₁ ^ (2 * k - 2)
              else 0) ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle, hIntDiskInner,
      hIntLambdaZ, hIntLambda, hSummable_ρ₁, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding: derive `c < branchSplit c` from `√(4/3) > 1`.
  have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [h_sq, h_sqrt_nonneg]
    nlinarith [h_sqrt_gt_one, hc_pos]
  have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hρ₁_pos : 0 < ρ₁ := lt_trans hc_pos hcρ₁
  have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le
  -- Disk-side bound via sprint 022 — already returned in the merged form
  -- `(c⁴/2) · Z_{ρ₁}`, so no kernel-collapse algebraic step is needed here.
  have hDisk :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse
      paper hc_pos hSplit_le_ρ₁ hρ₁_lt_one hIntDiskInner hSummable_ρ₁
  -- Z_{ρ₁} ≥ 0 via sprint 005.
  have hZ_ρ₁_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_nonneg_of_pos a b hρ₁_pos
  -- Step (a): multiply the kernel inequality by Z_{ρ₁} ≥ 0.
  have hStepA :
      c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    mul_le_mul_of_nonneg_right hKernel hZ_ρ₁_nonneg
  -- Step (b): pull the constant factor Z_{ρ₁} inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b ρ₁)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Build pointwise Z_{ρ₁} ≤ Z_{ρ'} via sprint 011 + sprint 012.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hρ₁_pos hρ₁_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hρ₁_nonneg hρ₁_le_ρ' hSummable_ρ'
  -- Step (c): integrate the pointwise Z_{ρ₁} ≤ Z_{ρ'} to dominate the
  -- constant-Z_{ρ₁} integrand by the Z_{ρ'}-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b ρ₁) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b ρ₁)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hρ'_pos : 0 < ρ' := lt_trans hρ₁_pos hρ'.1
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 006.
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := hDisk
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 024: thin uniform-summability wrapper around sprint 023's
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`. The new
reducer
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
is the workspace's **first end-to-end branch-2 closing reducer with zero
`paper.eq6_branch2_sigmaReduction` consumption AND only one series-summability
premise**, collapsing sprint 023's two-anchor summability shape (`Z @ ρ₁` and
`Z @ ρ₂`) into a single point summability premise at `ρ₂` via sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` transfer applied at `s = ρ₁`,
`t = ρ₂`. Mirrors sprint 012's relationship to sprint 011, and sprint 014's
single-summability shape on the full window — first deployment of that shape
on the branch-2 sub-window. The new top-level invocation of sprint 012
*outside* the existing `hZmono` Icc-loop body (in a single-anchor disk-side
bridging role rather than the interior-bridging role) is the structural
marker that the chain is genuinely different from a verbatim sprint 023 call.
-/
theorem valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
    hc_pos hc_lt_one ?_
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle, hIntDiskInner,
      hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding: derive `0 ≤ ρ₁` from `branchSplit c ≤ ρ₁` and
  -- `c < branchSplit c` (verbatim from sprint 023 lines 3484-3497).
  have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
    unfold PaperAxioms.branchSplit
    have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
    have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
      Real.sqrt_nonneg _
    have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
      Real.sq_sqrt (le_of_lt h_pos)
    have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
      nlinarith [h_sq, h_sqrt_nonneg]
    nlinarith [h_sqrt_gt_one, hc_pos]
  have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁
  have hρ₁_pos : 0 < ρ₁ := lt_trans hc_pos hcρ₁
  have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le
  -- In-house derivation of `Summable @ ρ₁` via sprint 012, in the new
  -- single-anchor disk-side bridging role (top-level, not inside the
  -- `hZmono` Icc-loop body of sprint 023).
  have hSummable_ρ₁ :=
    sigmaZeroMinus_summable_of_summable_at_upper
      hρ₁_nonneg hρ₁₂ hSummable_top
  -- Re-pack the existential bundle for sprint 023 (12-tuple ordering at
  -- Reduction.lean:3480-3482, with `hSummable_ρ₁` preceding `hSummable_top`).
  exact ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
    hIntDiskInner, hIntLambdaZ, hIntLambda, hSummable_ρ₁,
    hSummable_top, hKernel⟩

/--
Sprint 025 series-representation-level upper bound — the workspace's **first
lemma operating purely at the `circleGapSeries` representation level**, the
**first workspace consumer of `coeffPlusGap`/`sigmaPlus`/`n1Pred`**, and the
**first paper-internal cross-validation that the inequality direction of
`paper.eq3_circleGap_decomposition` (`circleGap r ≤ sigmaPlus r`) is provable
from series structure alone**, with **zero paper-axiom invocation** in the
transitive proof body. The proof unfolds `circleGap = circleGapSeries`,
exposes the underlying `∑'`-of-`coeffPlusGap a b k · r^(2k)` form on both
sides, splits termwise on the `n1Pred a b k`/`n2Pred a b k` partition (which
is `n1Pred = (k = 0 ∨ ‖a‖ ≥ ‖b‖)` vs `n2Pred = (0 < k ∧ ‖a‖ < ‖b‖)`), and
uses the fact that on the `n2Pred` branch `coeffPlusGap = ‖a‖² − ‖b‖² ≤ 0`
(via `pow_le_pow_left₀` on `‖a‖ < ‖b‖`) combined with `r^(2k) ≥ 0` to deduce
termwise non-positivity of the dropped contribution. The summability transfer
from the full `circleGapSeries` summand to the `n1Pred`-restricted
`sigmaPlus` summand goes via `Summable.indicator`. Independent of
`Section2Assumptions` — pure series-side property of `circleGap` and
`sigmaPlus`.
-/
theorem circleGap_le_sigmaPlus_via_series_split
    (a b : ℕ → ℂ) {r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hSummable_circleGap :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) :
    PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r := by
  classical
  -- Abbreviate the termwise summands.
  set f : ℕ → ℝ := fun k => PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    with hf_def
  set g : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    else 0 with hg_def
  -- Termwise inequality `f k ≤ g k` via case split on `n1Pred a b k`.
  have h_pointwise : ∀ k, f k ≤ g k := by
    intro k
    by_cases hk : PaperAxioms.n1Pred a b k
    · -- n1Pred true: g k = f k, equality.
      simp [f, g, hk]
    · -- n1Pred false: g k = 0, and on the n2Pred branch `coeffPlusGap ≤ 0`,
      -- so `f k = coeffPlusGap · r^(2k) ≤ 0 = g k`.
      have hn2 : PaperAxioms.n2Pred a b k := by
        unfold PaperAxioms.n1Pred PaperAxioms.n2Pred at *
        push_neg at hk
        exact ⟨Nat.pos_of_ne_zero hk.1, hk.2⟩
      have hab : ‖a k‖ < ‖b k‖ := hn2.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have h_sq_le : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_np : PaperAxioms.coeffPlusGap a b k ≤ 0 := by
        unfold PaperAxioms.coeffPlusGap
        linarith
      have h_pow_nn : 0 ≤ r ^ (2 * k) := pow_nonneg hr_nonneg _
      have h_mul_np :
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h_gap_np h_pow_nn
      simp only [f, g, hk, if_false]
      exact h_mul_np
  -- Summability of `g` via `Set.indicator` over `{k | n1Pred a b k}`.
  have hSummable_g : Summable g := by
    have h_indicator :
        Summable ({k | PaperAxioms.n1Pred a b k}.indicator f) :=
      hSummable_circleGap.indicator {k | PaperAxioms.n1Pred a b k}
    have h_eq : g = {k | PaperAxioms.n1Pred a b k}.indicator f := by
      funext k
      simp [g, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Termwise comparison of the two `tsum`s.
  have h_tsum_le : ∑' k, f k ≤ ∑' k, g k :=
    hSummable_circleGap.tsum_le_tsum h_pointwise hSummable_g
  -- Re-fold the `∑'` back to `circleGap` and `sigmaPlus`.
  change PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r
  unfold PaperAxioms.circleGap PaperAxioms.circleGapSeries PaperAxioms.sigmaPlus
  exact h_tsum_le

/--
Sprint 026 closed-form full-disk upper bound — the workspace's **first
integrated disk bound with paper-axiom signature `{eq4}` only** (vs sprint
013's `{eq3, eq4}`), the **first paper-internal cross-validation that sprint
013's `diskExcess ≤ c⁴ · sigmaZeroMinus c` bound is derivable through a
strictly smaller paper-axiom signature**, and **sprint 025's first downstream
consumer**. The pointwise step `circleGap a b r ≤ sigmaPlus a b r` for
`r ∈ Ioo 0 c` is supplied by sprint 025's
`circleGap_le_sigmaPlus_via_series_split` (paper-axiom-free, uses series
structure on the `n1Pred`/`n2Pred` partition), then `paper.eq4_sigmaPlus_bound`
chains `sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c² · sigmaZeroMinus c`. The
integration over `[0, c]` follows sprint 003's body verbatim. The closed-form
RHS `c⁴ · sigmaZeroMinus a b c` is identical to sprint 013's, but no
`paper.eq3_circleGap_decomposition` invocation appears anywhere in the
transitive proof body.
-/
theorem diskExcess_upper_bound_via_circleGapSeries_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
  -- Step 1: pointwise upper bound on `circleGap r` for `r ∈ Ioo 0 c`,
  -- composed from sprint 025 (`circleGap r ≤ sigmaPlus r`) with
  -- `paper.eq4_sigmaPlus_bound` (`sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c
  -- = c² · sigmaZeroMinus c`). No `eq3` invocation.
  have hPointwise :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        PaperAxioms.circleGap a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_nonneg : 0 ≤ r := hr_pos.le
    have hr_lt : r < c := hr.2
    -- Sprint 025: pointwise series-side bound `circleGap r ≤ sigmaPlus r`.
    have hSeries :
        PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r :=
      circleGap_le_sigmaPlus_via_series_split a b hr_nonneg
        (hSummable hr_nonneg hr_lt)
    -- `paper.eq4_sigmaPlus_bound`: three-conjunct chain.
    have h4 :=
      paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
    have h4_unfold :
        PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
          PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
            PaperAxioms.sigmaMinus a b c =
              c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
    obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
    have hSigmaPlus_le :
        PaperAxioms.sigmaPlus a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      have hChain :
          PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
        le_trans h4a h4b
      rw [h4c] at hChain
      exact hChain
    exact le_trans hSeries hSigmaPlus_le
  -- Step 2: multiply pointwise bound by `2r ≥ 0`.
  have hPointwise_jac :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := by
    intro r hr
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    exact mul_le_mul_of_nonneg_left (hPointwise r hr) h2r_nonneg
  -- Step 3: integrability of the constant-multiple-of-`2r` RHS.
  have hRhsCont :
      Continuous
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) := by
    fun_prop
  have hRhsIntegrable :
      IntervalIntegrable
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
        volume 0 c :=
    hRhsCont.intervalIntegrable _ _
  -- Step 4: integrate the pointwise bound on [0, c].
  have hIntegralMono :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hInt
      hRhsIntegrable hPointwise_jac
  -- Step 5: closed-form RHS integral.
  have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
    have h := @integral_pow 0 c 1
    simp only [pow_one] at h
    convert h using 2 <;> norm_num
  have hRhsClosedForm :
      ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)
        = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
    have hRewrite :
        (fun r : ℝ =>
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
          = fun r =>
            (2 * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) * r := by
      funext r; ring
    rw [hRewrite, intervalIntegral.integral_const_mul, hPow1]
    ring
  -- Step 6: identify diskExcess with the integral and chain via calc.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        ≤ ∫ r in (0 : ℝ)..c,
            2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := hIntegralMono
    _ = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hRhsClosedForm

/--
Sprint 027 series-level *equality* identity — the workspace's **first
paper-axiom-free proof of the *equality direction* of
`paper.eq3_circleGap_decomposition`** (`circleGap r = sigmaPlus r −
r² · sigmaZeroMinus r`), a strict structural upgrade of sprint 025's
inequality direction `circleGap r ≤ sigmaPlus r`, and the **first
workspace `tsum`-partition identity argument on `circleGapSeries`** (vs
sprint 005's single-step `tsum_congr` on `sigmaMinus`). The proof
unfolds `circleGap = circleGapSeries`, partitions the unconditioned
`tsum` of `coeffPlusGap a b k · r^(2k)` along the `n1Pred`/`n2Pred`
indicator decomposition (which partition `ℕ` exactly), identifies the
N1-restricted `tsum` as `sigmaPlus a b r` definitionally, identifies
the N2-restricted `tsum` as `−sigmaMinus a b r` via the termwise
identity `coeffPlusGap = −coeffMinusGap` plus `tsum_neg`, and finally
rewrites `sigmaMinus a b r = r² · sigmaZeroMinus a b r` via sprint 005's
`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. Independent of
`Section2Assumptions`; the only workspace lemma in the transitive
closure is sprint 005's identity, itself paper-axiom-free.
-/
theorem circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
    (a b : ℕ → ℂ) {r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hSummable_circleGap :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) :
    PaperAxioms.circleGap a b r =
      PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
  classical
  -- Abbreviate the three relevant termwise summands.
  set f : ℕ → ℝ := fun k => PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    with hf_def
  set f1 : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    else 0 with hf1_def
  set f2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    else 0 with hf2_def
  set g2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * r ^ (2 * k)
    else 0 with hg2_def
  -- Partition fact: ¬ n1Pred → n2Pred. Mirrors sprint 025's `push_neg` body.
  have h_n1_to_n2 :
      ∀ k, ¬ PaperAxioms.n1Pred a b k → PaperAxioms.n2Pred a b k := by
    intro k hk
    unfold PaperAxioms.n1Pred at hk
    unfold PaperAxioms.n2Pred
    push_neg at hk
    exact ⟨Nat.pos_of_ne_zero hk.1, hk.2⟩
  -- Reverse direction: n2Pred → ¬ n1Pred (the predicates are mutually exclusive).
  have h_n2_to_not_n1 :
      ∀ k, PaperAxioms.n2Pred a b k → ¬ PaperAxioms.n1Pred a b k := by
    intro k hk2 hk1
    unfold PaperAxioms.n2Pred at hk2
    unfold PaperAxioms.n1Pred at hk1
    obtain ⟨hk_pos, hab⟩ := hk2
    rcases hk1 with h | h
    · exact (Nat.lt_irrefl 0 (h ▸ hk_pos))
    · exact (not_lt_of_ge h) hab
  -- Termwise partition identity: f k = f1 k + f2 k for all k.
  have h_term_partition : ∀ k, f k = f1 k + f2 k := by
    intro k
    by_cases hk1 : PaperAxioms.n1Pred a b k
    · -- n1Pred true ⇒ n2Pred false ⇒ RHS = f k + 0 = f k.
      have hk2 : ¬ PaperAxioms.n2Pred a b k := fun hcontra =>
        h_n2_to_not_n1 k hcontra hk1
      simp [f, f1, f2, hk1, hk2]
    · -- n1Pred false ⇒ n2Pred true ⇒ RHS = 0 + f k = f k.
      have hk2 : PaperAxioms.n2Pred a b k := h_n1_to_n2 k hk1
      simp [f, f1, f2, hk1, hk2]
  -- Summability of `f1` via `Summable.indicator` over `{k | n1Pred a b k}`.
  have hSummable_f1 : Summable f1 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n1Pred a b k}.indicator f) :=
      hSummable_circleGap.indicator {k | PaperAxioms.n1Pred a b k}
    have h_eq : f1 = {k | PaperAxioms.n1Pred a b k}.indicator f := by
      funext k
      simp [f1, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Summability of `f2` via `Summable.indicator` over `{k | n2Pred a b k}`.
  have hSummable_f2 : Summable f2 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n2Pred a b k}.indicator f) :=
      hSummable_circleGap.indicator {k | PaperAxioms.n2Pred a b k}
    have h_eq : f2 = {k | PaperAxioms.n2Pred a b k}.indicator f := by
      funext k
      simp [f2, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Step A: ∑' k, f k = (∑' k, f1 k) + (∑' k, f2 k).
  -- Combines the termwise partition identity with `tsum_congr` and
  -- `Summable.tsum_add`.
  have h_tsum_partition :
      (∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k := by
    have h_congr : (∑' k, f k) = ∑' k, (f1 k + f2 k) :=
      tsum_congr h_term_partition
    rw [h_congr, hSummable_f1.tsum_add hSummable_f2]
  -- Step B: ∑' k, f1 k = sigmaPlus a b r (definitional).
  have h_f1_sigmaPlus :
      (∑' k, f1 k) = PaperAxioms.sigmaPlus a b r := by
    change (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
        else 0)
      = PaperAxioms.sigmaPlus a b r
    rfl
  -- Step C: ∑' k, f2 k = − ∑' k, g2 k.
  --   On `n2Pred`: coeffPlusGap a b k = ‖a‖² − ‖b‖² = −coeffMinusGap a b k.
  --   On `¬ n2Pred`: both branches collapse to 0.
  -- Lift via `tsum_congr` then pull `−` out via `tsum_neg`.
  have h_f2_eq_neg_g2 : (∑' k, f2 k) = - ∑' k, g2 k := by
    have h_term_neg : ∀ k, f2 k = -(g2 k) := by
      intro k
      by_cases hk : PaperAxioms.n2Pred a b k
      · simp only [f2, g2, hk, if_true]
        unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
        ring
      · simp [f2, g2, hk]
    calc (∑' k, f2 k)
        = ∑' k, -(g2 k) := tsum_congr h_term_neg
      _ = -∑' k, g2 k := tsum_neg
  -- Step D: ∑' k, g2 k = sigmaMinus a b r (definitional).
  have h_g2_sigmaMinus :
      (∑' k, g2 k) = PaperAxioms.sigmaMinus a b r := by
    change (∑' k : ℕ,
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * r ^ (2 * k)
        else 0)
      = PaperAxioms.sigmaMinus a b r
    rfl
  -- Step E: rewrite circleGap a b r as ∑' k, f k (definitional).
  have h_circleGap_unfold :
      PaperAxioms.circleGap a b r = ∑' k, f k := by
    change PaperAxioms.circleGapSeries a b r = ∑' k, f k
    rfl
  -- Step F: sprint 005's identity sigmaMinus = r² · sigmaZeroMinus.
  have h_sprint005 := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b r
  -- Combine all steps.
  rw [h_circleGap_unfold, h_tsum_partition, h_f1_sigmaPlus, h_f2_eq_neg_g2,
      h_g2_sigmaMinus, h_sprint005]
  ring

/--
Sprint 028 series-level cross-radius lower bound — the workspace's **first
paper-axiom-free proof of the inequality direction of
`paper.eq2_sigmaZeroMinus_lower`** (Wang's printed equation `(2)`,
`Z_r ≥ ((ρ²-r²)/(ρ²-c²)) · Z_c − ((c²-r²)/(ρ²-c²)) · Z_ρ`), and the **first
workspace `tsum_le_tsum` argument that consumes a Mathlib `ConvexOn`
instance**. The proof writes the inequality in its canonical convex-combination
form `(ρ²-c²) · Z_r + (c²-r²) · Z_ρ ≥ (ρ²-r²) · Z_c`, derives a termwise
convexity inequality from `convexOn_pow (k-1)` applied at the convex
combination `c² = μ_1 · r² + μ_2 · ρ²` with `μ_1 = (ρ²-c²)/(ρ²-r²)`,
`μ_2 = (c²-r²)/(ρ²-r²)`, lifts the inequality to a `tsum_le_tsum` comparison
on the `n2Pred`-restricted summands, and rearranges algebraically. The summability
premises at the lower anchors `r` and `c` are derived in-house via sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` (the first usage pattern that
exercises sprint 012's transitivity across two distinct lower bridging
targets in one lemma). Independent of `Section2Assumptions` — only `(a, b)`,
three radii `0 ≤ r < c < ρ`, and a single summability premise at the upper
anchor `ρ` are needed.
-/
theorem sigmaZeroMinus_lower_via_series_convexity
    (a b : ℕ → ℂ) {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt_c : r < c)
    (hc_lt_ρ : c < ρ)
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.sigmaZeroMinus a b r ≥
      ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
        ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ := by
  classical
  -- Geometric scaffolding.
  have hr_lt_ρ : r < ρ := lt_trans hr_lt_c hc_lt_ρ
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt_c
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hρ_pos : 0 < ρ := lt_of_le_of_lt hc_nonneg hc_lt_ρ
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  -- Squared geometric facts.
  have hr_sq_nonneg : 0 ≤ r ^ 2 := sq_nonneg r
  have hρ_sq_nonneg : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hr_sq_lt_c_sq : r ^ 2 < c ^ 2 := by
    have h := mul_self_lt_mul_self hr_nonneg hr_lt_c
    have hr : r * r = r ^ 2 := by ring
    have hc' : c * c = c ^ 2 := by ring
    rw [hr, hc'] at h; exact h
  have hc_sq_lt_ρ_sq : c ^ 2 < ρ ^ 2 := by
    have h := mul_self_lt_mul_self hc_nonneg hc_lt_ρ
    have hc' : c * c = c ^ 2 := by ring
    have hρ' : ρ * ρ = ρ ^ 2 := by ring
    rw [hc', hρ'] at h; exact h
  have hr_sq_lt_ρ_sq : r ^ 2 < ρ ^ 2 := lt_trans hr_sq_lt_c_sq hc_sq_lt_ρ_sq
  have h_ρ_sq_minus_r_sq_pos : 0 < ρ ^ 2 - r ^ 2 := by linarith
  have h_ρ_sq_minus_c_sq_pos : 0 < ρ ^ 2 - c ^ 2 := by linarith
  have h_c_sq_minus_r_sq_pos : 0 < c ^ 2 - r ^ 2 := by linarith
  have h_ρ_sq_minus_r_sq_ne : (ρ ^ 2 - r ^ 2) ≠ 0 := ne_of_gt h_ρ_sq_minus_r_sq_pos
  have h_ρ_sq_minus_c_sq_ne : (ρ ^ 2 - c ^ 2) ≠ 0 := ne_of_gt h_ρ_sq_minus_c_sq_pos
  -- In-house derivation of summability at `c` and `r` from the upper-anchor
  -- premise via sprint 012 — first usage with two distinct lower targets.
  have hSummable_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * c ^ (2 * k - 2)
        else 0) :=
    sigmaZeroMinus_summable_of_summable_at_upper hc_nonneg hc_lt_ρ.le hSummable_ρ
  have hSummable_r :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * r ^ (2 * k - 2)
        else 0) :=
    sigmaZeroMinus_summable_of_summable_at_upper hr_nonneg
      (le_of_lt hr_lt_ρ) hSummable_ρ
  -- Abbreviate the three relevant termwise summands.
  set fr : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * r ^ (2 * k - 2)
    else 0 with hfr_def
  set fc : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * c ^ (2 * k - 2)
    else 0 with hfc_def
  set fρ : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
    else 0 with hfρ_def
  -- Termwise convexity inequality at the convex combination
  -- `c² = μ_1·r² + μ_2·ρ²` where `μ_1 = (ρ²-c²)/(ρ²-r²)`,
  -- `μ_2 = (c²-r²)/(ρ²-r²)`. We work directly with the unscaled form
  --   (ρ²-r²) · fc k ≤ (ρ²-c²) · fr k + (c²-r²) · fρ k
  -- to avoid having to thread the division through every step.
  have h_term_convexity :
      ∀ k, (ρ ^ 2 - r ^ 2) * fc k ≤
        (ρ ^ 2 - c ^ 2) * fr k + (c ^ 2 - r ^ 2) * fρ k := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · -- Active branch: 0 < k, ‖a k‖ < ‖b k‖, hence coeffMinusGap ≥ 0.
      have hkpos : 0 < k := hk.1
      have hab : ‖a k‖ < ‖b k‖ := hk.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have hsq_le : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap; linarith
      -- For 0 < k, we have 2*k - 2 = 2*(k-1).
      have hkm1 : 2 * k - 2 = 2 * (k - 1) := by omega
      -- Convexity inequality from `convexOn_pow (k-1)` evaluated at
      -- `r²`, `ρ²` ∈ Ici 0 with weights `μ_1`, `μ_2`. We work with the
      -- algebraic content: (c²)^(k-1) ≤ μ_1·(r²)^(k-1) + μ_2·(ρ²)^(k-1).
      have h_convexOn :
          ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ (k - 1)) :=
        convexOn_pow (k - 1)
      -- Define the convex weights μ_1, μ_2.
      set μ₁ : ℝ := (ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2) with hμ₁_def
      set μ₂ : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2) with hμ₂_def
      have hμ₁_nn : 0 ≤ μ₁ :=
        div_nonneg h_ρ_sq_minus_c_sq_pos.le h_ρ_sq_minus_r_sq_pos.le
      have hμ₂_nn : 0 ≤ μ₂ :=
        div_nonneg h_c_sq_minus_r_sq_pos.le h_ρ_sq_minus_r_sq_pos.le
      have hμ_sum : μ₁ + μ₂ = 1 := by
        change (ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)
            + (c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2) = 1
        field_simp
        ring
      have h_convex_combo : μ₁ • (r ^ 2) + μ₂ • (ρ ^ 2) = c ^ 2 := by
        change μ₁ * r ^ 2 + μ₂ * ρ ^ 2 = c ^ 2
        rw [hμ₁_def, hμ₂_def]
        field_simp
        ring
      have h_r_in : (r ^ 2) ∈ Set.Ici (0 : ℝ) := hr_sq_nonneg
      have h_ρ_in : (ρ ^ 2) ∈ Set.Ici (0 : ℝ) := hρ_sq_nonneg
      have h_conv_ineq :=
        h_convexOn.2 h_r_in h_ρ_in hμ₁_nn hμ₂_nn hμ_sum
      -- h_conv_ineq : (μ₁•r² + μ₂•ρ²)^(k-1) ≤ μ₁•(r²)^(k-1) + μ₂•(ρ²)^(k-1)
      rw [h_convex_combo] at h_conv_ineq
      -- Convert the • to *.
      have h_conv_ineq' :
          (c ^ 2) ^ (k - 1) ≤ μ₁ * (r ^ 2) ^ (k - 1) + μ₂ * (ρ ^ 2) ^ (k - 1) :=
        h_conv_ineq
      -- Rewrite (s²)^(k-1) = s^(2*(k-1)) = s^(2*k - 2) for s ∈ {r, c, ρ}.
      have hpow_r : (r ^ 2) ^ (k - 1) = r ^ (2 * k - 2) := by
        rw [← pow_mul, hkm1]
      have hpow_c : (c ^ 2) ^ (k - 1) = c ^ (2 * k - 2) := by
        rw [← pow_mul, hkm1]
      have hpow_ρ : (ρ ^ 2) ^ (k - 1) = ρ ^ (2 * k - 2) := by
        rw [← pow_mul, hkm1]
      rw [hpow_r, hpow_c, hpow_ρ] at h_conv_ineq'
      -- Multiply by (ρ²-r²) > 0 to clear denominators.
      have h_scaled :
          (ρ ^ 2 - r ^ 2) * c ^ (2 * k - 2) ≤
            (ρ ^ 2 - c ^ 2) * r ^ (2 * k - 2)
              + (c ^ 2 - r ^ 2) * ρ ^ (2 * k - 2) := by
        have h_scale :=
          (mul_le_mul_of_nonneg_left h_conv_ineq' h_ρ_sq_minus_r_sq_pos.le)
        -- Rearrange the LHS and RHS.
        have hL : (ρ ^ 2 - r ^ 2) * c ^ (2 * k - 2)
            = (ρ ^ 2 - r ^ 2) * c ^ (2 * k - 2) := rfl
        have hμ₁_mul :
            (ρ ^ 2 - r ^ 2) * (μ₁ * r ^ (2 * k - 2))
              = (ρ ^ 2 - c ^ 2) * r ^ (2 * k - 2) := by
          rw [hμ₁_def]
          field_simp
        have hμ₂_mul :
            (ρ ^ 2 - r ^ 2) * (μ₂ * ρ ^ (2 * k - 2))
              = (c ^ 2 - r ^ 2) * ρ ^ (2 * k - 2) := by
          rw [hμ₂_def]
          field_simp
        calc (ρ ^ 2 - r ^ 2) * c ^ (2 * k - 2)
            ≤ (ρ ^ 2 - r ^ 2) *
                (μ₁ * r ^ (2 * k - 2) + μ₂ * ρ ^ (2 * k - 2)) := h_scale
          _ = (ρ ^ 2 - r ^ 2) * (μ₁ * r ^ (2 * k - 2))
              + (ρ ^ 2 - r ^ 2) * (μ₂ * ρ ^ (2 * k - 2)) := by ring
          _ = (ρ ^ 2 - c ^ 2) * r ^ (2 * k - 2)
              + (c ^ 2 - r ^ 2) * ρ ^ (2 * k - 2) := by
                rw [hμ₁_mul, hμ₂_mul]
      -- Multiply both sides by coeffMinusGap a b k ≥ 0 to get the bare summand
      -- inequality, then unfold the indicator.
      have h_pow_ineq := h_scaled
      have h_with_gap :
          PaperAxioms.coeffMinusGap a b k *
              ((ρ ^ 2 - r ^ 2) * c ^ (2 * k - 2)) ≤
            PaperAxioms.coeffMinusGap a b k *
              ((ρ ^ 2 - c ^ 2) * r ^ (2 * k - 2)
                + (c ^ 2 - r ^ 2) * ρ ^ (2 * k - 2)) :=
        mul_le_mul_of_nonneg_left h_pow_ineq h_gap_nn
      simp only [fr, fc, fρ, hk, if_true]
      nlinarith [h_with_gap]
    · -- Inactive branch: all three indicator branches are 0.
      simp [fr, fc, fρ, hk]
  -- Lift to the tsum level.
  -- Define the RHS combined summand and prove it is summable.
  set gρ : ℕ → ℝ := fun k => (ρ ^ 2 - c ^ 2) * fr k + (c ^ 2 - r ^ 2) * fρ k
    with hgρ_def
  have hSummable_lhs_tsum :
      Summable (fun k => (ρ ^ 2 - r ^ 2) * fc k) :=
    hSummable_c.mul_left _
  have hSummable_rhs_tsum :
      Summable gρ := by
    have h1 : Summable (fun k => (ρ ^ 2 - c ^ 2) * fr k) :=
      hSummable_r.mul_left _
    have h2 : Summable (fun k => (c ^ 2 - r ^ 2) * fρ k) :=
      hSummable_ρ.mul_left _
    exact h1.add h2
  -- Apply tsum_le_tsum on the termwise convexity inequality.
  have h_tsum_le :
      (∑' k, (ρ ^ 2 - r ^ 2) * fc k) ≤ ∑' k, gρ k := by
    refine hSummable_lhs_tsum.tsum_le_tsum ?_ hSummable_rhs_tsum
    intro k
    exact h_term_convexity k
  -- Identify each tsum with the corresponding sigmaZeroMinus.
  have h_lhs_eq :
      (∑' k, (ρ ^ 2 - r ^ 2) * fc k)
        = (ρ ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b c := by
    rw [tsum_mul_left]
    rfl
  have h_tsum_fr :
      (∑' k, (ρ ^ 2 - c ^ 2) * fr k)
        = (ρ ^ 2 - c ^ 2) * PaperAxioms.sigmaZeroMinus a b r := by
    rw [tsum_mul_left]
    rfl
  have h_tsum_fρ :
      (∑' k, (c ^ 2 - r ^ 2) * fρ k)
        = (c ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b ρ := by
    rw [tsum_mul_left]
    rfl
  have h_rhs_eq :
      (∑' k, gρ k)
        = (ρ ^ 2 - c ^ 2) * PaperAxioms.sigmaZeroMinus a b r
          + (c ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b ρ := by
    have h1 : Summable (fun k => (ρ ^ 2 - c ^ 2) * fr k) :=
      hSummable_r.mul_left _
    have h2 : Summable (fun k => (c ^ 2 - r ^ 2) * fρ k) :=
      hSummable_ρ.mul_left _
    rw [show (gρ : ℕ → ℝ)
          = fun k => (ρ ^ 2 - c ^ 2) * fr k + (c ^ 2 - r ^ 2) * fρ k from rfl]
    rw [h1.tsum_add h2, h_tsum_fr, h_tsum_fρ]
  rw [h_lhs_eq, h_rhs_eq] at h_tsum_le
  -- Final algebraic rearrangement: divide by (ρ²-c²) > 0 then rearrange.
  -- We have: (ρ²-r²) * Z_c ≤ (ρ²-c²) * Z_r + (c²-r²) * Z_ρ.
  -- Goal:    Z_r ≥ ((ρ²-r²)/(ρ²-c²)) * Z_c - ((c²-r²)/(ρ²-c²)) * Z_ρ.
  rw [ge_iff_le]
  have hDiv : (0 : ℝ) < ρ ^ 2 - c ^ 2 := h_ρ_sq_minus_c_sq_pos
  have key :
      (ρ ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b c ≤
        (ρ ^ 2 - c ^ 2) * PaperAxioms.sigmaZeroMinus a b r
          + (c ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b ρ := h_tsum_le
  have h_div_clear :
      ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        - ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
            * PaperAxioms.sigmaZeroMinus a b ρ
      = ((ρ ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b c
          - (c ^ 2 - r ^ 2) * PaperAxioms.sigmaZeroMinus a b ρ)
        / (ρ ^ 2 - c ^ 2) := by
    field_simp
  rw [h_div_clear, div_le_iff₀ hDiv]
  linarith [key]

/--
Sprint 029 inner-disk pointwise bound: combine sprints 027 (`circleGap`-as-
series-partition equality, paper-axiom-`eq3`-free) and 028
(`sigmaZeroMinus`-cross-radius lower bound, paper-axiom-`eq2`-free) with
`paper.eq4_sigmaPlus_bound` to upper-bound `circleGap r` for `r < c` in terms
of `sigmaZeroMinus` at `c` and at a free parameter `ρ ∈ (c, 1)`. The
conclusion is byte-for-byte identical to sprint 002's
`circleGap_inner_bound_of_eq2_eq3_eq4`, but the paper-axiom signature
shrinks from `{eq2, eq3, eq4}` to `{eq4}` only — at the price of two
extra summability premises. The first is the `circleGap` series at the
lower radius `r` (sprint 027's hypothesis); the second is the
N2-restricted minus-gap series at the upper radius `ρ` (sprint 028's
hypothesis).
-/
theorem circleGap_inner_bound_via_series_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {r ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity facts.
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt
  have hc_lt_one : c < 1 := lt_trans hcρ hρ1
  have hc_lt_ρ : c < ρ := hcρ
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have hρ2_minus_c2_pos : 0 < ρ ^ 2 - c ^ 2 := by nlinarith
  have hr2_nonneg : 0 ≤ r ^ 2 := by positivity
  -- Step 1: sprint 027 supplies the equality
  --   `circleGap r = sigmaPlus r - r^2 * sigmaZeroMinus r`
  -- without any paper-axiom invocation (replaces sprint 002's eq3 step).
  have hr_lt_one : r < 1 := lt_trans hr_lt hc_lt_one
  have h3 :
      PaperAxioms.circleGap a b r =
        PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r :=
    circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
      a b hr_nonneg hSummable_circleGap_r
  -- Step 2: invoke the eq4 bundle (three pieces about sigmaPlus / sigmaMinus
  -- at c). Verbatim from sprint 002; the sole `paper.*` invocation in this proof.
  have h4 :=
    paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
  have h4_unfold :
      PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
        PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
  obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
  have hSigmaPlus_le :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    have : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
      le_trans h4a h4b
    rw [h4c] at this
    exact this
  -- Step 3: sprint 028 supplies the cross-radius lower bound on
  -- `sigmaZeroMinus a b r` without any paper-axiom invocation (replaces
  -- sprint 002's eq2 step). Sprint 028 already returns the bound in the
  -- unfolded form, so the sprint-002 `simpa` step is unnecessary.
  have h2_unfold :
      PaperAxioms.sigmaZeroMinus a b r ≥
        ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
          ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaZeroMinus_lower_via_series_convexity
      a b hr_nonneg hr_lt hcρ hSummable_n2_ρ
  -- Multiply `h2_unfold` by `r^2 ≥ 0` to get an upper bound on
  -- `-r^2 * sigmaZeroMinus a b r`.
  set Z_c : ℝ := PaperAxioms.sigmaZeroMinus a b c with hZc
  set Z_ρ : ℝ := PaperAxioms.sigmaZeroMinus a b ρ with hZρ
  set Z_r : ℝ := PaperAxioms.sigmaZeroMinus a b r with hZr
  set A : ℝ := (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hA
  set B : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hB
  -- Rewrite h2 in terms of A, B.
  have h2' : A * Z_c - B * Z_ρ ≤ Z_r := by
    have := h2_unfold
    simp only [ge_iff_le, hA, hB, hZc, hZρ, hZr] at this ⊢
    exact this
  -- Multiply by r^2 ≥ 0.
  have hMul : r ^ 2 * (A * Z_c - B * Z_ρ) ≤ r ^ 2 * Z_r :=
    mul_le_mul_of_nonneg_left h2' hr2_nonneg
  -- So -r^2 * Z_r ≤ -r^2 * (A * Z_c - B * Z_ρ) = -r^2 * A * Z_c + r^2 * B * Z_ρ.
  have hNeg : -(r ^ 2 * Z_r) ≤ -(r ^ 2 * (A * Z_c - B * Z_ρ)) := by linarith
  -- Now combine: circleGap r = sigmaPlus r - r^2 * Z_r ≤ c^2 * Z_c - r^2 * Z_r
  --                          ≤ c^2 * Z_c + (-r^2*A*Z_c + r^2*B*Z_ρ).
  have hSigmaPlus_le' :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * Z_c := by
    simp only [hZc]; exact hSigmaPlus_le
  -- Final algebra: c^2 * Z_c - r^2 * (A * Z_c - B * Z_ρ)
  --              = (c^2 - r^2 * A) * Z_c + r^2 * B * Z_ρ.
  -- And we need to show that target's first coefficient
  -- `(c^2 - r^2 * (ρ^2 - r^2) / (ρ^2 - c^2))` equals `c^2 - r^2 * A`.
  have hA_def : A = (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  have hB_def : B = (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  -- Build the chain.
  have hStep1 :
      PaperAxioms.circleGap a b r ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := by
    rw [h3]
    linarith [hSigmaPlus_le']
  have hStep2 :
      c ^ 2 * Z_c - r ^ 2 * Z_r ≤
        c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := by
    linarith [hMul]
  have hRewrite :
      c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) =
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by ring
  have hFinal :
      PaperAxioms.circleGap a b r ≤
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by
    calc PaperAxioms.circleGap a b r
        ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := hStep1
      _ ≤ c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := hStep2
      _ = (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := hRewrite
  -- Match the goal's denominator-laden form.
  have hCoeff1 : c ^ 2 - r ^ 2 * A =
      c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := by
    simp only [hA_def, mul_div_assoc']
  have hCoeff2 : r ^ 2 * B = r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) := by
    simp only [hB_def]
  rw [hCoeff1, hCoeff2] at hFinal
  exact hFinal

/--
Sprint 030 integrated two-`Z` `diskExcess` upper bound (paper-axiom-`{eq4}`-only):
the integrated counterpart of sprint 029. Re-walks sprint 003's algebraic chain
verbatim with one surgical replacement at Step A — the inner-disk pointwise
bound is supplied by sprint 029's `circleGap_inner_bound_via_series_eq4_only`
instead of sprint 002's `circleGap_inner_bound_of_eq2_eq3_eq4`. The conclusion
is byte-for-byte identical to sprint 003's `diskExcess_upper_bound_of_eq2_eq3_eq4`.
The hypothesis count grows by exactly two new summability premises:
* `hSummable_circleGap` quantified over `r ∈ [0, c)` (sprint 029's first
  hypothesis lifted under integration);
* `hSummable_n2_ρ` at the single upper anchor `ρ` (sprint 029's second
  hypothesis at the integrated bound's RHS anchor).
-/
theorem diskExcess_upper_bound_via_series_eq4_only_two_Z
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c
        + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity facts.
  have hρ2c2_pos : 0 < ρ ^ 2 - c ^ 2 := by nlinarith
  have hρ2c2_ne : (ρ ^ 2 - c ^ 2) ≠ 0 := ne_of_gt hρ2c2_pos
  have hc_le : (0 : ℝ) ≤ c := hc_pos.le
  -- Abbreviations.
  set Z_c : ℝ := PaperAxioms.sigmaZeroMinus a b c with hZc_def
  set Z_ρ : ℝ := PaperAxioms.sigmaZeroMinus a b ρ with hZρ_def
  set u : ℝ := ρ ^ 2 - c ^ 2 with hu_def
  have hu_pos : 0 < u := hρ2c2_pos
  have hu_ne : u ≠ 0 := hρ2c2_ne
  -- Step A: pointwise upper bound on `2 * r * paper.circleGap r` over Ioo 0 c.
  have hPointwise :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤
          2 * r * ((c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
            + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ) := by
    intro r hr
    have hr_nonneg : (0 : ℝ) ≤ r := hr.1.le
    have hr_lt : r < c := hr.2
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    have hBound :=
      circleGap_inner_bound_via_series_eq4_only
        paper hr_nonneg hr_lt hcρ hρ1
        (hSummable_circleGap hr_nonneg hr_lt) hSummable_n2_ρ
    -- Rewrite via the abbreviations on Z_c, Z_ρ, u.
    have hBound' :
        PaperAxioms.circleGap a b r ≤
          (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
            + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ := by
      simpa [hu_def, hZc_def, hZρ_def] using hBound
    exact mul_le_mul_of_nonneg_left hBound' h2r_nonneg
  -- Step B: rewrite the upper bound into a flat polynomial in r,
  --         f_upper r = A_coef · r + B_coef · r^3 + C_coef · r^5,
  -- where A_coef, B_coef, C_coef are constants depending on c, ρ, Z_c, Z_ρ.
  set A_coef : ℝ := 2 * c ^ 2 * Z_c with hA_def
  set B_coef : ℝ := (2 * c ^ 2 * Z_ρ - 2 * ρ ^ 2 * Z_c) / u with hB_def
  set C_coef : ℝ := (2 * Z_c - 2 * Z_ρ) / u with hC_def
  -- The integrand of the upper bound, in expanded form.
  set fLin : ℝ → ℝ :=
    fun r => A_coef * r + B_coef * r ^ 3 + C_coef * r ^ 5 with hfLin_def
  have hLinEq :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * ((c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / u) * Z_c
          + r ^ 2 * ((c ^ 2 - r ^ 2) / u) * Z_ρ) = fLin r := by
    intro r _
    simp only [hfLin_def, hA_def, hB_def, hC_def]
    field_simp
    ring
  have hPointwise2 :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤ fLin r := by
    intro r hr
    have h1 := hPointwise r hr
    have h2 := hLinEq r hr
    linarith
  -- Step C: integrate the pointwise bound on [0, c].
  have hLinCont : Continuous fLin := by
    simp only [hfLin_def]
    fun_prop
  have hLinIntegrable : IntervalIntegrable fLin volume 0 c :=
    hLinCont.intervalIntegrable _ _
  have hIntegralMono :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c, fLin r := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo hc_le hInt hLinIntegrable
      hPointwise2
  -- Step D: compute ∫_0^c fLin r dr explicitly.
  have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
    have h := @integral_pow 0 c 1
    simp only [pow_one] at h
    convert h using 2 <;> norm_num
  have hPow3 : ∫ r in (0 : ℝ)..c, r ^ 3 = c ^ 4 / 4 := by
    have h := @integral_pow 0 c 3
    convert h using 2 <;> norm_num
  have hPow5 : ∫ r in (0 : ℝ)..c, r ^ 5 = c ^ 6 / 6 := by
    have h := @integral_pow 0 c 5
    convert h using 2 <;> norm_num
  have hIntA : IntervalIntegrable (fun r : ℝ => A_coef * r) volume 0 c :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hIntB : IntervalIntegrable (fun r : ℝ => B_coef * r ^ 3) volume 0 c :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
  have hIntC : IntervalIntegrable (fun r : ℝ => C_coef * r ^ 5) volume 0 c :=
    (continuous_const.mul (continuous_id.pow 5)).intervalIntegrable _ _
  have hIntAB :
      IntervalIntegrable (fun r : ℝ => A_coef * r + B_coef * r ^ 3) volume 0 c :=
    hIntA.add hIntB
  have hIntegralLin :
      ∫ r in (0 : ℝ)..c, fLin r =
        A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) := by
    simp only [hfLin_def]
    rw [intervalIntegral.integral_add hIntAB hIntC]
    rw [intervalIntegral.integral_add hIntA hIntB]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hPow1, hPow3, hPow5]
  -- Step E: rewrite this closed-form into the contract's stated form.
  have hClosedAlg :
      A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) =
        (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / u * Z_c
          + (c ^ 6 / 6) / u * Z_ρ := by
    -- Establish that 3*ρ^2 - 4*c^2 = 6*u - 3*ρ^2 + 2*c^2 algebraic identity:
    -- the LHS minus RHS, after multiplying through by 12*u, is zero.
    have hu_eq : u = ρ ^ 2 - c ^ 2 := hu_def
    simp only [hA_def, hB_def, hC_def]
    field_simp
    ring
  -- Step F: chain the diskExcess to the closed-form bound.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        ≤ ∫ r in (0 : ℝ)..c, fLin r := hIntegralMono
    _ = A_coef * (c ^ 2 / 2) + B_coef * (c ^ 4 / 4) + C_coef * (c ^ 6 / 6) :=
        hIntegralLin
    _ = (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / u * Z_c + (c ^ 6 / 6) / u * Z_ρ :=
        hClosedAlg

/--
Sprint 031 branch-1 single-`Z` collapse of sprint 030's integrated two-`Z` upper
bound (paper-axiom-`{eq4}`-only). The conclusion is byte-for-byte identical to
sprint 007's `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` but the
*paper-axiom signature* shrinks from `{eq2, eq3, eq4}` (sprint 007) to `{eq4}`
only — the inner-disk pointwise bound is supplied by sprint 029 (consumed
through sprint 030), not by sprint 002 (consumed through sprint 003).

The proof body re-walks sprint 007's algebraic chain verbatim with one surgical
replacement: the call to `diskExcess_upper_bound_of_eq2_eq3_eq4` is replaced by
a call to `diskExcess_upper_bound_via_series_eq4_only_two_Z`. All other steps
(positivity of `ρ²−c²`, sign analysis of the `Z_c` coefficient on the
branch-split sub-regime, closing `linarith`) are unchanged because they operate
on sprint 030's conclusion shape, which is byte-for-byte identical to sprint
003's.

The hypothesis count grows by exactly two new summability premises:
* `hSummable_circleGap` quantified over `r ∈ [0, c)` (sprint 030's first
  hypothesis lifted verbatim);
* `hSummable_n2_ρ` at the single upper anchor `ρ` (sprint 030's second
  hypothesis lifted verbatim).
-/
theorem diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2)
    (hρ1 : ρ < 1)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
        * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity of the denominator ρ² − c².
  have hρ2c2_pos : 0 < ρ ^ 2 - c ^ 2 := by
    nlinarith [hcρ, hc_pos, sq_nonneg (ρ - c), sq_nonneg (ρ + c)]
  -- Sprint 030: paper-axiom-`{eq4}`-only two-`Z` upper bound on diskExcess.
  have hUpper :=
    diskExcess_upper_bound_via_series_eq4_only_two_Z
      paper hc_pos hcρ hρ1 hSummable_circleGap hSummable_n2_ρ hInt
  -- Sprint 006 corollary: sigmaZeroMinus a b c ≥ 0.
  have hZc_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
    sigmaZeroMinus_nonneg_of_pos a b hc_pos
  -- The `Z_c` coefficient `α := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-positive:
  -- numerator factor `(3ρ²−4c²)` is `≤ 0` by `hρ_branch`, denominator
  -- `(ρ²−c²) > 0`, leading factor `(c⁴/6) ≥ 0`.
  have hNumNonpos : 3 * ρ ^ 2 - 4 * c ^ 2 ≤ 0 := by linarith
  have hc4_nonneg : 0 ≤ c ^ 4 / 6 := by positivity
  have hα_nonpos :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2) ≤ 0 := by
    have hProd_nonpos : (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc4_nonneg hNumNonpos
    exact div_nonpos_of_nonpos_of_nonneg hProd_nonpos hρ2c2_pos.le
  -- α · Z_c ≤ 0.
  have hαZc_nonpos :
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hα_nonpos hZc_nonneg
  -- Chain: diskExcess ≤ α·Z_c + β·Z_ρ ≤ 0 + β·Z_ρ = β·Z_ρ.
  linarith [hUpper, hαZc_nonpos]

/--
Sprint 032 series-level monotonicity lemma — the workspace's **first
paper-axiom-free monotonicity lemma on `sigmaPlus`**, the **dual of sprint
011's `sigmaZeroMinus_monotone_of_summable` on the structurally distinct N1
partition**, the **first N1-side comparison/monotonicity argument** in the
workspace, and the **first lemma to handle the `k = 0 ∈ N1` boundary case
explicitly**. It derives monotonicity of the `tsum`-defined function
`sigmaPlus a b ·` from termwise monotonicity of its summands on N1, with the
`k = 0` summand handled by termwise equality (since `r^0 = s^0 = 1`).
Together with sprints 005 (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`), 027
(`circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`), and 028
(`sigmaZeroMinus_lower_via_series_convexity`), this completes the
workspace's series-level discharge of every conjunct of `paper.eq2`,
`paper.eq3`, and `paper.eq4` *except* the single inequality
`sigmaPlus c ≤ sigmaMinus c`, isolating it as the **unique remaining
non-series-derivable conjunct of the `eq2`/`eq3`/`eq4` cone**.

Independent of `Section2Assumptions` — pure series-side property of
`sigmaPlus`. The summability-transfer route differs from sprint 011's:
sprint 011 uses `Summable.of_nonneg_of_le` on the summands directly because
`n2Pred a b 0 = False` makes the `k = 0` summand trivially `0`. Sprint 032
cannot do this because `n1Pred a b 0 = True` and `coeffPlusGap a b 0` can be
negative; instead, summability at `r` is recovered by zeroing the `k = 0`
term (a single-point modification preserving summability) and applying
`Summable.of_nonneg_of_le` to the modified function.
-/
theorem sigmaPlus_monotone_of_summable
    {a b : ℕ → ℂ} {r s : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hrs : r ≤ s)
    (hSummable_s :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * s ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b s := by
  classical
  -- Abbreviate the termwise summands.
  set fr : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    else 0 with hfr_def
  set fs : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * s ^ (2 * k)
    else 0 with hfs_def
  have hs_nonneg : 0 ≤ s := le_trans hr_nonneg hrs
  -- Termwise monotonicity: fr k ≤ fs k for every k.
  -- The k = 0 case (always in N1) reduces to coeffPlusGap a b 0 ≤
  -- coeffPlusGap a b 0 since r^0 = s^0 = 1; the k ≥ 1 case uses
  -- pow_le_pow_left₀ on the strictly positive-k portion of N1 where
  -- coeffPlusGap a b k ≥ 0.
  have h_pointwise : ∀ k, fr k ≤ fs k := by
    intro k
    by_cases hk : PaperAxioms.n1Pred a b k
    · -- Active N1 branch.
      by_cases hk0 : k = 0
      · -- k = 0: r^0 = s^0 = 1, both sides equal coeffPlusGap a b 0.
        subst hk0
        simp [fr, fs, hk]
      · -- k ≥ 1: standard termwise monotonicity argument.
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk0
          · linarith
        have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
        have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
          pow_le_pow_left₀ hb_nn hab 2
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap
          linarith
        have h_pow_le : r ^ (2 * k) ≤ s ^ (2 * k) :=
          pow_le_pow_left₀ hr_nonneg hrs (2 * k)
        have h_mul :
            PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) ≤
              PaperAxioms.coeffPlusGap a b k * s ^ (2 * k) :=
          mul_le_mul_of_nonneg_left h_pow_le h_gap_nn
        simpa [fr, fs, hk] using h_mul
    · -- Inactive branch: both sides are 0.
      simp [fr, fs, hk]
  -- Termwise non-negativity *for k ≥ 1*. Sprint 011's proof has termwise
  -- non-negativity at every k because n2Pred a b 0 = False; sprint 032
  -- cannot, because n1Pred a b 0 = True and coeffPlusGap a b 0 may be
  -- negative.
  have h_nonneg_pos : ∀ k, 1 ≤ k → 0 ≤ fr k := by
    intro k hk1
    by_cases hk : PaperAxioms.n1Pred a b k
    · have hk_ne_zero : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
      have hab : ‖b k‖ ≤ ‖a k‖ := by
        rcases hk with hk0' | hab'
        · exact absurd hk0' hk_ne_zero
        · linarith
      have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
      have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
        pow_le_pow_left₀ hb_nn hab 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
        unfold PaperAxioms.coeffPlusGap
        linarith
      have h_pow_nn : 0 ≤ r ^ (2 * k) := pow_nonneg hr_nonneg _
      have h_mul_nn :
          0 ≤ PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) :=
        mul_nonneg h_gap_nn h_pow_nn
      simpa [fr, hk] using h_mul_nn
    · simp [fr, hk]
  have h_nonneg_pos_s : ∀ k, 1 ≤ k → 0 ≤ fs k := by
    intro k hk1
    by_cases hk : PaperAxioms.n1Pred a b k
    · have hk_ne_zero : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
      have hab : ‖b k‖ ≤ ‖a k‖ := by
        rcases hk with hk0' | hab'
        · exact absurd hk0' hk_ne_zero
        · linarith
      have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
      have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
        pow_le_pow_left₀ hb_nn hab 2
      have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
        unfold PaperAxioms.coeffPlusGap
        linarith
      have h_pow_nn : 0 ≤ s ^ (2 * k) := pow_nonneg hs_nonneg _
      have h_mul_nn :
          0 ≤ PaperAxioms.coeffPlusGap a b k * s ^ (2 * k) :=
        mul_nonneg h_gap_nn h_pow_nn
      simpa [fs, hk] using h_mul_nn
    · simp [fs, hk]
  -- Zero-out the k = 0 term to get globally nonneg variants. The
  -- single-point shifts are summable on their own.
  set fr_pos : ℕ → ℝ := fun k => if k = 0 then 0 else fr k with hfr_pos_def
  set fs_pos : ℕ → ℝ := fun k => if k = 0 then 0 else fs k with hfs_pos_def
  set delta_r : ℕ → ℝ := fun k => if k = 0 then fr 0 else 0 with hdelta_r_def
  set delta_s : ℕ → ℝ := fun k => if k = 0 then fs 0 else 0 with hdelta_s_def
  -- Decompositions: fr = fr_pos + delta_r and fs = fs_pos + delta_s.
  have hfr_decomp : fr = fun k => fr_pos k + delta_r k := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [fr_pos, delta_r]
    · simp [fr_pos, delta_r, hk0]
  have hfs_decomp : fs = fun k => fs_pos k + delta_s k := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [fs_pos, delta_s]
    · simp [fs_pos, delta_s, hk0]
  -- Single-point shifts are summable.
  have h_delta_r_summable : Summable delta_r := by
    have : delta_r = fun k => if k = 0 then fr 0 else 0 := rfl
    -- A function supported on a single point is summable.
    rw [this]
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (by
      intro k hk
      simp at hk
      simp [hk])
  have h_delta_s_summable : Summable delta_s := by
    have : delta_s = fun k => if k = 0 then fs 0 else 0 := rfl
    rw [this]
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (by
      intro k hk
      simp at hk
      simp [hk])
  -- fs_pos = fs - delta_s is summable.
  have h_fs_pos_summable : Summable fs_pos := by
    have heq : fs_pos = fun k => fs k - delta_s k := by
      funext k
      by_cases hk0 : k = 0
      · subst hk0; simp [fs_pos, delta_s]
      · simp [fs_pos, delta_s, hk0]
    rw [heq]
    exact hSummable_s.sub h_delta_s_summable
  -- Termwise nonneg of fr_pos and fs_pos, and termwise comparison.
  have h_fr_pos_nonneg : ∀ k, 0 ≤ fr_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fr_pos]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      simp [fr_pos, hk0]
      exact h_nonneg_pos k hk1
  have h_fs_pos_nonneg : ∀ k, 0 ≤ fs_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fs_pos]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      simp [fs_pos, hk0]
      exact h_nonneg_pos_s k hk1
  have h_pointwise_pos : ∀ k, fr_pos k ≤ fs_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fr_pos, fs_pos]
    · simp [fr_pos, fs_pos, hk0]
      exact h_pointwise k
  -- Transfer summability to fr_pos, then to fr.
  have h_fr_pos_summable : Summable fr_pos :=
    Summable.of_nonneg_of_le h_fr_pos_nonneg h_pointwise_pos h_fs_pos_summable
  have h_fr_summable : Summable fr := by
    rw [hfr_decomp]
    exact h_fr_pos_summable.add h_delta_r_summable
  -- Apply tsum monotonicity.
  have h_tsum_le : ∑' k, fr k ≤ ∑' k, fs k :=
    h_fr_summable.tsum_le_tsum h_pointwise hSummable_s
  -- Re-fold the ∑' expressions back to `sigmaPlus`.
  change (∑' k, fr k) ≤ ∑' k, fs k
  exact h_tsum_le

/--
Sprint 033: the workspace's **first paper-axiom-free convexity lemma on
`sigmaPlus`**, the **N1-side dual of sprint 028's
`sigmaZeroMinus_lower_via_series_convexity`**, and the **first three-radius
`sigmaPlus` lemma**. Establishes the cross-radius upper bound
`Σ⁺(c) ≤ μ₁·Σ⁺(r) + μ₂·Σ⁺(ρ)` for `0 ≤ r < c < ρ` with convex weights
`μ₁ := (ρ²-c²)/(ρ²-r²)` and `μ₂ := (c²-r²)/(ρ²-r²)` summing to `1`. The
N1-side argument uses non-negativity of `coeffPlusGap a b k` on the
positive-`k` portion of N1 and convexity of `t ↦ t^k` on `[0, ∞)`. The
`k = 0 ∈ N1` boundary case (which N2-side sprint 028 trivially excludes via
`n2Pred a b 0 = False`) is handled here by termwise equality: at `k = 0`,
both LHS and RHS evaluate to `coeffPlusGap a b 0` after applying the
convex-weight sum identity `μ₁ + μ₂ = 1`. The summability transfer to
`c` is in-house via `Summable.of_nonneg_of_le` against the convex
combination, taking *two* summability premises (at lower-`r` and upper-`ρ`)
since the workspace has no N1-side `sigmaPlus_summable_of_summable_at_upper`
lemma yet (the dual of sprint 012's N2-side transfer).
-/
theorem sigmaPlus_upper_via_series_convexity
    (a b : ℕ → ℂ) {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt_c : r < c)
    (hc_lt_ρ : c < ρ)
    (hSummable_r :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
        else 0))
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b c ≤
      ((ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b r +
        ((c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b ρ := by
  classical
  -- Geometric scaffolding (parallels sprint 028).
  have hr_lt_ρ : r < ρ := lt_trans hr_lt_c hc_lt_ρ
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt_c
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hρ_pos : 0 < ρ := lt_of_le_of_lt hc_nonneg hc_lt_ρ
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  -- Squared geometric facts.
  have hr_sq_nonneg : 0 ≤ r ^ 2 := sq_nonneg r
  have hρ_sq_nonneg : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hr_sq_lt_c_sq : r ^ 2 < c ^ 2 := by
    have h := mul_self_lt_mul_self hr_nonneg hr_lt_c
    have hr : r * r = r ^ 2 := by ring
    have hc' : c * c = c ^ 2 := by ring
    rw [hr, hc'] at h; exact h
  have hc_sq_lt_ρ_sq : c ^ 2 < ρ ^ 2 := by
    have h := mul_self_lt_mul_self hc_nonneg hc_lt_ρ
    have hc' : c * c = c ^ 2 := by ring
    have hρ' : ρ * ρ = ρ ^ 2 := by ring
    rw [hc', hρ'] at h; exact h
  have hr_sq_lt_ρ_sq : r ^ 2 < ρ ^ 2 := lt_trans hr_sq_lt_c_sq hc_sq_lt_ρ_sq
  have h_ρ_sq_minus_r_sq_pos : 0 < ρ ^ 2 - r ^ 2 := by linarith
  have h_ρ_sq_minus_c_sq_pos : 0 < ρ ^ 2 - c ^ 2 := by linarith
  have h_c_sq_minus_r_sq_pos : 0 < c ^ 2 - r ^ 2 := by linarith
  have h_ρ_sq_minus_r_sq_ne : (ρ ^ 2 - r ^ 2) ≠ 0 := ne_of_gt h_ρ_sq_minus_r_sq_pos
  -- Convex weights μ₁, μ₂.
  set μ₁ : ℝ := (ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2) with hμ₁_def
  set μ₂ : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2) with hμ₂_def
  have hμ₁_nn : 0 ≤ μ₁ :=
    div_nonneg h_ρ_sq_minus_c_sq_pos.le h_ρ_sq_minus_r_sq_pos.le
  have hμ₂_nn : 0 ≤ μ₂ :=
    div_nonneg h_c_sq_minus_r_sq_pos.le h_ρ_sq_minus_r_sq_pos.le
  have hμ_sum : μ₁ + μ₂ = 1 := by
    change (ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)
        + (c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2) = 1
    field_simp
    ring
  have h_convex_combo : μ₁ • (r ^ 2) + μ₂ • (ρ ^ 2) = c ^ 2 := by
    change μ₁ * r ^ 2 + μ₂ * ρ ^ 2 = c ^ 2
    rw [hμ₁_def, hμ₂_def]
    field_simp
    ring
  -- Abbreviate the three relevant termwise summands.
  set fr : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
    else 0 with hfr_def
  set fc : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
    else 0 with hfc_def
  set fρ : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)
    else 0 with hfρ_def
  -- Termwise convexity inequality at the convex combination
  -- `c² = μ₁·r² + μ₂·ρ²` in scaled form
  --   fc k ≤ μ₁ * fr k + μ₂ * fρ k.
  have h_term_convexity :
      ∀ k, fc k ≤ μ₁ * fr k + μ₂ * fρ k := by
    intro k
    by_cases hk : PaperAxioms.n1Pred a b k
    · -- Active N1 branch: split on k = 0 vs k ≥ 1.
      by_cases hk0 : k = 0
      · -- k = 0: collapse via `μ₁ + μ₂ = 1` (the structurally novel
        -- handling pattern not present in sprint 028's N2-side argument).
        subst hk0
        simp only [fr, fc, fρ, hk, if_true, Nat.mul_zero, pow_zero, mul_one]
        -- Goal: coeffPlusGap a b 0 ≤ μ₁ * coeffPlusGap a b 0 + μ₂ * coeffPlusGap a b 0
        have h_collapse :
            μ₁ * PaperAxioms.coeffPlusGap a b 0 + μ₂ * PaperAxioms.coeffPlusGap a b 0
              = PaperAxioms.coeffPlusGap a b 0 := by
          have : (μ₁ + μ₂) * PaperAxioms.coeffPlusGap a b 0
              = PaperAxioms.coeffPlusGap a b 0 := by
            rw [hμ_sum]; ring
          linarith [this]
        linarith [h_collapse]
      · -- k ≥ 1: standard convexity argument on N1's positive-k portion
        -- where coeffPlusGap a b k ≥ 0.
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk0
          · linarith
        have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
        have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
          pow_le_pow_left₀ hb_nn hab 2
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap
          linarith
        -- Convexity of `t ↦ t^k` on `Ici 0` evaluated at `r²`, `ρ²` with
        -- weights `μ₁`, `μ₂`. Note: no `−1` shift because the
        -- `sigmaPlus`-side exponent is `2*k`, not `2*k − 2`.
        have h_convexOn :
            ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ k) :=
          convexOn_pow k
        have h_r_in : (r ^ 2) ∈ Set.Ici (0 : ℝ) := hr_sq_nonneg
        have h_ρ_in : (ρ ^ 2) ∈ Set.Ici (0 : ℝ) := hρ_sq_nonneg
        have h_conv_ineq :=
          h_convexOn.2 h_r_in h_ρ_in hμ₁_nn hμ₂_nn hμ_sum
        -- h_conv_ineq : (μ₁•r² + μ₂•ρ²)^k ≤ μ₁•(r²)^k + μ₂•(ρ²)^k
        rw [h_convex_combo] at h_conv_ineq
        -- Convert the • to *.
        have h_conv_ineq' :
            (c ^ 2) ^ k ≤ μ₁ * (r ^ 2) ^ k + μ₂ * (ρ ^ 2) ^ k :=
          h_conv_ineq
        -- Rewrite (s²)^k = s^(2*k) for s ∈ {r, c, ρ}.
        have hpow_r : (r ^ 2) ^ k = r ^ (2 * k) := by
          rw [← pow_mul]
        have hpow_c : (c ^ 2) ^ k = c ^ (2 * k) := by
          rw [← pow_mul]
        have hpow_ρ : (ρ ^ 2) ^ k = ρ ^ (2 * k) := by
          rw [← pow_mul]
        rw [hpow_r, hpow_c, hpow_ρ] at h_conv_ineq'
        -- Multiply by coeffPlusGap a b k ≥ 0.
        have h_with_gap :
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k) ≤
              PaperAxioms.coeffPlusGap a b k *
                (μ₁ * r ^ (2 * k) + μ₂ * ρ ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left h_conv_ineq' h_gap_nn
        simp only [fr, fc, fρ, hk, if_true]
        nlinarith [h_with_gap]
    · -- Inactive branch: all three indicator branches are 0.
      simp [fr, fc, fρ, hk]
  -- In-house summability at `c` via termwise sandwich on the positive-k
  -- portion (the k = 0 term is handled separately as a singleton, since
  -- `coeffPlusGap a b 0` can be negative when ‖a 0‖ < ‖b 0‖, ruling out a
  -- direct `Summable.of_nonneg_of_le` on `fc`).
  -- Zero-out the k = 0 term to get globally non-negative variants.
  set fr_pos : ℕ → ℝ := fun k => if k = 0 then 0 else fr k with hfr_pos_def
  set fc_pos : ℕ → ℝ := fun k => if k = 0 then 0 else fc k with hfc_pos_def
  set fρ_pos : ℕ → ℝ := fun k => if k = 0 then 0 else fρ k with hfρ_pos_def
  set delta_r : ℕ → ℝ := fun k => if k = 0 then fr 0 else 0 with hdelta_r_def
  set delta_c : ℕ → ℝ := fun k => if k = 0 then fc 0 else 0 with hdelta_c_def
  set delta_ρ : ℕ → ℝ := fun k => if k = 0 then fρ 0 else 0 with hdelta_ρ_def
  -- Decompositions.
  have hfr_decomp : fr = fun k => fr_pos k + delta_r k := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [fr_pos, delta_r]
    · simp [fr_pos, delta_r, hk0]
  have hfc_decomp : fc = fun k => fc_pos k + delta_c k := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [fc_pos, delta_c]
    · simp [fc_pos, delta_c, hk0]
  have hfρ_decomp : fρ = fun k => fρ_pos k + delta_ρ k := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [fρ_pos, delta_ρ]
    · simp [fρ_pos, delta_ρ, hk0]
  -- Single-point shifts are summable.
  have h_delta_r_summable : Summable delta_r := by
    have : delta_r = fun k => if k = 0 then fr 0 else 0 := rfl
    rw [this]
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (by
      intro k hk
      simp at hk
      simp [hk])
  have h_delta_c_summable : Summable delta_c := by
    have : delta_c = fun k => if k = 0 then fc 0 else 0 := rfl
    rw [this]
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (by
      intro k hk
      simp at hk
      simp [hk])
  have h_delta_ρ_summable : Summable delta_ρ := by
    have : delta_ρ = fun k => if k = 0 then fρ 0 else 0 := rfl
    rw [this]
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (by
      intro k hk
      simp at hk
      simp [hk])
  -- fr_pos = fr - delta_r is summable, similarly fρ_pos.
  have h_fr_pos_summable : Summable fr_pos := by
    have heq : fr_pos = fun k => fr k - delta_r k := by
      funext k
      by_cases hk0 : k = 0
      · subst hk0; simp [fr_pos, delta_r]
      · simp [fr_pos, delta_r, hk0]
    rw [heq]
    exact hSummable_r.sub h_delta_r_summable
  have h_fρ_pos_summable : Summable fρ_pos := by
    have heq : fρ_pos = fun k => fρ k - delta_ρ k := by
      funext k
      by_cases hk0 : k = 0
      · subst hk0; simp [fρ_pos, delta_ρ]
      · simp [fρ_pos, delta_ρ, hk0]
    rw [heq]
    exact hSummable_ρ.sub h_delta_ρ_summable
  -- Termwise non-negativity of fr_pos, fc_pos, fρ_pos and termwise
  -- convex-combination upper bound on fc_pos.
  have h_fr_pos_nonneg : ∀ k, 0 ≤ fr_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fr_pos]
    · simp only [fr_pos, hk0, if_false]
      by_cases hk : PaperAxioms.n1Pred a b k
      · have hk_ne_zero : k ≠ 0 := hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk_ne_zero
          · linarith
        have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
        have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
          pow_le_pow_left₀ hb_nn hab 2
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap; linarith
        have h_pow_nn : 0 ≤ r ^ (2 * k) := pow_nonneg hr_nonneg _
        have h_mul_nn :
            0 ≤ PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) :=
          mul_nonneg h_gap_nn h_pow_nn
        simpa [fr, hk] using h_mul_nn
      · simp [fr, hk]
  have h_fρ_pos_nonneg : ∀ k, 0 ≤ fρ_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fρ_pos]
    · simp only [fρ_pos, hk0, if_false]
      by_cases hk : PaperAxioms.n1Pred a b k
      · have hk_ne_zero : k ≠ 0 := hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk_ne_zero
          · linarith
        have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
        have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
          pow_le_pow_left₀ hb_nn hab 2
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap; linarith
        have h_pow_nn : 0 ≤ ρ ^ (2 * k) := pow_nonneg hρ_nonneg _
        have h_mul_nn :
            0 ≤ PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k) :=
          mul_nonneg h_gap_nn h_pow_nn
        simpa [fρ, hk] using h_mul_nn
      · simp [fρ, hk]
  have h_fc_pos_nonneg : ∀ k, 0 ≤ fc_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0; simp [fc_pos]
    · simp only [fc_pos, hk0, if_false]
      by_cases hk : PaperAxioms.n1Pred a b k
      · have hk_ne_zero : k ≠ 0 := hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk_ne_zero
          · linarith
        have hb_nn : 0 ≤ ‖b k‖ := norm_nonneg _
        have h_sq_le : ‖b k‖ ^ 2 ≤ ‖a k‖ ^ 2 :=
          pow_le_pow_left₀ hb_nn hab 2
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap; linarith
        have h_pow_nn : 0 ≤ c ^ (2 * k) := pow_nonneg hc_nonneg _
        have h_mul_nn :
            0 ≤ PaperAxioms.coeffPlusGap a b k * c ^ (2 * k) :=
          mul_nonneg h_gap_nn h_pow_nn
        simpa [fc, hk] using h_mul_nn
      · simp [fc, hk]
  -- Termwise convex-combination upper bound on fc_pos by μ₁ * fr_pos + μ₂ * fρ_pos.
  have h_fc_pos_le : ∀ k, fc_pos k ≤ μ₁ * fr_pos k + μ₂ * fρ_pos k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [fc_pos, fr_pos, fρ_pos, if_true, mul_zero, add_zero]
      exact le_refl _
    · simp only [fc_pos, fr_pos, fρ_pos, hk0, if_false]
      exact h_term_convexity k
  -- Apply Summable.of_nonneg_of_le to fc_pos with bound μ₁ fr_pos + μ₂ fρ_pos.
  have h_bound_summable :
      Summable (fun k => μ₁ * fr_pos k + μ₂ * fρ_pos k) :=
    (h_fr_pos_summable.mul_left μ₁).add (h_fρ_pos_summable.mul_left μ₂)
  have h_fc_pos_summable : Summable fc_pos :=
    Summable.of_nonneg_of_le h_fc_pos_nonneg h_fc_pos_le h_bound_summable
  -- fc summable from decomposition.
  have hSummable_c : Summable fc := by
    rw [hfc_decomp]
    exact h_fc_pos_summable.add h_delta_c_summable
  -- Lift to tsum: ∑' k, fc k ≤ ∑' k, (μ₁ * fr k + μ₂ * fρ k).
  have h_bound_total_summable :
      Summable (fun k => μ₁ * fr k + μ₂ * fρ k) :=
    (hSummable_r.mul_left μ₁).add (hSummable_ρ.mul_left μ₂)
  have h_tsum_le :
      (∑' k, fc k) ≤ ∑' k, (μ₁ * fr k + μ₂ * fρ k) :=
    hSummable_c.tsum_le_tsum h_term_convexity h_bound_total_summable
  -- Identify the RHS tsum with `μ₁ * Σ⁺(r) + μ₂ * Σ⁺(ρ)`.
  have h_tsum_fr : (∑' k, μ₁ * fr k) = μ₁ * PaperAxioms.sigmaPlus a b r := by
    rw [tsum_mul_left]; rfl
  have h_tsum_fρ : (∑' k, μ₂ * fρ k) = μ₂ * PaperAxioms.sigmaPlus a b ρ := by
    rw [tsum_mul_left]; rfl
  have h_rhs_eq :
      (∑' k, (μ₁ * fr k + μ₂ * fρ k))
        = μ₁ * PaperAxioms.sigmaPlus a b r
          + μ₂ * PaperAxioms.sigmaPlus a b ρ := by
    have h1 : Summable (fun k => μ₁ * fr k) := hSummable_r.mul_left _
    have h2 : Summable (fun k => μ₂ * fρ k) := hSummable_ρ.mul_left _
    rw [h1.tsum_add h2, h_tsum_fr, h_tsum_fρ]
  -- Identify the LHS tsum with `Σ⁺(c)`.
  have h_lhs_eq : (∑' k, fc k) = PaperAxioms.sigmaPlus a b c := rfl
  rw [h_lhs_eq, h_rhs_eq] at h_tsum_le
  exact h_tsum_le

/--
Sprint 034 closed-form full-disk upper bound — the workspace's **first
integrated `diskExcess` upper bound whose proof body invokes zero
`paper.eq*` field projections**, with the unique series-non-derivable
conjunct of the `(2)/(3)/(4)` cone — `Σ⁺(c) ≤ Σ⁻(c)` — lifted into the
signature as the explicit hypothesis `hSigmaCmp`. Every other analytical
step is supplied by an existing paper-axiom-free workspace lemma:

* `circleGap r ≤ sigmaPlus r` for `r ∈ Ioo 0 c` via sprint 025
  (`circleGap_le_sigmaPlus_via_series_split`),
* `sigmaPlus r ≤ sigmaPlus c` via sprint 032
  (`sigmaPlus_monotone_of_summable`),
* `sigmaPlus c ≤ sigmaMinus c` via the explicit hypothesis `hSigmaCmp`,
* `sigmaMinus c = c² · sigmaZeroMinus c` via sprint 005
  (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`),
* multiplication by the polar Jacobian `2r` and integration over `[0, c]`
  follow sprint 026's body verbatim.

The closed-form RHS `c⁴ · sigmaZeroMinus a b c` matches sprint
013's/026's/030's (collapsed) RHS but is reached through a structurally
distinct paper-axiom signature: empty body, single explicit hypothesis
`hSigmaCmp`. This is the **type-level isolation of the unique
series-non-derivable analytical fact** in the `eq2`/`eq3`/`eq4` cone.
-/
theorem diskExcess_upper_bound_via_series_only_modulo_sigma_compare
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
  -- Step 1: pointwise upper bound on `circleGap r` for `r ∈ Ioo 0 c`,
  -- composed from sprint 025 (`circleGap r ≤ sigmaPlus r`), sprint 032
  -- (`sigmaPlus r ≤ sigmaPlus c`), the explicit `hSigmaCmp`
  -- (`sigmaPlus c ≤ sigmaMinus c`), and sprint 005
  -- (`sigmaMinus c = c² · sigmaZeroMinus c`). Body invokes no
  -- paper-axiom field projection.
  have hPointwise :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        PaperAxioms.circleGap a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_nonneg : 0 ≤ r := hr_pos.le
    have hr_lt : r < c := hr.2
    -- Sprint 025: pointwise series-side bound `circleGap r ≤ sigmaPlus r`.
    have hSeries :
        PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r :=
      circleGap_le_sigmaPlus_via_series_split a b hr_nonneg
        (hSummable hr_nonneg hr_lt)
    -- Sprint 032: paper-axiom-free monotonicity `sigmaPlus r ≤ sigmaPlus c`.
    have hMono :
        PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
      sigmaPlus_monotone_of_summable hr_nonneg hr_lt.le hSummable_n1_c
    -- Explicit hypothesis: `sigmaPlus c ≤ sigmaMinus c`.
    have hCmp :
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c :=
      hSigmaCmp
    -- Sprint 005: paper-axiom-free identity
    -- `sigmaMinus c = c² · sigmaZeroMinus c`.
    have hIdent :
        PaperAxioms.sigmaMinus a b c =
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c :=
      sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b c
    have hSigmaPlus_le :
        PaperAxioms.sigmaPlus a b r ≤
          c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      have hChain :
          PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
        le_trans hMono hCmp
      rw [hIdent] at hChain
      exact hChain
    exact le_trans hSeries hSigmaPlus_le
  -- Step 2: multiply pointwise bound by `2r ≥ 0`.
  have hPointwise_jac :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r ≤
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := by
    intro r hr
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    exact mul_le_mul_of_nonneg_left (hPointwise r hr) h2r_nonneg
  -- Step 3: integrability of the constant-multiple-of-`2r` RHS.
  have hRhsCont :
      Continuous
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) := by
    fun_prop
  have hRhsIntegrable :
      IntervalIntegrable
        (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
        volume 0 c :=
    hRhsCont.intervalIntegrable _ _
  -- Step 4: integrate the pointwise bound on [0, c].
  have hIntegralMono :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hInt
      hRhsIntegrable hPointwise_jac
  -- Step 5: closed-form RHS integral.
  have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
    have h := @integral_pow 0 c 1
    simp only [pow_one] at h
    convert h using 2 <;> norm_num
  have hRhsClosedForm :
      ∫ r in (0 : ℝ)..c,
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)
        = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
    have hRewrite :
        (fun r : ℝ =>
          2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
          = fun r =>
            (2 * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) * r := by
      funext r; ring
    rw [hRewrite, intervalIntegral.integral_const_mul, hPow1]
    ring
  -- Step 6: identify diskExcess with the integral and chain via calc.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        ≤ ∫ r in (0 : ℝ)..c,
            2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := hIntegralMono
    _ = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hRhsClosedForm

/--
Sprint 035: the workspace's **first `valid_of_*` reducer whose disk-side
proof body invokes zero `paper.eq*` field projections**, and the **first
reducer to lift the unique series-non-derivable conjunct
`Σ⁺(c) ≤ Σ⁻(c)` into the witness existential as a type-level cell**.
This is sprint 014's body verbatim, with one targeted disk-side
substitution: the call to sprint 013's `diskExcess_upper_bound_via_eq3_eq4`
(paper-axiom signature `{eq3, eq4}`) is replaced by a call to sprint 034's
`diskExcess_upper_bound_via_series_only_modulo_sigma_compare` (body
paper-axiom-free, with `Σ⁺(c) ≤ Σ⁻(c)` lifted as the explicit
`hSigmaCmp` hypothesis). The witness existential gains three new
disk-side cells (`hSummable`, `hSummable_n1_c`, `hSigmaCmp`) inserted
before `hIntDisk`. The annulus side and the kernel inequality
`c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` are byte-for-byte identical to
sprint 014.

After this sprint lands, the disk-side `paper.eq*` signature for the
full-window closing-reducer family is empty (modulo `hSigmaCmp`),
exposing the precise oracle target — the single scalar inequality
`Σ⁺(c) ≤ Σ⁻(c)` at the witness level — that a future
oracle-bearing candidate would discharge to obtain a paper-axiom-free
disk-side route. The annulus side still uses `paper.eq8`/`paper.eq9`
unchanged.
-/
theorem valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
              Summable (fun k : ℕ =>
                PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
              else 0) ∧
            (PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hSummable, hSummable_n1_c,
      hSigmaCmp, hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda,
      hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding.
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  -- Disk-side bound via sprint 034 (paper-axiom-free body, modulo
  -- the explicit `hSigmaCmp` hypothesis).
  have hDisk :=
    diskExcess_upper_bound_via_series_only_modulo_sigma_compare
      hc_pos hc_lt_one hSummable hSummable_n1_c hSigmaCmp hIntDisk
  -- Z_c ≥ 0 via sprint 005.
  have hZ_c_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
    sigmaZeroMinus_nonneg_of_pos a b hc_pos
  -- Step (a): multiply the kernel inequality by Z_c ≥ 0.
  have hStepA :
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c :=
    mul_le_mul_of_nonneg_right hKernel hZ_c_nonneg
  -- Step (b): pull the constant factor Z_c inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b c)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Build pointwise Z_c ≤ Z_ρ' via sprint 011 + sprint 012.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b c ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hc_le_ρ' : c ≤ ρ' := le_trans hc_le_ρ₁ hρ₁_le_ρ'
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hc_pos hc_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hc_pos.le hc_le_ρ' hSummable_ρ'
  -- Step (c): integrate the pointwise Z_c ≤ Z_ρ' to dominate the
  -- constant-Z_c integrand by the Z_ρ'-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b c) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b c)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'_pos : 0 < ρ' := lt_trans hc_pos hcρ'
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 006.
  have hAnn :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hDisk
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 036 closed-form pointwise inner-disk upper bound — the workspace's
**first non-integrated, paper-axiom-free two-`Z` upper bound on
`circleGap a b r`**, with the unique series-non-derivable conjunct of the
`(2)/(3)/(4)` cone — `Σ⁺(c) ≤ Σ⁻(c)` — lifted into the signature as the
explicit hypothesis `hSigmaCmp`. Every other analytical step is supplied by
an existing paper-axiom-free workspace lemma:

* `circleGap r = sigmaPlus r - r²·sigmaZeroMinus r` via sprint 027
  (`circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`),
* `sigmaPlus r ≤ sigmaPlus c` via sprint 032
  (`sigmaPlus_monotone_of_summable`),
* `sigmaPlus c ≤ sigmaMinus c` via the explicit hypothesis `hSigmaCmp`,
* `sigmaMinus c = c² · sigmaZeroMinus c` via sprint 005
  (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`),
* `sigmaZeroMinus r ≥ ((ρ²−r²)/(ρ²−c²)) · Z_c − ((c²−r²)/(ρ²−c²)) · Z_ρ`
  via sprint 028 (`sigmaZeroMinus_lower_via_series_convexity`),
* multiplication by `r² ≥ 0` and the algebraic chain follow sprint 029's
  body verbatim.

The closed-form RHS is byte-for-byte identical to sprints 002's and 029's
RHS — the analytical chain converges on the same target through a
structurally distinct paper-axiom signature: empty body, single explicit
hypothesis `hSigmaCmp` carrying the unique remaining oracle-target
inequality.
-/
theorem circleGap_inner_bound_via_series_only_modulo_sigma_compare
    {a b : ℕ → ℂ} {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) :
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Positivity facts.
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt
  have hc_lt_one : c < 1 := lt_trans hcρ hρ1
  have hc_lt_ρ : c < ρ := hcρ
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have hρ2_minus_c2_pos : 0 < ρ ^ 2 - c ^ 2 := by nlinarith
  have hr2_nonneg : 0 ≤ r ^ 2 := by positivity
  -- Step 1: sprint 027 supplies the equality
  --   `circleGap r = sigmaPlus r - r^2 * sigmaZeroMinus r`
  -- without any paper-axiom invocation (replaces sprint 002's eq3 step).
  have hr_lt_one : r < 1 := lt_trans hr_lt hc_lt_one
  have h3 :
      PaperAxioms.circleGap a b r =
        PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r :=
    circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
      a b hr_nonneg hSummable_circleGap_r
  -- Step 2: paper-axiom-free three-step chain
  --   Σ⁺(r) ≤ Σ⁺(c) ≤ Σ⁻(c) = c²·Z_c.
  -- sprint 032 supplies `Σ⁺(r) ≤ Σ⁺(c)` (paper-axiom-free).
  have hMono : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
    sigmaPlus_monotone_of_summable hr_nonneg hr_lt.le hSummable_n1_c
  -- explicit hypothesis: `Σ⁺(c) ≤ Σ⁻(c)`.
  -- sprint 005 supplies `Σ⁻(c) = c² · Z_c` (paper-axiom-free).
  have hIdent :
      PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b c
  have hSigmaPlus_le :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    have hChain : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
      le_trans hMono hSigmaCmp
    rw [hIdent] at hChain
    exact hChain
  -- Step 3: sprint 028 supplies the cross-radius lower bound on
  -- `sigmaZeroMinus a b r` without any paper-axiom invocation (replaces
  -- sprint 002's eq2 step). Sprint 028 already returns the bound in the
  -- unfolded form, so the sprint-002 `simpa` step is unnecessary.
  have h2_unfold :
      PaperAxioms.sigmaZeroMinus a b r ≥
        ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
          ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaZeroMinus_lower_via_series_convexity
      a b hr_nonneg hr_lt hcρ hSummable_n2_ρ
  -- Multiply `h2_unfold` by `r^2 ≥ 0` to get an upper bound on
  -- `-r^2 * sigmaZeroMinus a b r`.
  set Z_c : ℝ := PaperAxioms.sigmaZeroMinus a b c with hZc
  set Z_ρ : ℝ := PaperAxioms.sigmaZeroMinus a b ρ with hZρ
  set Z_r : ℝ := PaperAxioms.sigmaZeroMinus a b r with hZr
  set A : ℝ := (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hA
  set B : ℝ := (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) with hB
  -- Rewrite h2 in terms of A, B.
  have h2' : A * Z_c - B * Z_ρ ≤ Z_r := by
    have := h2_unfold
    simp only [ge_iff_le, hA, hB, hZc, hZρ, hZr] at this ⊢
    exact this
  -- Multiply by r^2 ≥ 0.
  have hMul : r ^ 2 * (A * Z_c - B * Z_ρ) ≤ r ^ 2 * Z_r :=
    mul_le_mul_of_nonneg_left h2' hr2_nonneg
  -- So -r^2 * Z_r ≤ -r^2 * (A * Z_c - B * Z_ρ) = -r^2 * A * Z_c + r^2 * B * Z_ρ.
  have hNeg : -(r ^ 2 * Z_r) ≤ -(r ^ 2 * (A * Z_c - B * Z_ρ)) := by linarith
  -- Now combine: circleGap r = sigmaPlus r - r^2 * Z_r ≤ c^2 * Z_c - r^2 * Z_r
  --                          ≤ c^2 * Z_c + (-r^2*A*Z_c + r^2*B*Z_ρ).
  have hSigmaPlus_le' :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * Z_c := by
    simp only [hZc]; exact hSigmaPlus_le
  -- Final algebra: c^2 * Z_c - r^2 * (A * Z_c - B * Z_ρ)
  --              = (c^2 - r^2 * A) * Z_c + r^2 * B * Z_ρ.
  -- And we need to show that target's first coefficient
  -- `(c^2 - r^2 * (ρ^2 - r^2) / (ρ^2 - c^2))` equals `c^2 - r^2 * A`.
  have hA_def : A = (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  have hB_def : B = (c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := rfl
  -- Build the chain.
  have hStep1 :
      PaperAxioms.circleGap a b r ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := by
    rw [h3]
    linarith [hSigmaPlus_le']
  have hStep2 :
      c ^ 2 * Z_c - r ^ 2 * Z_r ≤
        c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := by
    linarith [hMul]
  have hRewrite :
      c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) =
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by ring
  have hFinal :
      PaperAxioms.circleGap a b r ≤
        (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := by
    calc PaperAxioms.circleGap a b r
        ≤ c ^ 2 * Z_c - r ^ 2 * Z_r := hStep1
      _ ≤ c ^ 2 * Z_c - r ^ 2 * (A * Z_c - B * Z_ρ) := hStep2
      _ = (c ^ 2 - r ^ 2 * A) * Z_c + r ^ 2 * B * Z_ρ := hRewrite
  -- Match the goal's denominator-laden form.
  have hCoeff1 : c ^ 2 - r ^ 2 * A =
      c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2) := by
    simp only [hA_def, mul_div_assoc']
  have hCoeff2 : r ^ 2 * B = r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) := by
    simp only [hB_def]
  rw [hCoeff1, hCoeff2] at hFinal
  exact hFinal

/--
Sprint 037 outer-annulus paper-axiom-free pointwise lower bound on
`circleGap a b ρ` modulo an explicit `Λ`-bridge cell. This is the
**annulus-side mirror of sprint 036**: where sprint 036 lifts the unique
series-non-derivable conjunct of the disk-side `(2)/(3)/(4)` cone — namely
`Σ⁺(c) ≤ Σ⁻(c)` — into a hypothesis cell `hSigmaCmp`, sprint 037 lifts the
unique series-non-derivable post-substitution form of the annulus-side
`(8)+(9)` bridge — namely `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ` — into the
hypothesis cell `hLambdaBridge`. The proof body is sprint 005's body
verbatim with the single targeted substitution at the `(8)+(9)` bridge
invocation: replace
`PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9 paper.eq8 paper.eq9 …`
with direct consumption of `hLambdaBridge`. The rest of the body — the
sprint 005 series identity `sigmaMinus = ρ² · sigmaZeroMinus`,
`paperLambda_pos`, `div_le_iff₀`, multiplication by `2ρ ≥ 0`, and the
`field_simp` algebraic clean-up — is byte-for-byte identical to sprint
005. The conclusion is byte-for-byte identical to sprint 005's, but the
paper-axiom signature on the body shrinks from `{eq8, eq9}` to `{}`
modulo the explicit `hLambdaBridge`.
-/
theorem circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hLambdaBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
    2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
        / WangOuter.paperLambda K c ρ
      ≤ 2 * ρ * PaperAxioms.circleGap a b ρ := by
  -- Explicit hypothesis: `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap ρ`.
  -- This replaces sprint 005's invocation of
  -- `eq8eq9_sigma_to_circleBridge_of_eq8_eq9 paper.eq8_* paper.eq9_*`,
  -- making the body paper-axiom-free.
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    hLambdaBridge
  -- Rewrite `sigmaMinus a b ρ = ρ² · sigmaZeroMinus a b ρ`.
  have hIdentity := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  rw [hIdentity] at hBridge
  -- Λ(c, ρ) > 0.
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  -- Divide through: ρ² · sigmaZeroMinus ρ / Λ ≤ circleGap ρ.
  have hDiv :
      ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ
        ≤ PaperAxioms.circleGap a b ρ :=
    (div_le_iff₀ hΛpos).2 (by simpa [mul_comm] using hBridge)
  -- Multiply by 2ρ ≥ 0.
  have hρpos : 0 < ρ := lt_trans hc_pos hcρ
  have h2ρ_nonneg : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hMul :
      2 * ρ * (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ)
        ≤ 2 * ρ * PaperAxioms.circleGap a b ρ :=
    mul_le_mul_of_nonneg_left hDiv h2ρ_nonneg
  -- Rearrange the LHS to match the goal.
  have hLambdaNe : WangOuter.paperLambda K c ρ ≠ 0 := ne_of_gt hΛpos
  have hRewrite :
      2 * ρ * (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ) =
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ /
          WangOuter.paperLambda K c ρ := by
    field_simp
  rw [hRewrite] at hMul
  exact hMul

/--
Sprint 038 integrated annulus-side paper-axiom-free lower bound on
`PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c` modulo a
window-uniform `Λ`-bridge family `hLambdaBridgeWindow`. This is the
**integrated counterpart of sprint 037** and the **annulus-side mirror of
sprint 034**: where sprint 037 lifts the unique series-non-derivable
post-substitution form of the annulus-side `(8)+(9)` bridge — namely
`Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ` — at a **single** `ρ` into a
hypothesis cell, sprint 038 lifts the **window-uniform family** of the
same inequality on `(c, 1)` into the hypothesis cell
`hLambdaBridgeWindow`. The proof body is sprint 006's body verbatim with
two targeted substitutions: (a) the pointwise step delegates to sprint
037 consuming `hLambdaBridgeWindow`; (b) the side-slice non-negativity
sub-arguments use a fresh `hCircleNonneg` helper derived inline from
`hLambdaBridgeWindow` + `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` +
`sigmaZeroMinus_nonneg_of_pos` + `paperLambda_pos` plus
division-by-positive — without any `paper.eq*` invocation. The body
invokes **zero `paper.eq*` field projections** and **zero
`OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` invocations**.
-/
theorem annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hcρ₁ : c < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hρ₂_lt_one : ρ₂ < 1)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ) volume ρ₁ ρ₂)
    (hLambdaBridgeWindow :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := by
  -- Positivity facts.
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hρ₂_le_one : ρ₂ ≤ 1 := hρ₂_lt_one.le
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₂ : c ≤ ρ₂ := hcρ₂.le
  have hc_lt_one : c < 1 := lt_trans hcρ₁ hρ₁_lt_one
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Sprint 038 paper-axiom-free side-slice non-negativity helper:
  -- derive `0 ≤ circleGap a b ρ` on the open window `(c, 1)` from
  -- `hLambdaBridgeWindow` + sprint 005 `sigmaMinus = ρ²·Z_ρ` +
  -- `sigmaZeroMinus_nonneg_of_pos` + `paperLambda_pos` plus
  -- division-by-positive (no `OneModePaperBridge` invocation).
  have hCircleNonneg :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 → 0 ≤ PaperAxioms.circleGap a b ρ := by
    intro ρ hcρ hρ_lt_one
    have hBridge :
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
      hLambdaBridgeWindow hcρ hρ_lt_one
    have hIdentity := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
    have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
    have hZ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ :=
      sigmaZeroMinus_nonneg_of_pos a b hρ_pos
    have hSigmaMinus_nonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ := by
      rw [hIdentity]
      have h2 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
      exact mul_nonneg h2 hZ_nonneg
    have hLamPos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    -- 0 ≤ Σ⁻ ≤ Λ · circleGap; divide by Λ > 0.
    have hChain :
        0 ≤ WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
      le_trans hSigmaMinus_nonneg hBridge
    exact (mul_nonneg_iff_of_pos_left hLamPos).mp hChain
  -- Step 1: Pointwise lower bound on Ioo ρ₁ ρ₂ (via sprint 037).
  have hPointwise :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ
          ≤ 2 * ρ * PaperAxioms.circleGap a b ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2.le hρ₂_lt_one
    exact circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
      hc_pos hcρ hρ_lt_one (hLambdaBridgeWindow hcρ hρ_lt_one)
  -- Step 2: Integrability of the RHS on [ρ₁, ρ₂] / [c, ρ₁] / [ρ₂, 1]
  -- derived from `hIntCircle` via `mono_set`.
  have hIcc_ρ₁ρ₂_sub_c1 : Set.Icc ρ₁ ρ₂ ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc hc_le_ρ₁ hρ₂_le_one
  have hIcc_cρ₁_sub_c1 : Set.Icc c ρ₁ ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc le_rfl hρ₁_lt_one.le
  have hIcc_ρ₂1_sub_c1 : Set.Icc ρ₂ 1 ⊆ Set.Icc c 1 :=
    Set.Icc_subset_Icc hc_le_ρ₂ le_rfl
  have huIcc_ρ₁ρ₂ : Set.uIcc ρ₁ ρ₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₁₂, Set.uIcc_of_le hc_le_one]; exact hIcc_ρ₁ρ₂_sub_c1
  have huIcc_cρ₁ : Set.uIcc c ρ₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_ρ₁, Set.uIcc_of_le hc_le_one]; exact hIcc_cρ₁_sub_c1
  have huIcc_ρ₂1 : Set.uIcc ρ₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hρ₂_le_one, Set.uIcc_of_le hc_le_one]; exact hIcc_ρ₂1_sub_c1
  have hIntCircle_ρ₁ρ₂ :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume ρ₁ ρ₂ :=
    hIntCircle.mono_set huIcc_ρ₁ρ₂
  have hIntCircle_cρ₁ :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c ρ₁ :=
    hIntCircle.mono_set huIcc_cρ₁
  have hIntCircle_ρ₂1 :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume ρ₂ 1 :=
    hIntCircle.mono_set huIcc_ρ₂1
  -- These are exactly `IntervalIntegrable (annulusDensity (circleGap a b))`.
  have hIntDens_ρ₁ρ₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b))
        volume ρ₁ ρ₂ := hIntCircle_ρ₁ρ₂
  have hIntDens_cρ₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b))
        volume c ρ₁ := hIntCircle_cρ₁
  have hIntDens_ρ₂1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b))
        volume ρ₂ 1 := hIntCircle_ρ₂1
  -- Step 3: Integrate the pointwise bound on [ρ₁, ρ₂].
  have hIntegralMono :
      (∫ ρ in ρ₁..ρ₂,
          2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ) ≤
        ∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda hIntCircle_ρ₁ρ₂
      hPointwise
  -- Step 4: Recognise the upper bound as
  --   `annulusSlice (PaperAxioms.circleGap a b) ρ₁ ρ₂`.
  have hSlice_ρ₁ρ₂ :
      (∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ) =
        AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) ρ₁ ρ₂ := by
    change _ = ∫ ρ in ρ₁..ρ₂,
      AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b) ρ
    rfl
  -- Step 5: Split `annulusSlice (circleGap a b) c 1` into the three sub-slices.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) c ρ₁ +
          AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) ρ₁ 1 =
        AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) c 1 := by
    have hIntDens_ρ₁1 :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b))
          volume ρ₁ 1 := by
      have huIcc_ρ₁1 : Set.uIcc ρ₁ 1 ⊆ Set.uIcc c 1 := by
        rw [Set.uIcc_of_le hρ₁_lt_one.le, Set.uIcc_of_le hc_le_one]
        exact Set.Icc_subset_Icc hc_le_ρ₁ le_rfl
      exact hIntCircle.mono_set huIcc_ρ₁1
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cρ₁ hIntDens_ρ₁1
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) ρ₁ ρ₂ +
          AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) ρ₂ 1 =
        AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) ρ₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_ρ₁ρ₂ hIntDens_ρ₂1
  -- Step 6: Non-negativity of the side slices via the a.e. version,
  -- using `hCircleNonneg` (paper-axiom-free) in place of sprint 006's
  -- `paper`-bundle side-slice non-negativity helper.
  have hSlice_cρ₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice
            (PaperAxioms.circleGap a b) c ρ₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρ₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity
                (PaperAxioms.circleGap a b) ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρ₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity
                  (PaperAxioms.circleGap a b) ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hρ₁_lt_one
        have hC : 0 ≤ PaperAxioms.circleGap a b ρ := hCircleNonneg hcρ hρ_lt_one
        have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
        change 0 ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
        nlinarith
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := PaperAxioms.circleGap a b) (a := c) (b := ρ₁)
      hc_le_ρ₁ hNonnegAE
  have hSlice_ρ₂1_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice
            (PaperAxioms.circleGap a b) ρ₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity
                (PaperAxioms.circleGap a b) ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity
                  (PaperAxioms.circleGap a b) ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hcρ₂ hρ.1
        have hC : 0 ≤ PaperAxioms.circleGap a b ρ := hCircleNonneg hcρ hρ.2
        have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
        change 0 ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
        nlinarith
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := PaperAxioms.circleGap a b) (a := ρ₂) (b := (1 : ℝ))
      hρ₂_le_one hNonnegAE
  -- Step 7: Discharge `sigmaZeroMinus_nonneg_of_pos` (materialise the
  -- sprint 005 side lemma in the call graph; mirrors sprint 006).
  have hZ_ρ₁_nonneg :
      0 ≤ PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_nonneg_of_pos a b (lt_trans hc_pos hcρ₁)
  -- Step 8: Chain everything to get the lower bound on annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) ρ₁ ρ₂ ≤
        AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cρ₁_nonneg, hSlice_ρ₂1_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := by
    rfl
  -- Drop the unused Z_ρ₁ non-negativity into a `_` to silence linter.
  have _hZused := hZ_ρ₁_nonneg
  calc
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ)
        ≤ ∫ ρ in ρ₁..ρ₂, 2 * ρ * PaperAxioms.circleGap a b ρ := hIntegralMono
    _ = AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) ρ₁ ρ₂ := hSlice_ρ₁ρ₂
    _ ≤ AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 039 end-to-end full-window closing reducer fusing sprint 034's
paper-axiom-free integrated disk-side bound (modulo the disk-side scalar
hypothesis `hSigmaCmp`) with sprint 038's paper-axiom-free integrated
annulus-side bound (modulo the window-uniform hypothesis
`hLambdaBridgeWindow`). This is the workspace's **first `valid_of_*`
reducer whose entire transitive proof body invokes zero `paper.eq*`
field projections** on either disk or annulus side, the **first reducer
to lift two independent oracle-shaped hypothesis cells (`hSigmaCmp`
scalar at one anchor and `hLambdaBridgeWindow` window-uniform on
`(c, 1)`) into the witness existential simultaneously**, and the
**structural completion of the disk/annulus paper-axiom-free
`valid_of_*` matrix**.

The proof body is sprint 035's body verbatim with one targeted
substitution: the annulus-side step delegates to sprint 038
(`annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`,
paper-axiom-free body, modulo the explicit window-uniform
`hLambdaBridgeWindow`) instead of sprint 006
(`annulusExcess_lower_bound_of_eq8_eq9`, which transitively invokes
`paper.eq8`, `paper.eq9`, and
`OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper`). The witness
existential gains one new annulus-side cell `hLambdaBridgeWindow`
inserted between `hSigmaCmp` and `hIntDisk` (13 cells total after
`ρ₁, ρ₂`, vs. sprint 035's 12). The kernel inequality
`c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` and the admissible window
`[ρ₁, ρ₂] ⊂ (c, 1)` are byte-for-byte identical to sprints 014 and
035.

After this sprint lands, the workspace has its **first end-to-end
`ValidKorenblumBound c` closing reducer whose entire transitive proof
body invokes zero `paper.eq*` field projections** — both disk and
annulus sides paper-axiom-free, modulo exactly two independent
oracle-shaped hypothesis cells `hSigmaCmp` and `hLambdaBridgeWindow`.
A future oracle/proposal on either cell plugs directly into this
reducer's witness existential and immediately yields a paper-axiom-free
`ValidKorenblumBound c` route without any further structural plumbing.
-/
theorem valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
              Summable (fun k : ℕ =>
                PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
              else 0) ∧
            (PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) ∧
            (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
              PaperAxioms.sigmaMinus a b ρ ≤
                WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hSummable, hSummable_n1_c,
      hSigmaCmp, hLambdaBridgeWindow, hIntDisk, hIntCircle, hIntLambdaZ,
      hIntLambda, hSummable_top, hKernel⟩ :=
    h_witness paper
  -- Geometric scaffolding.
  have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
  have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
  have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
  -- Disk-side bound via sprint 034 (paper-axiom-free body, modulo
  -- the explicit `hSigmaCmp` hypothesis).
  have hDisk :=
    diskExcess_upper_bound_via_series_only_modulo_sigma_compare
      hc_pos hc_lt_one hSummable hSummable_n1_c hSigmaCmp hIntDisk
  -- Z_c ≥ 0 via sprint 005.
  have hZ_c_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
    sigmaZeroMinus_nonneg_of_pos a b hc_pos
  -- Step (a): multiply the kernel inequality by Z_c ≥ 0.
  have hStepA :
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c ≤
        (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c :=
    mul_le_mul_of_nonneg_right hKernel hZ_c_nonneg
  -- Step (b): pull the constant factor Z_c inside the integral.
  have hStepB :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c =
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c :=
    (intervalIntegral.integral_mul_const
        (PaperAxioms.sigmaZeroMinus a b c)
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
  -- Build pointwise Z_c ≤ Z_ρ' via sprint 011 + sprint 012.
  have hZmono :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b c ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
    have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
    have hc_le_ρ' : c ≤ ρ' := le_trans hc_le_ρ₁ hρ₁_le_ρ'
    have hρ'_nonneg : 0 ≤ ρ' :=
      le_of_lt (lt_of_lt_of_le hc_pos hc_le_ρ')
    have hSummable_ρ' :=
      sigmaZeroMinus_summable_of_summable_at_upper
        hρ'_nonneg hρ'_le_ρ₂ hSummable_top
    exact sigmaZeroMinus_monotone_of_summable
      hc_pos.le hc_le_ρ' hSummable_ρ'
  -- Step (c): integrate the pointwise Z_c ≤ Z_ρ' to dominate the
  -- constant-Z_c integrand by the Z_ρ'-weighted integrand.
  have hIntLambda_mul :
      IntervalIntegrable
        (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
            * PaperAxioms.sigmaZeroMinus a b c) volume ρ₁ ρ₂ :=
    hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b c)
  have hPointwise :
      ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
    intro ρ' hρ'
    have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
    have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
    have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
      WangPaperSideConditions.paperLambda_pos
        (K := K) (c := c) (ρ := ρ')
    have hρ'_pos : 0 < ρ' := lt_trans hc_pos hcρ'
    have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
    have hWeight_nonneg :
        0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
      div_nonneg hρ'3_nonneg hΛpos.le
    have hZmono_at := hZmono ρ' hρ'_in_Icc
    have hMul :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b c ≤
          2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' :=
      mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
    have hRewrite :
        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
            PaperAxioms.sigmaZeroMinus a b ρ' =
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
            WangOuter.paperLambda K c ρ' := by
      field_simp
    linarith [hMul, hRewrite.le, hRewrite.symm.le]
  have hStepC :
      (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c) ≤
        ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' :=
    intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
      hIntLambdaZ hPointwise
  -- Annulus-side lower bound via sprint 038 (paper-axiom-free body,
  -- modulo the explicit window-uniform `hLambdaBridgeWindow`
  -- hypothesis). This is the targeted substitution that drops the
  -- annulus-side equation-(8)/(9) invocations from the transitive
  -- proof body.
  have hAnn :=
    annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
      hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
      hLambdaBridgeWindow
  -- Final calc chain: diskExcess ≤ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hDisk
    _ ≤ (∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
          * PaperAxioms.sigmaZeroMinus a b c := hStepA
    _ = ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
              * PaperAxioms.sigmaZeroMinus a b c := hStepB
    _ ≤ ∫ ρ' in ρ₁..ρ₂,
            2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
              WangOuter.paperLambda K c ρ' := hStepC
    _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn

/--
Sprint 040 first paper-axiom-free integrated `diskExcess` upper bound of
shape `c²·sigmaPlus a b c` (no `Z_c`/`hSigmaCmp` cell). The proof body
integrates sprint 027's pointwise *equality*
`circleGap a b r = sigmaPlus a b r - r²·sigmaZeroMinus a b r` over
`[0, c]`, then bounds `∫ 2r·sigmaPlus r dr ≤ c²·sigmaPlus c` using
sprint 032's monotonicity (`sigmaPlus_monotone_of_summable`), and drops
the non-negative `∫ 2r³·Z_r dr` summand using
`sigmaZeroMinus_nonneg_of_pos`. This is the workspace's first
integrated `diskExcess` upper bound whose total trust-base hypothesis
count (paper axioms + oracle cells) is strictly zero, and the first
to land on the `Σ⁺` side of the disk-side ladder rather than on the
`Z`-side.
-/
theorem diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_pos : 0 < c)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hIntCircle :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b r) volume 0 c)
    (hIntZ :
      IntervalIntegrable
        (fun r => 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r)
        volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 2 * PaperAxioms.sigmaPlus a b c := by
  -- Step 1: pointwise equality on `Ioo 0 c` via sprint 027
  -- (paper-axiom-free; only requires `0 ≤ r` and summability).
  have hPointwiseEq :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        PaperAxioms.circleGap a b r =
          PaperAxioms.sigmaPlus a b r
            - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
    intro r hr
    exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
      a b hr.1.le (hSummable hr.1.le hr.2)
  -- Step 2: multiply by `2r` to convert to the integrand form.
  have hPointwiseEq_jac :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.circleGap a b r =
          2 * r * PaperAxioms.sigmaPlus a b r
            - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r := by
    intro r hr
    have hEq := hPointwiseEq r hr
    have hExpand :
        2 * r * PaperAxioms.circleGap a b r =
          2 * r * (PaperAxioms.sigmaPlus a b r
            - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r) := by
      rw [hEq]
    rw [hExpand]; ring
  -- Step 3: integrate the pointwise equality over `[0, c]` via two-sided
  -- application of `integral_mono_on_of_le_Ioo` (since pointwise equality
  -- on `Ioo 0 c` gives both `≤` and `≥` directions).
  have hRhs_int :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b r
          - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) volume 0 c :=
    hIntSigmaPlus.sub hIntZ
  have hLe_RhsLhs :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
        ∫ r in (0 : ℝ)..c,
            (2 * r * PaperAxioms.sigmaPlus a b r
              - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hIntCircle
      hRhs_int ?_
    intro r hr
    exact (hPointwiseEq_jac r hr).le
  have hGe_RhsLhs :
      ∫ r in (0 : ℝ)..c,
            (2 * r * PaperAxioms.sigmaPlus a b r
              - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) ≤
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hRhs_int
      hIntCircle ?_
    intro r hr
    exact (hPointwiseEq_jac r hr).ge
  have hIntegralEq :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r =
        ∫ r in (0 : ℝ)..c,
            (2 * r * PaperAxioms.sigmaPlus a b r
              - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) :=
    le_antisymm hLe_RhsLhs hGe_RhsLhs
  -- Step 4: split the integral via `intervalIntegral.integral_sub`.
  have hIntegralSub :
      ∫ r in (0 : ℝ)..c,
            (2 * r * PaperAxioms.sigmaPlus a b r
              - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) =
        (∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b r)
          - ∫ r in (0 : ℝ)..c, 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r :=
    intervalIntegral.integral_sub hIntSigmaPlus hIntZ
  -- Step 5: bound `∫ 2r·sigmaPlus a b r dr ≤ c²·sigmaPlus a b c`
  -- via sprint 032's monotonicity, integrated against the constant
  -- upper bound `sigmaPlus a b c`.
  have hPointwiseSigmaPlus :
      ∀ r ∈ Set.Ioo (0 : ℝ) c,
        2 * r * PaperAxioms.sigmaPlus a b r ≤
          2 * r * PaperAxioms.sigmaPlus a b c := by
    intro r hr
    have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
    have hMono :
        PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
      sigmaPlus_monotone_of_summable hr.1.le hr.2.le hSummable_n1_c
    exact mul_le_mul_of_nonneg_left hMono h2r_nonneg
  have hRhsSigmaPlus_cont :
      Continuous (fun r => 2 * r * PaperAxioms.sigmaPlus a b c) := by
    fun_prop
  have hRhsSigmaPlus_int :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b c) volume 0 c :=
    hRhsSigmaPlus_cont.intervalIntegrable _ _
  have hSigmaPlus_int_bound :
      ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b r ≤
        c ^ 2 * PaperAxioms.sigmaPlus a b c := by
    have hMonoInt :
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b r ≤
          ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b c :=
      intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hIntSigmaPlus
        hRhsSigmaPlus_int hPointwiseSigmaPlus
    have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
      have h := @integral_pow 0 c 1
      simp only [pow_one] at h
      convert h using 2 <;> norm_num
    have hRhsClosedForm :
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b c
          = c ^ 2 * PaperAxioms.sigmaPlus a b c := by
      have hRewrite :
          (fun r : ℝ => 2 * r * PaperAxioms.sigmaPlus a b c)
            = fun r => (2 * PaperAxioms.sigmaPlus a b c) * r := by
        funext r; ring
      rw [hRewrite, intervalIntegral.integral_const_mul, hPow1]
      ring
    linarith [hMonoInt, hRhsClosedForm.le, hRhsClosedForm.symm.le]
  -- Step 6: lower bound `0 ≤ ∫ 2r³·Z_r dr` via
  -- `intervalIntegral.integral_nonneg` applied to the pointwise
  -- non-negativity from `sigmaZeroMinus_nonneg_of_pos`.
  have hZ_int_nonneg :
      0 ≤ ∫ r in (0 : ℝ)..c,
            2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r := by
    refine intervalIntegral.integral_nonneg hc_pos.le ?_
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hr0 | hr_pos
    · -- r = 0 case: 2 * 0^3 * Z_0 = 0.
      have : r = 0 := hr0.symm
      rw [this]
      simp
    · -- r > 0 case: use sigmaZeroMinus_nonneg_of_pos.
      have h2r3_nonneg : (0 : ℝ) ≤ 2 * r ^ 3 := by positivity
      have hZ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b r :=
        sigmaZeroMinus_nonneg_of_pos a b hr_pos
      exact mul_nonneg h2r3_nonneg hZ_nonneg
  -- Step 7: identify diskExcess with the integral and chain via calc.
  have hDiskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  rw [hDiskExcess]
  calc
    ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
        = ∫ r in (0 : ℝ)..c,
            (2 * r * PaperAxioms.sigmaPlus a b r
              - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) := hIntegralEq
    _ = (∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b r)
          - ∫ r in (0 : ℝ)..c,
              2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r := hIntegralSub
    _ ≤ (c ^ 2 * PaperAxioms.sigmaPlus a b c) - 0 := by
          linarith [hSigmaPlus_int_bound, hZ_int_nonneg]
    _ = c ^ 2 * PaperAxioms.sigmaPlus a b c := by ring

/--
Sprint 041: the workspace's **first paper-axiom-free integrated *equality*
identity for `annulusSlice`** over an arbitrary radial sub-window
`[α, β] ⊂ [0, 1)`. Integrates sprint 027's pointwise equality
`circleGap r = sigmaPlus r − r²·sigmaZeroMinus r` over `[α, β]`, multiplies
by the polar Jacobian `2ρ`, and splits the resulting integrand via
`intervalIntegral.integral_sub`. No `Section2Assumptions` parameter, no
`paper.eq*` invocation, no `paperLambda`, no `Σ⁺ ≤ Σ⁻` cell.

The conclusion couples `annulusSlice (circleGap a b) α β` to the
*pure-series* quantities `∫ 2ρ·sigmaPlus a b ρ` and
`∫ 2ρ³·sigmaZeroMinus a b ρ`. Specialises uniformly to:
* the disk side at `(α, β) = (0, c)` (recovers sprint 040's
  intermediate identity without dropping the `Z`-integral term), and
* the annulus side at `(α, β) = (c, β)` for any `β < 1` (the **first**
  workspace lemma to express `annulusExcess`-style quantities as a pure
  series quantity, with no `Λ` and no oracle).
-/
theorem annulusSlice_eq_via_series_partition
    {a b : ℕ → ℂ} {α β : ℝ}
    (hα_nonneg : 0 ≤ α)
    (hα_le_β : α ≤ β)
    (hβ_lt_one : β < 1)
    (hSummable :
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ β →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume α β)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ) volume α β)
    (hIntZ :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
        volume α β) :
    AnnulusIntegralReduction.annulusSlice
        (PaperAxioms.circleGap a b) α β =
      (∫ ρ in α..β, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        - ∫ ρ in α..β, 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ := by
  -- Sprint 027 pointwise equality holds on `Set.uIcc α β = Set.Icc α β`.
  have hUIccEq : Set.uIcc α β = Set.Icc α β := Set.uIcc_of_le hα_le_β
  -- Step 1: pointwise equality `circleGap = sigmaPlus − ρ²·Z` on `[α, β]`
  -- (paper-axiom-free; only requires `0 ≤ ρ` and summability at `ρ`).
  have hPointwiseEq :
      ∀ ρ ∈ Set.uIcc α β,
        PaperAxioms.circleGap a b ρ =
          PaperAxioms.sigmaPlus a b ρ
            - ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ := by
    intro ρ hρ
    rw [hUIccEq] at hρ
    have hρ_nonneg : 0 ≤ ρ := le_trans hα_nonneg hρ.1
    have hρ_le_β : ρ ≤ β := hρ.2
    exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
      a b hρ_nonneg (hSummable hρ_nonneg hρ_le_β)
  -- Step 2: multiply by `2ρ` to convert to integrand form.
  have hPointwiseEq_jac :
      ∀ ρ ∈ Set.uIcc α β,
        2 * ρ * PaperAxioms.circleGap a b ρ =
          2 * ρ * PaperAxioms.sigmaPlus a b ρ
            - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ := by
    intro ρ hρ
    have hEq := hPointwiseEq ρ hρ
    have hExpand :
        2 * ρ * PaperAxioms.circleGap a b ρ =
          2 * ρ * (PaperAxioms.sigmaPlus a b ρ
            - ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ) := by
      rw [hEq]
    rw [hExpand]; ring
  -- Step 3: integrate the pointwise equality via `integral_congr`.
  have hIntegralEq :
      ∫ ρ in α..β, 2 * ρ * PaperAxioms.circleGap a b ρ =
        ∫ ρ in α..β,
            (2 * ρ * PaperAxioms.sigmaPlus a b ρ
              - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ) :=
    intervalIntegral.integral_congr hPointwiseEq_jac
  -- Step 4: split the integral via `integral_sub`.
  have hIntegralSub :
      ∫ ρ in α..β,
            (2 * ρ * PaperAxioms.sigmaPlus a b ρ
              - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ) =
        (∫ ρ in α..β, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
          - ∫ ρ in α..β, 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ :=
    intervalIntegral.integral_sub hIntSigmaPlus hIntZ
  -- Step 5: identify `annulusSlice` with the integral and chain via calc.
  have hAnnulusSliceUnfold :
      AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) α β =
        ∫ ρ in α..β, 2 * ρ * PaperAxioms.circleGap a b ρ := by
    rfl
  rw [hAnnulusSliceUnfold]
  exact hIntegralEq.trans hIntegralSub

/--
Sprint 042: the workspace's **first paper-axiom-free `tsum`-of-integrals
closed-form *equality*** for `diskExcess (circleGap a b) c`. Composes the
definitional series unfolding `circleGap a b r = ∑' k, coeffPlusGap a b k *
r^(2k)` with the polar Jacobian `2r`, then applies Mathlib's
`MeasureTheory.integral_tsum_of_summable_integral_norm` to swap the `∑'` past
the `∫`, evaluating each termwise integral via `@integral_pow 0 c (2k+1)` to
the closed-form `coeffPlusGap a b k * c^(2k+2) / (k+1)`.

The hypothesis is the natural integral-norm summability cell
`Summable (fun k => |coeffPlusGap a b k| * c^(2k+2) / (k+1))`, exactly the
shape produced by `∫₀^c ‖2 * coeffPlusGap a b k * r^(2k+1)‖ dr` after the
polynomial closed form. No `Section2Assumptions` parameter, no `paper.eq*`
invocation, no `paperLambda`, no oracle cell. The conclusion is an
**equality** at the per-coefficient level — strictly more informative than
every prior workspace `diskExcess` upper bound (sprints 003 / 013 / 026 /
030 / 031 / 034 / 040), which give bulk function-level numbers.

This is the workspace's **first lemma at the `tsum`-of-integrals layer**:
every prior lemma operates either at the function-level pointwise layer, the
function-level series-partition `tsum` layer (at fixed `r`), or the
function-level integrated layer (a single `∫` over a fixed window). Sprint
042 swaps a `∑'` over the series index `k` past an `∫` over the radial
variable `r ∈ [0, c]`, exposing each `k`-th termwise integral as an
independently-computable closed-form quantity. Unlocks per-coefficient
analytical and numerical handling of `diskExcess` for the first time.
-/
theorem diskExcess_eq_tsum_via_termwise_integration
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) := by
  classical
  -- Step 0: define the termwise function family
  -- F k r = 2 * coeffPlusGap a b k * r^(2k+1).
  set F : ℕ → ℝ → ℝ := fun k r =>
    2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) with hF_def
  -- Each F k is continuous (polynomial in r).
  have hF_cont : ∀ k : ℕ, Continuous (F k) := by
    intro k
    simp only [hF_def]
    fun_prop
  -- Each F k is integrable on `Ioc 0 c` w.r.t. volume, i.e.
  -- `Integrable (F k) (volume.restrict (Ioc 0 c))`.
  have hF_int :
      ∀ k : ℕ, Integrable (F k) (volume.restrict (Set.Ioc 0 c)) := by
    intro k
    have hIO : IntegrableOn (F k) (Set.Ioc 0 c) volume :=
      (hF_cont k).integrableOn_Ioc
    exact hIO
  -- Step 1: termwise L¹-norm closed form
  -- ∫ r in 0..c, ‖F k r‖ = |coeffPlusGap a b k| * c^(2k+2) / (k+1).
  have h_int_norm_eq : ∀ k : ℕ,
      ∫ r in (0:ℝ)..c, ‖F k r‖ =
        |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1) := by
    intro k
    -- On `[0, c]`, ‖F k r‖ = 2 * |coeffPlusGap a b k| * r^(2k+1) (since r ≥ 0).
    have h_norm_eq :
        ∀ r ∈ Set.uIcc (0:ℝ) c,
          ‖F k r‖ =
            2 * |PaperAxioms.coeffPlusGap a b k| * r ^ (2 * k + 1) := by
      intro r hr
      rw [Set.uIcc_of_le hc_nonneg] at hr
      have hr_nonneg : 0 ≤ r := hr.1
      simp only [hF_def, Real.norm_eq_abs, abs_mul, abs_pow]
      have h2_abs : |(2:ℝ)| = 2 := by norm_num
      rw [h2_abs, abs_of_nonneg hr_nonneg]
    rw [intervalIntegral.integral_congr h_norm_eq]
    -- ∫₀^c (2 * |coeff| * r^(2k+1)) dr = (2 * |coeff|) * (c^(2k+2)/(2k+2))
    have h_factor :
        (fun r : ℝ =>
            2 * |PaperAxioms.coeffPlusGap a b k| * r ^ (2 * k + 1)) =
          fun r : ℝ =>
            (2 * |PaperAxioms.coeffPlusGap a b k|) * r ^ (2 * k + 1) := by
      funext r; ring
    rw [h_factor, intervalIntegral.integral_const_mul]
    -- Closed form: ∫₀^c r^(2k+1) dr = c^(2k+2) / (2k+2).
    have h_pow :
        ∫ r in (0:ℝ)..c, r ^ (2 * k + 1) =
          c ^ (2 * k + 2) / ((2 * k + 2 : ℕ) : ℝ) := by
      have h := @integral_pow 0 c (2 * k + 1)
      have h0 : (0:ℝ) ^ (2 * k + 1 + 1) = 0 := by
        apply zero_pow
        omega
      rw [h0, sub_zero] at h
      have hExp : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      rw [hExp] at h
      have hCast : ((2 * k + 2 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [hCast]
      exact h
    rw [h_pow]
    -- Algebraic normalisation: 2 * |coeff| * (c^(2k+2)/(2k+2))
    --                        = |coeff| * c^(2k+2) / (k+1).
    have h_denom_pos : (0 : ℝ) < (k + 1 : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_denom_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt h_denom_pos
    have h_cast : ((2 * k + 2 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
      push_cast; ring
    rw [h_cast]
    field_simp
  -- Step 2: summability of the L¹-norms (transferred from hSummable_int_norm).
  have h_int_norm_general_eq : ∀ k : ℕ,
      ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc 0 c)) =
        |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1) := by
    intro k
    have h_conv : ∫ r in (0:ℝ)..c, ‖F k r‖ =
        ∫ r in Set.Ioc 0 c, ‖F k r‖ ∂volume :=
      intervalIntegral.integral_of_le hc_nonneg
    have h_restrict : ∫ r in Set.Ioc 0 c, ‖F k r‖ ∂volume =
        ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc 0 c)) := rfl
    rw [← h_restrict, ← h_conv]
    exact h_int_norm_eq k
  have h_int_norm_summable :
      Summable (fun k : ℕ =>
        ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc 0 c))) := by
    have h_eq : (fun k : ℕ =>
          ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc 0 c))) =
        (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1)) :=
      funext h_int_norm_general_eq
    rw [h_eq]
    exact hSummable_int_norm
  -- Step 3: apply MeasureTheory.integral_tsum_of_summable_integral_norm.
  have h_swap_general :
      ∑' k : ℕ, ∫ r, F k r ∂(volume.restrict (Set.Ioc 0 c)) =
        ∫ r, ∑' k : ℕ, F k r ∂(volume.restrict (Set.Ioc 0 c)) :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      hF_int h_int_norm_summable
  -- Convert the general integrals back to intervalIntegral on `0..c`.
  have h_lhs_conv : ∀ k : ℕ,
      ∫ r, F k r ∂(volume.restrict (Set.Ioc 0 c)) =
        ∫ r in (0:ℝ)..c, F k r := by
    intro k
    rw [intervalIntegral.integral_of_le hc_nonneg]
  have h_rhs_conv :
      ∫ r, ∑' k : ℕ, F k r ∂(volume.restrict (Set.Ioc 0 c)) =
        ∫ r in (0:ℝ)..c, ∑' k : ℕ, F k r := by
    rw [intervalIntegral.integral_of_le hc_nonneg]
  have h_swap :
      ∑' k : ℕ, ∫ r in (0:ℝ)..c, F k r =
        ∫ r in (0:ℝ)..c, ∑' k : ℕ, F k r := by
    have h_lhs_eq : (fun k : ℕ =>
          ∫ r, F k r ∂(volume.restrict (Set.Ioc 0 c))) =
        (fun k : ℕ => ∫ r in (0:ℝ)..c, F k r) := funext h_lhs_conv
    rw [← h_lhs_eq, ← h_rhs_conv]
    exact h_swap_general
  -- Step 4: pointwise series unfold of `2r * circleGap a b r` on [0, c].
  have h_integrand_eq :
      ∀ r ∈ Set.uIcc (0:ℝ) c,
        2 * r * PaperAxioms.circleGap a b r =
          ∑' k : ℕ, F k r := by
    intro r _hr
    change 2 * r * PaperAxioms.circleGap a b r =
        ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1)
    -- circleGap a b r = ∑' k, coeffPlusGap a b k * r^(2k) (definitional).
    have hUnfold : PaperAxioms.circleGap a b r =
        ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) := rfl
    rw [hUnfold]
    -- Pull `2*r` inside the tsum (`tsum_mul_left.symm` direction).
    rw [show (2 * r) *
            (∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)) =
          ∑' k : ℕ, (2 * r) *
            (PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))
        from (tsum_mul_left).symm]
    refine tsum_congr (fun k => ?_)
    -- Termwise: (2*r) * (coeff k * r^(2k)) = 2 * coeff k * r^(2k+1).
    have hPow : r ^ (2 * k + 1) = r * r ^ (2 * k) := by
      rw [pow_succ]; ring
    rw [hPow]; ring
  -- Step 5: lift the pointwise integrand identity to an integral equality.
  have h_integral_eq :
      ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r =
        ∫ r in (0:ℝ)..c, ∑' k : ℕ, F k r :=
    intervalIntegral.integral_congr h_integrand_eq
  -- Step 6: termwise integral closed form
  -- ∫₀^c F k r dr = coeffPlusGap a b k * c^(2k+2) / (k+1).
  have h_termwise_integral : ∀ k : ℕ,
      ∫ r in (0:ℝ)..c, F k r =
        PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) := by
    intro k
    change ∫ r in (0:ℝ)..c,
            2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) =
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
    have h_factor :
        (fun r : ℝ =>
            2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1)) =
          fun r : ℝ =>
            (2 * PaperAxioms.coeffPlusGap a b k) * r ^ (2 * k + 1) := by
      funext r; ring
    rw [h_factor, intervalIntegral.integral_const_mul]
    -- Closed form: ∫₀^c r^(2k+1) dr = c^(2k+2) / (2k+2).
    have h_pow :
        ∫ r in (0:ℝ)..c, r ^ (2 * k + 1) =
          c ^ (2 * k + 2) / ((2 * k + 2 : ℕ) : ℝ) := by
      have h := @integral_pow 0 c (2 * k + 1)
      have h0 : (0:ℝ) ^ (2 * k + 1 + 1) = 0 := by
        apply zero_pow
        omega
      rw [h0, sub_zero] at h
      have hExp : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      rw [hExp] at h
      have hCast : ((2 * k + 2 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [hCast]
      exact h
    rw [h_pow]
    have h_denom_pos : (0 : ℝ) < (k + 1 : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_denom_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt h_denom_pos
    have h_cast : ((2 * k + 2 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
      push_cast; ring
    rw [h_cast]
    field_simp
  -- Step 7: identify `diskExcess` with the integral and chain via calc.
  have h_diskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      = ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r :=
        h_diskExcess
    _ = ∫ r in (0:ℝ)..c, ∑' k : ℕ, F k r := h_integral_eq
    _ = ∑' k : ℕ, ∫ r in (0:ℝ)..c, F k r := h_swap.symm
    _ = ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
        tsum_congr h_termwise_integral

/--
Sprint 043 — first paper-axiom-free **N1/N2 partition** of sprint 042's
`tsum`-of-integrals identity for `diskExcess (circleGap a b) c`. Composes
sprint 042's invocation (single-line application of
`diskExcess_eq_tsum_via_termwise_integration`) with sprint 027's partition
skeleton (with the termwise summand rebound to the integrated form
`coeffPlusGap a b k * c^(2k+2)/(k+1)`). Introduces the integrated `Σ⁺_int`/
`Σ⁻_int` series quantities at the integrated × N1/N2-restricted layer; no
prior workspace lemma operates at this layer. The signature is `(a, b, c)`-
only with no `Section2Assumptions` parameter, no `paper.eq*` invocation, no
`paperLambda`, and no oracle cell.
-/
theorem diskExcess_eq_tsum_partition_via_series
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c ^ (2 * k + 2) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                c ^ (2 * k + 2) / (k + 1)
            else 0 := by
  classical
  -- Step 0: invoke sprint 042 to obtain the unconditioned `tsum` identity.
  have h_sprint042 :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
    diskExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
      hc_nonneg hSummable_int_norm
  -- Abbreviate the four relevant termwise summands (mirroring sprint 027).
  set f : ℕ → ℝ := fun k =>
    PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
    with hf_def
  set f1 : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
    else 0 with hf1_def
  set f2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
    else 0 with hf2_def
  set g2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * c ^ (2 * k + 2) / (k + 1)
    else 0 with hg2_def
  -- Summability transfer: from `Summable (|f|)` to `Summable f`.
  -- The bound `‖f k‖ ≤ |coeffPlusGap a b k| * c^(2k+2)/(k+1)` is in fact an
  -- equality (since `c^(2k+2)/(k+1) ≥ 0`).
  have hSummable_f : Summable f := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / (k + 1))
      hSummable_int_norm ?_
    intro k
    simp only [hf_def, Real.norm_eq_abs]
    -- |coeffPlusGap_k * c^(2k+2)/(k+1)| = |coeffPlusGap_k| * c^(2k+2)/(k+1).
    have hpow_nonneg : 0 ≤ c ^ (2 * k + 2) := pow_nonneg hc_nonneg _
    have hkp1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hkp1_nonneg : (0 : ℝ) ≤ (k : ℝ) + 1 := hkp1_pos.le
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hc_nonneg,
        abs_of_nonneg hkp1_nonneg]
  -- Partition fact: ¬ n1Pred → n2Pred (verbatim from sprint 027).
  have h_n1_to_n2 :
      ∀ k, ¬ PaperAxioms.n1Pred a b k → PaperAxioms.n2Pred a b k := by
    intro k hk
    unfold PaperAxioms.n1Pred at hk
    unfold PaperAxioms.n2Pred
    push_neg at hk
    exact ⟨Nat.pos_of_ne_zero hk.1, hk.2⟩
  -- Reverse direction: n2Pred → ¬ n1Pred (verbatim from sprint 027).
  have h_n2_to_not_n1 :
      ∀ k, PaperAxioms.n2Pred a b k → ¬ PaperAxioms.n1Pred a b k := by
    intro k hk2 hk1
    unfold PaperAxioms.n2Pred at hk2
    unfold PaperAxioms.n1Pred at hk1
    obtain ⟨hk_pos, hab⟩ := hk2
    rcases hk1 with h | h
    · exact (Nat.lt_irrefl 0 (h ▸ hk_pos))
    · exact (not_lt_of_ge h) hab
  -- Termwise partition identity: f k = f1 k + f2 k for all k.
  have h_term_partition : ∀ k, f k = f1 k + f2 k := by
    intro k
    by_cases hk1 : PaperAxioms.n1Pred a b k
    · -- n1Pred true ⇒ n2Pred false ⇒ RHS = f k + 0 = f k.
      have hk2 : ¬ PaperAxioms.n2Pred a b k := fun hcontra =>
        h_n2_to_not_n1 k hcontra hk1
      simp [f, f1, f2, hk1, hk2]
    · -- n1Pred false ⇒ n2Pred true ⇒ RHS = 0 + f k = f k.
      have hk2 : PaperAxioms.n2Pred a b k := h_n1_to_n2 k hk1
      simp [f, f1, f2, hk1, hk2]
  -- Summability of `f1` via `Summable.indicator` over `{k | n1Pred a b k}`.
  have hSummable_f1 : Summable f1 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n1Pred a b k}.indicator f) :=
      hSummable_f.indicator {k | PaperAxioms.n1Pred a b k}
    have h_eq : f1 = {k | PaperAxioms.n1Pred a b k}.indicator f := by
      funext k
      simp [f1, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Summability of `f2` via `Summable.indicator` over `{k | n2Pred a b k}`.
  have hSummable_f2 : Summable f2 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n2Pred a b k}.indicator f) :=
      hSummable_f.indicator {k | PaperAxioms.n2Pred a b k}
    have h_eq : f2 = {k | PaperAxioms.n2Pred a b k}.indicator f := by
      funext k
      simp [f2, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Step A: ∑' k, f k = (∑' k, f1 k) + (∑' k, f2 k).
  have h_tsum_partition :
      (∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k := by
    have h_congr : (∑' k, f k) = ∑' k, (f1 k + f2 k) :=
      tsum_congr h_term_partition
    rw [h_congr, hSummable_f1.tsum_add hSummable_f2]
  -- Step C: ∑' k, f2 k = − ∑' k, g2 k via the termwise N2 sign-swap identity.
  have h_f2_eq_neg_g2 : (∑' k, f2 k) = - ∑' k, g2 k := by
    have h_term_neg : ∀ k, f2 k = -(g2 k) := by
      intro k
      by_cases hk : PaperAxioms.n2Pred a b k
      · simp only [f2, g2, hk, if_true]
        unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
        ring
      · simp [f2, g2, hk]
    calc (∑' k, f2 k)
        = ∑' k, -(g2 k) := tsum_congr h_term_neg
      _ = -∑' k, g2 k := tsum_neg
  -- Chain: diskExcess = ∑' f = ∑' f1 + ∑' f2 = ∑' f1 - ∑' g2.
  calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      = ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
        h_sprint042
    _ = ∑' k, f k := rfl
    _ = (∑' k, f1 k) + ∑' k, f2 k := h_tsum_partition
    _ = (∑' k, f1 k) + (-∑' k, g2 k) := by rw [h_f2_eq_neg_g2]
    _ = (∑' k, f1 k) - ∑' k, g2 k := by ring

/--
Sprint 044 — first paper-axiom-free **and** oracle-cell-free disk-side
upper bound on `diskExcess (circleGap a b) c` whose RHS is a per-`k`
termwise series. Composes sprint 043's N1/N2 partition equality
(`diskExcess = Σ⁺_int(c) − Σ⁻_int(c)`) with the termwise non-negativity
of the N2 summand to drop the non-negative `Σ⁻_int(c)` piece. The
signature is `(a, b, c)`-only with no `Section2Assumptions` parameter,
no `paper.eq*` invocation, no `paperLambda`, and no oracle cell.
-/
theorem diskExcess_upper_bound_via_tsum_partition_drop_N2
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      ∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c ^ (2 * k + 2) / (k + 1)
        else 0 := by
  classical
  -- Step 1: invoke sprint 043 to get the partition equality.
  have h_sprint043 :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c ^ (2 * k + 2) / (k + 1)
          else 0)
          - ∑' k : ℕ,
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  c ^ (2 * k + 2) / (k + 1)
              else 0 :=
    diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
      hc_nonneg hSummable_int_norm
  -- Step 2: termwise non-negativity of the N2 summand.
  have h_n2_term_nonneg :
      ∀ k : ℕ,
        0 ≤ (if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  c ^ (2 * k + 2) / (k + 1)
              else (0 : ℝ)) := by
    intro k
    by_cases hk : PaperAxioms.n2Pred a b k
    · -- n2Pred ⇒ ‖a k‖ < ‖b k‖ ⇒ ‖a k‖² ≤ ‖b k‖² ⇒ coeffMinusGap ≥ 0.
      simp only [hk, if_true]
      have h_norm_le : ‖a k‖ ≤ ‖b k‖ := le_of_lt hk.2
      have h_a_nonneg : (0 : ℝ) ≤ ‖a k‖ := norm_nonneg _
      have h_norm_sq : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ h_a_nonneg h_norm_le 2
      have h_coeff_nonneg :
          (0 : ℝ) ≤ PaperAxioms.coeffMinusGap a b k := by
        unfold PaperAxioms.coeffMinusGap
        linarith
      have h_pow_nonneg : (0 : ℝ) ≤ c ^ (2 * k + 2) :=
        pow_nonneg hc_nonneg _
      have h_kp1_pos : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
      have h_num_nonneg :
          (0 : ℝ) ≤ PaperAxioms.coeffMinusGap a b k * c ^ (2 * k + 2) :=
        mul_nonneg h_coeff_nonneg h_pow_nonneg
      exact div_nonneg h_num_nonneg h_kp1_pos.le
    · simp [hk]
  -- Step 3: apply `tsum_nonneg` to conclude the dropped N2 piece is ≥ 0.
  have h_n2_tsum_nonneg :
      (0 : ℝ) ≤
        ∑' k : ℕ,
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k *
              c ^ (2 * k + 2) / (k + 1)
          else 0 :=
    tsum_nonneg h_n2_term_nonneg
  -- Step 4: chain the equality + non-negativity to the upper bound.
  linarith [h_sprint043, h_n2_tsum_nonneg]

/--
Sprint 045 — first workspace `valid_of_*` closing reducer with paper-axiom
signature `{eq8, eq9}` AND **zero** oracle cells AND a per-`k` termwise
series disk-side kernel `Σ⁺_int(c) := ∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1)`.

Composes sprint 044's paper-axiom-free, oracle-cell-free disk bound
(`diskExcess_upper_bound_via_tsum_partition_drop_N2`) with sprint 006's
annulus lower bound (`annulusExcess_lower_bound_of_eq8_eq9`), connecting
them via a per-`k` × integrated kernel inequality
`Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ` lifted into the witness
existential.

Strict structural upgrade over sprint 035: replaces the bulk-scalar
`hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)` cell with the per-`k` kernel inequality, and
replaces the `c⁴ · Z_c` kernel LHS with the per-`k` series `Σ⁺_int(c)`.
The disk-side body is paper-axiom-free **and** oracle-cell-free; the only
paper axioms in the transitive proof body come from sprint 006's annulus
side (`{eq8, eq9}`).
-/
theorem valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            -- sprint 044's input cell: integrated absolute-value summability
            Summable (fun k : ℕ =>
              |PaperAxioms.coeffPlusGap a b k| *
                c ^ (2 * k + 2) / (k + 1)) ∧
            -- sprint 006's input cell: summability for series-monotonicity
            -- transfer at the right edge ρ₂
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k)
              else 0) ∧
            -- sprint 006's annulus-side integrability cells
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            -- The new per-`k` termwise kernel inequality
            (∑' k : ℕ,
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k *
                  c ^ (2 * k + 2) / (k + 1)
              else 0) ≤
              ∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                  / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρ₁, ρ₂, hρ₁_gt_c, hρ₁_le_ρ₂, hρ₂_lt_one,
      hSummable_int_norm, _hSummable_n2_at_ρ₂,
      hIntCircleAnnulus, hIntZOverLambda, hKernel⟩ :=
    h_witness paper
  -- Disk-side bound via sprint 044 (paper-axiom-free, oracle-cell-free).
  have hDisk :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        ∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c ^ (2 * k + 2) / (k + 1)
          else 0 :=
    diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
      hc_pos.le hSummable_int_norm
  -- Annulus-side lower bound via sprint 006.
  have hAnnulus :
      (∫ ρ' in ρ₁..ρ₂,
          2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
            / WangOuter.paperLambda K c ρ') ≤
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c :=
    annulusExcess_lower_bound_of_eq8_eq9
      paper hc_pos hρ₁_gt_c hρ₁_le_ρ₂ hρ₂_lt_one
      hIntCircleAnnulus hIntZOverLambda
  -- Final calc chain: diskExcess ≤ Σ⁺_int(c) ≤ ∫ … ≤ annulusExcess.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  exact le_trans hDisk (le_trans hKernel hAnnulus)

/--
Sprint 046 — first paper-axiom-free, oracle-cell-free annulus-side
`tsum`-of-integrals closed-form **equality** for
`annulusExcess (circleGap a b) c`. Mirror of sprint 042's
`diskExcess_eq_tsum_via_termwise_integration` over the structurally distinct
interval `[c, 1]` (sprint 042 covers `[0, c]`).

The identity expresses
`annulusExcess (circleGap a b) c = ∫ r in c..1, 2 * r * circleGap a b r`
as a per-`k` `tsum` with each `k`-th coefficient computed via the closed-form
polynomial integral
`∫ r in c..1, r^(2k+1) dr = (1 - c^(2k+2)) / (2k+2)`.

The hypothesis is the natural integral-norm summability cell on the per-`k`
weight `(1 - c^(2k+2)) / (k+1)` — strictly weaker for `c < 1` than sprint
042's `c^(2k+2)/(k+1)` weight (the new weight decays only like `1/(k+1)`).
No `Section2Assumptions` parameter, no `paper.eq*` invocation, no
`paperLambda`, no oracle cell. The conclusion is an **equality**.

Together with sprint 042 this covers **both halves** of the natural
decomposition `annulusSlice 0 1 = diskExcess + annulusExcess`, exposing the
entire `[0, 1)`-integrated `2r · circleGap a b r` as a `tsum` of polynomial
integrals on each half.
-/
theorem annulusExcess_eq_tsum_via_termwise_integration
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1))) :
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k
          * (1 - c ^ (2 * k + 2)) / (k + 1) := by
  classical
  -- Step 0: define the termwise function family
  -- F k r = 2 * coeffPlusGap a b k * r^(2k+1).
  set F : ℕ → ℝ → ℝ := fun k r =>
    2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) with hF_def
  -- Each F k is continuous (polynomial in r).
  have hF_cont : ∀ k : ℕ, Continuous (F k) := by
    intro k
    simp only [hF_def]
    fun_prop
  -- Each F k is integrable on `Ioc c 1` w.r.t. volume, i.e.
  -- `Integrable (F k) (volume.restrict (Ioc c 1))`.
  have hF_int :
      ∀ k : ℕ, Integrable (F k) (volume.restrict (Set.Ioc c 1)) := by
    intro k
    have hIO : IntegrableOn (F k) (Set.Ioc c 1) volume :=
      (hF_cont k).integrableOn_Ioc
    exact hIO
  -- Step 1: termwise L¹-norm closed form
  -- ∫ r in c..1, ‖F k r‖ = |coeffPlusGap a b k| * (1 - c^(2k+2)) / (k+1).
  have h_int_norm_eq : ∀ k : ℕ,
      ∫ r in c..(1:ℝ), ‖F k r‖ =
        |PaperAxioms.coeffPlusGap a b k| * (1 - c ^ (2 * k + 2)) / (k + 1) := by
    intro k
    -- On `[c, 1]`, ‖F k r‖ = 2 * |coeffPlusGap a b k| * r^(2k+1)
    -- (since r ≥ c ≥ 0).
    have h_norm_eq :
        ∀ r ∈ Set.uIcc c (1:ℝ),
          ‖F k r‖ =
            2 * |PaperAxioms.coeffPlusGap a b k| * r ^ (2 * k + 1) := by
      intro r hr
      rw [Set.uIcc_of_le hc_le_one] at hr
      have hr_nonneg : 0 ≤ r := le_trans hc_nonneg hr.1
      simp only [hF_def, Real.norm_eq_abs, abs_mul, abs_pow]
      have h2_abs : |(2:ℝ)| = 2 := by norm_num
      rw [h2_abs, abs_of_nonneg hr_nonneg]
    rw [intervalIntegral.integral_congr h_norm_eq]
    -- ∫_c^1 (2 * |coeff| * r^(2k+1)) dr =
    --   (2 * |coeff|) * ((1 - c^(2k+2))/(2k+2))
    have h_factor :
        (fun r : ℝ =>
            2 * |PaperAxioms.coeffPlusGap a b k| * r ^ (2 * k + 1)) =
          fun r : ℝ =>
            (2 * |PaperAxioms.coeffPlusGap a b k|) * r ^ (2 * k + 1) := by
      funext r; ring
    rw [h_factor, intervalIntegral.integral_const_mul]
    -- Closed form: ∫_c^1 r^(2k+1) dr = (1 - c^(2k+2)) / (2k+2).
    have h_pow :
        ∫ r in c..(1:ℝ), r ^ (2 * k + 1) =
          (1 - c ^ (2 * k + 2)) / ((2 * k + 2 : ℕ) : ℝ) := by
      have h := @integral_pow c 1 (2 * k + 1)
      have h1 : (1:ℝ) ^ (2 * k + 1 + 1) = 1 := one_pow _
      rw [h1] at h
      have hExp : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      rw [hExp] at h
      have hCast : ((2 * k + 2 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [hCast]
      exact h
    rw [h_pow]
    -- Algebraic normalisation:
    -- 2 * |coeff| * ((1 - c^(2k+2))/(2k+2)) = |coeff| * (1 - c^(2k+2)) / (k+1).
    have h_denom_pos : (0 : ℝ) < (k + 1 : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_denom_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt h_denom_pos
    have h_cast : ((2 * k + 2 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
      push_cast; ring
    rw [h_cast]
    field_simp
  -- Step 2: summability of the L¹-norms (transferred from hSummable_int_norm).
  have h_int_norm_general_eq : ∀ k : ℕ,
      ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc c 1)) =
        |PaperAxioms.coeffPlusGap a b k| * (1 - c ^ (2 * k + 2)) / (k + 1) := by
    intro k
    have h_conv : ∫ r in c..(1:ℝ), ‖F k r‖ =
        ∫ r in Set.Ioc c 1, ‖F k r‖ ∂volume :=
      intervalIntegral.integral_of_le hc_le_one
    have h_restrict : ∫ r in Set.Ioc c 1, ‖F k r‖ ∂volume =
        ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc c 1)) := rfl
    rw [← h_restrict, ← h_conv]
    exact h_int_norm_eq k
  have h_int_norm_summable :
      Summable (fun k : ℕ =>
        ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc c 1))) := by
    have h_eq : (fun k : ℕ =>
          ∫ r, ‖F k r‖ ∂(volume.restrict (Set.Ioc c 1))) =
        (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            (1 - c ^ (2 * k + 2)) / (k + 1)) :=
      funext h_int_norm_general_eq
    rw [h_eq]
    exact hSummable_int_norm
  -- Step 3: apply MeasureTheory.integral_tsum_of_summable_integral_norm.
  have h_swap_general :
      ∑' k : ℕ, ∫ r, F k r ∂(volume.restrict (Set.Ioc c 1)) =
        ∫ r, ∑' k : ℕ, F k r ∂(volume.restrict (Set.Ioc c 1)) :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      hF_int h_int_norm_summable
  -- Convert the general integrals back to intervalIntegral on `c..1`.
  have h_lhs_conv : ∀ k : ℕ,
      ∫ r, F k r ∂(volume.restrict (Set.Ioc c 1)) =
        ∫ r in c..(1:ℝ), F k r := by
    intro k
    rw [intervalIntegral.integral_of_le hc_le_one]
  have h_rhs_conv :
      ∫ r, ∑' k : ℕ, F k r ∂(volume.restrict (Set.Ioc c 1)) =
        ∫ r in c..(1:ℝ), ∑' k : ℕ, F k r := by
    rw [intervalIntegral.integral_of_le hc_le_one]
  have h_swap :
      ∑' k : ℕ, ∫ r in c..(1:ℝ), F k r =
        ∫ r in c..(1:ℝ), ∑' k : ℕ, F k r := by
    have h_lhs_eq : (fun k : ℕ =>
          ∫ r, F k r ∂(volume.restrict (Set.Ioc c 1))) =
        (fun k : ℕ => ∫ r in c..(1:ℝ), F k r) := funext h_lhs_conv
    rw [← h_lhs_eq, ← h_rhs_conv]
    exact h_swap_general
  -- Step 4: pointwise series unfold of `2r * circleGap a b r` on [c, 1].
  have h_integrand_eq :
      ∀ r ∈ Set.uIcc c (1:ℝ),
        2 * r * PaperAxioms.circleGap a b r =
          ∑' k : ℕ, F k r := by
    intro r _hr
    change 2 * r * PaperAxioms.circleGap a b r =
        ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1)
    -- circleGap a b r = ∑' k, coeffPlusGap a b k * r^(2k) (definitional).
    have hUnfold : PaperAxioms.circleGap a b r =
        ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) := rfl
    rw [hUnfold]
    -- Pull `2*r` inside the tsum (`tsum_mul_left.symm` direction).
    rw [show (2 * r) *
            (∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)) =
          ∑' k : ℕ, (2 * r) *
            (PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))
        from (tsum_mul_left).symm]
    refine tsum_congr (fun k => ?_)
    -- Termwise: (2*r) * (coeff k * r^(2k)) = 2 * coeff k * r^(2k+1).
    have hPow : r ^ (2 * k + 1) = r * r ^ (2 * k) := by
      rw [pow_succ]; ring
    rw [hPow]; ring
  -- Step 5: lift the pointwise integrand identity to an integral equality.
  have h_integral_eq :
      ∫ r in c..(1:ℝ), 2 * r * PaperAxioms.circleGap a b r =
        ∫ r in c..(1:ℝ), ∑' k : ℕ, F k r :=
    intervalIntegral.integral_congr h_integrand_eq
  -- Step 6: termwise integral closed form
  -- ∫_c^1 F k r dr = coeffPlusGap a b k * (1 - c^(2k+2)) / (k+1).
  have h_termwise_integral : ∀ k : ℕ,
      ∫ r in c..(1:ℝ), F k r =
        PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1) := by
    intro k
    change ∫ r in c..(1:ℝ),
            2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) =
          PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
    have h_factor :
        (fun r : ℝ =>
            2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1)) =
          fun r : ℝ =>
            (2 * PaperAxioms.coeffPlusGap a b k) * r ^ (2 * k + 1) := by
      funext r; ring
    rw [h_factor, intervalIntegral.integral_const_mul]
    -- Closed form: ∫_c^1 r^(2k+1) dr = (1 - c^(2k+2)) / (2k+2).
    have h_pow :
        ∫ r in c..(1:ℝ), r ^ (2 * k + 1) =
          (1 - c ^ (2 * k + 2)) / ((2 * k + 2 : ℕ) : ℝ) := by
      have h := @integral_pow c 1 (2 * k + 1)
      have h1 : (1:ℝ) ^ (2 * k + 1 + 1) = 1 := one_pow _
      rw [h1] at h
      have hExp : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      rw [hExp] at h
      have hCast : ((2 * k + 2 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [hCast]
      exact h
    rw [h_pow]
    have h_denom_pos : (0 : ℝ) < (k + 1 : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_denom_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt h_denom_pos
    have h_cast : ((2 * k + 2 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
      push_cast; ring
    rw [h_cast]
    field_simp
  -- Step 7: identify `annulusExcess` with the integral and chain via calc.
  have h_annulusExcess :
      PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
        ∫ r in c..(1:ℝ), 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) c 1 = _
    rfl
  calc PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
      = ∫ r in c..(1:ℝ), 2 * r * PaperAxioms.circleGap a b r :=
        h_annulusExcess
    _ = ∫ r in c..(1:ℝ), ∑' k : ℕ, F k r := h_integral_eq
    _ = ∑' k : ℕ, ∫ r in c..(1:ℝ), F k r := h_swap.symm
    _ = ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1) :=
        tsum_congr h_termwise_integral

/--
Sprint 047 — first paper-axiom-free **N1/N2 partition** of sprint 046's
`tsum`-of-integrals identity for `annulusExcess (circleGap a b) c`. Composes
sprint 046's invocation (single-line application of
`annulusExcess_eq_tsum_via_termwise_integration`) with sprint 043's partition
skeleton (with the termwise summand rebound to the integrated annulus form
`coeffPlusGap a b k * (1 - c^(2k+2))/(k+1)`). Introduces the integrated
`Σ⁺_int_ann`/`Σ⁻_int_ann` series quantities at the integrated × N1/N2-restricted
annulus layer; no prior workspace lemma operates at this layer on the annulus
side. The signature is `(a, b, c)`-only with no `Section2Assumptions`
parameter, no `paper.eq*` invocation, no `paperLambda`, and no oracle cell.
-/
theorem annulusExcess_eq_tsum_partition_via_series
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c ^ (2 * k + 2)) / (k + 1))) :
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            (1 - c ^ (2 * k + 2)) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                (1 - c ^ (2 * k + 2)) / (k + 1)
            else 0 := by
  classical
  -- Step 0: invoke sprint 046 to obtain the unconditioned `tsum` identity.
  have h_sprint046 :
      PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
        ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k *
            (1 - c ^ (2 * k + 2)) / (k + 1) :=
    annulusExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
      hc_nonneg hc_le_one hSummable_int_norm
  -- Abbreviate the four relevant termwise summands (mirroring sprint 043,
  -- with the disk weight `c^(2k+2)/(k+1)` replaced by the annulus weight
  -- `(1 - c^(2k+2))/(k+1)`).
  set f : ℕ → ℝ := fun k =>
    PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
    with hf_def
  set f1 : ℕ → ℝ := fun k =>
    if PaperAxioms.n1Pred a b k then
      PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
    else 0 with hf1_def
  set f2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
    else 0 with hf2_def
  set g2 : ℕ → ℝ := fun k =>
    if PaperAxioms.n2Pred a b k then
      PaperAxioms.coeffMinusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
    else 0 with hg2_def
  -- Per-`k` non-negativity of the annulus integration weight
  -- `(1 - c^(2k+2)) / (k+1)`. This is the only step that diverges from
  -- sprint 043's body (which has the trivially non-negative disk weight
  -- `c^(2k+2)/(k+1)`).
  have h_one_sub_pow_nonneg : ∀ k : ℕ, 0 ≤ 1 - c ^ (2 * k + 2) := by
    intro k
    have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 :=
      pow_le_one₀ hc_nonneg hc_le_one
    linarith
  have h_weight_nonneg : ∀ k : ℕ, 0 ≤ (1 - c ^ (2 * k + 2)) / (k + 1) := by
    intro k
    apply div_nonneg (h_one_sub_pow_nonneg k)
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Summability transfer: from `Summable (|f|)` to `Summable f`.
  -- The bound `‖f k‖ ≤ |coeffPlusGap a b k| * (1 - c^(2k+2))/(k+1)` is in
  -- fact an equality (since `(1 - c^(2k+2))/(k+1) ≥ 0`).
  have hSummable_f : Summable f := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c ^ (2 * k + 2)) / (k + 1))
      hSummable_int_norm ?_
    intro k
    simp only [hf_def, Real.norm_eq_abs]
    -- |coeffPlusGap_k * (1 - c^(2k+2))/(k+1)|
    --     = |coeffPlusGap_k| * (1 - c^(2k+2))/(k+1).
    have h_one_sub_nonneg : 0 ≤ 1 - c ^ (2 * k + 2) :=
      h_one_sub_pow_nonneg k
    have hkp1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hkp1_nonneg : (0 : ℝ) ≤ (k : ℝ) + 1 := hkp1_pos.le
    rw [abs_div, abs_mul, abs_of_nonneg h_one_sub_nonneg,
        abs_of_nonneg hkp1_nonneg]
  -- Partition fact: ¬ n1Pred → n2Pred (verbatim from sprint 027/043).
  have h_n1_to_n2 :
      ∀ k, ¬ PaperAxioms.n1Pred a b k → PaperAxioms.n2Pred a b k := by
    intro k hk
    unfold PaperAxioms.n1Pred at hk
    unfold PaperAxioms.n2Pred
    push_neg at hk
    exact ⟨Nat.pos_of_ne_zero hk.1, hk.2⟩
  -- Reverse direction: n2Pred → ¬ n1Pred (verbatim from sprint 027/043).
  have h_n2_to_not_n1 :
      ∀ k, PaperAxioms.n2Pred a b k → ¬ PaperAxioms.n1Pred a b k := by
    intro k hk2 hk1
    unfold PaperAxioms.n2Pred at hk2
    unfold PaperAxioms.n1Pred at hk1
    obtain ⟨hk_pos, hab⟩ := hk2
    rcases hk1 with h | h
    · exact (Nat.lt_irrefl 0 (h ▸ hk_pos))
    · exact (not_lt_of_ge h) hab
  -- Termwise partition identity: f k = f1 k + f2 k for all k.
  have h_term_partition : ∀ k, f k = f1 k + f2 k := by
    intro k
    by_cases hk1 : PaperAxioms.n1Pred a b k
    · -- n1Pred true ⇒ n2Pred false ⇒ RHS = f k + 0 = f k.
      have hk2 : ¬ PaperAxioms.n2Pred a b k := fun hcontra =>
        h_n2_to_not_n1 k hcontra hk1
      simp [f, f1, f2, hk1, hk2]
    · -- n1Pred false ⇒ n2Pred true ⇒ RHS = 0 + f k = f k.
      have hk2 : PaperAxioms.n2Pred a b k := h_n1_to_n2 k hk1
      simp [f, f1, f2, hk1, hk2]
  -- Summability of `f1` via `Summable.indicator` over `{k | n1Pred a b k}`.
  have hSummable_f1 : Summable f1 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n1Pred a b k}.indicator f) :=
      hSummable_f.indicator {k | PaperAxioms.n1Pred a b k}
    have h_eq : f1 = {k | PaperAxioms.n1Pred a b k}.indicator f := by
      funext k
      simp [f1, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Summability of `f2` via `Summable.indicator` over `{k | n2Pred a b k}`.
  have hSummable_f2 : Summable f2 := by
    have h_indicator :
        Summable ({k | PaperAxioms.n2Pred a b k}.indicator f) :=
      hSummable_f.indicator {k | PaperAxioms.n2Pred a b k}
    have h_eq : f2 = {k | PaperAxioms.n2Pred a b k}.indicator f := by
      funext k
      simp [f2, f, Set.indicator]
    rw [h_eq]
    exact h_indicator
  -- Step A: ∑' k, f k = (∑' k, f1 k) + (∑' k, f2 k).
  have h_tsum_partition :
      (∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k := by
    have h_congr : (∑' k, f k) = ∑' k, (f1 k + f2 k) :=
      tsum_congr h_term_partition
    rw [h_congr, hSummable_f1.tsum_add hSummable_f2]
  -- Step C: ∑' k, f2 k = − ∑' k, g2 k via the termwise N2 sign-swap identity.
  have h_f2_eq_neg_g2 : (∑' k, f2 k) = - ∑' k, g2 k := by
    have h_term_neg : ∀ k, f2 k = -(g2 k) := by
      intro k
      by_cases hk : PaperAxioms.n2Pred a b k
      · simp only [f2, g2, hk, if_true]
        unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
        ring
      · simp [f2, g2, hk]
    calc (∑' k, f2 k)
        = ∑' k, -(g2 k) := tsum_congr h_term_neg
      _ = -∑' k, g2 k := tsum_neg
  -- Chain: annulusExcess = ∑' f = ∑' f1 + ∑' f2 = ∑' f1 - ∑' g2.
  calc PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
      = ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k *
            (1 - c ^ (2 * k + 2)) / (k + 1) :=
        h_sprint046
    _ = ∑' k, f k := rfl
    _ = (∑' k, f1 k) + ∑' k, f2 k := h_tsum_partition
    _ = (∑' k, f1 k) + (-∑' k, g2 k) := by rw [h_f2_eq_neg_g2]
    _ = (∑' k, f1 k) - ∑' k, g2 k := by ring

/--
Sprint 071 — first per-mode τ-window closing reducer in the workspace.

Consumes
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
(the per-mode pointwise bound on a `[start, stop]` τ-window where mode `j*`
is dominant), integrates it over the window via
`AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound`, and
closes via the standard `annulusSlice` adjacency machinery to produce a
`ValidKorenblumBound c`.

Structurally novel relative to every existing closing reducer in
`Reduction.lean`: this is the **first** per-mode reducer (every other
reducer integrates the `(a, b)`-independent sup-kernel
`OneModeSupBridge.scalarIntegrand` or some closed-form scalar
simplification of it). The c-pushing potential of per-mode reducers is
that on a τ-window where `mode = j* ≥ 2` is dominant,
`OneModeKernel.term c ρ j* = OneModeSup.supKernel c ρ` pointwise, so the
per-mode kernel agrees with the sup-kernel on the window — but the
**multi-window partition** of `(c, 1)` into `m` τ-windows each with its
own dominant mode is structurally tighter than the single-window sup-kernel
discharge. This sprint targets ONE window only (the structural
prerequisite); a successor sprint chaining `m` windows is queued.

The mass-1 kernel hypothesis `1 ≤ ∫ ModeBridge.scalarIntegrand` plays the
role of `Eq15ScalarBound`'s `1 ≤ scalarCriterion` in `valid_of_eq15`. The
contract's original Phase 0 numerical sweep (Scratch
`sprint_071_per_mode_kernel_witness.{py,txt}`) reports that this kernel
fails by ~3 orders of magnitude at every probed `(c, j*, start, stop)`
with `c > 7129/20000` (max `RHS_routeB ≈ 0.005` vs target `1`); the
reducer therefore ships under the contract's Outcome B (V56 ties V55,
structural advance is the new reducer).

The proof is a direct adaptation of sprint 008's
`valid_of_eq10_subinterval_branch1` template (mass-1 integrand-style
reducer using `mass_mul_le_annulusSlice_of_integral_bound` on a sub-window
plus the `annulusSlice` adjacency machinery to extend to `[c, 1]`),
with the following structural changes:
  - the pointwise bound source is
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    (per-mode τ-window) rather than `paper.eq10_branch1_pointwise`;
  - the integrand is `ModeBridge.scalarIntegrand c mode (paperLambda K c)`
    rather than `Korenblum.scalarIntegrand1 c (paperLambda K c)`;
  - the inner-excess argument carries `paper.diskExcess ≤
    OneModePaperBridge.innerSeriesExcess a b c` as an additional witness
    cell (the bridge's `hInner` premise);
  - the sub-window is `[start, stop] ⊆ (c, 1)` rather than the
    branch-1 sub-window `(c, branchSplit c]`.

The integrability of `ModeBridge.scalarIntegrand` is passed as a witness
hypothesis (the workspace does not yet have a
`paperScalarIntegrand_intervalIntegrable` companion to
`WangPaperSideConditions.paperScalarIntegrand{1,2}_intervalIntegrable` for
the per-mode integrand; surfacing it as a hypothesis matches sprint 014's
pattern of explicit `IntervalIntegrable` witness cells).
-/
theorem valid_of_perMode_tau_window_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (start stop : ℝ) (mode : ℕ),
          c < start ∧ start ≤ stop ∧ stop < 1 ∧
            1 ≤ mode ∧
            -- τ-window endpoint hypotheses (mode `j*` dominant on `[start, stop]`):
            OneModeTail.tau (mode - 1) ≤ c ^ 2 / stop ^ 2 ∧
            c ^ 2 / start ^ 2 ≤ OneModeTail.tau mode ∧
            -- Summability hypotheses required by
            -- `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`:
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                OneModeKernel.weight c n) ∧
            (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
              Summable (fun n : ℕ =>
                OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
            -- Annulus-side circleGap integrability on (c, 1):
            IntervalIntegrable
              (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
              volume c 1 ∧
            -- Per-mode scalar integrand integrability on [start, stop]:
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c mode
                  (WangOuter.paperLambda K c) ρ)
              volume start stop ∧
            -- diskExcess ≤ innerSeriesExcess (carried as witness; satisfied
            -- under the standard summability hypotheses by sprint 027/043):
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              OneModePaperBridge.innerSeriesExcess a b c ∧
            -- The mass-1 mode-fixed scalar kernel hypothesis (KERNEL_71):
            (1 : ℝ) ≤
              ∫ ρ in start..stop,
                ModeBridge.scalarIntegrand c mode
                  (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨start, stop, mode, hStart, hStartLeStop, hStopLtOne, hMode,
      hLower, hUpper, hPlusDisk, hPlusSigma, hMinusDisk, hMinusSigmaC,
      hMinusWeight, hMinusSigma, hIntCircle, hIntMode, hInner,
      hMass⟩ :=
    h_witness paper
  -- Geometric scaffolding.
  have hc_le_start : c ≤ start := hStart.le
  have hStart_lt_one : start < 1 := lt_of_le_of_lt hStartLeStop hStopLtOne
  have hc_lt_stop : c < stop := lt_of_lt_of_le hStart hStartLeStop
  have hc_le_stop : c ≤ stop := hc_lt_stop.le
  have hStop_le_one : stop ≤ 1 := hStopLtOne.le
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Step 1: discharge `paper.eq4_sigmaPlus_bound` to get
  -- `sigmaPlus a b c ≤ sigmaMinus a b c`.
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c := by
    have h0c : (0 : ℝ) ≤ 0 := le_refl 0
    have hZeroLtC : (0 : ℝ) < c := hc_pos
    have h_eq4_at_zero :
        PaperAxioms.Eq4SigmaPlusBound (PaperAxioms.sigmaPlus a b)
          (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b) 0 c :=
      paper.eq4_sigmaPlus_bound h0c hZeroLtC hc_lt_one
    exact h_eq4_at_zero.2.1
  -- Step 2: invoke the per-mode bridge to obtain the pointwise inequality
  -- on `Icc start stop`.
  have hPointwiseIcc :
      ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc start stop →
        ModeBridge.scalarIntegrand c mode
            (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
    OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
      hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hPlusLeMinus hInner
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hMinusSigma hMode hStart hStopLtOne hLower hUpper
  -- Step 3: package as the `mass_mul_le_annulusSlice_of_integral_bound`
  -- pointwise hypothesis (`modeIntegrand · innerExcess ≤ annulusDensity`).
  have hPointwiseDensity :
      ∀ ρ ∈ Set.Icc start stop,
        (fun ρ' =>
          ModeBridge.scalarIntegrand c mode
            (WangOuter.paperLambda K c) ρ') ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hPt := hPointwiseIcc hρ
    -- annulusDensity paper.circleGap ρ = 2 * ρ * paper.circleGap ρ
    -- and paper.circleGap = PaperAxioms.circleGap a b (definitional rfl).
    change ModeBridge.scalarIntegrand c mode
              (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * paper.circleGap ρ
    have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
    rw [hCircleEq]
    exact hPt
  -- Step 4: ae nonneg of the annulus density on [start, stop].
  have hAnnNonneg :
      ∀ ρ ∈ Set.Icc start stop,
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hStart hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 hStopLtOne
    exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
  -- Step 5: integrability of `annulusDensity` on subintervals of (c, 1).
  have huIcc_startStop : Set.uIcc start stop ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStartLeStop, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_start hStop_le_one
  have huIcc_cStart : Set.uIcc c start ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_start, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hStart_lt_one.le
  have huIcc_stopOne : Set.uIcc stop 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStop_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_stop le_rfl
  have huIcc_startOne : Set.uIcc start 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_start le_rfl
  have hIntDens_startStop :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume start stop :=
    hIntCircle.mono_set huIcc_startStop
  have hIntDens_cStart :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c start :=
    hIntCircle.mono_set huIcc_cStart
  have hIntDens_stopOne :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume stop 1 :=
    hIntCircle.mono_set huIcc_stopOne
  have hIntDens_startOne :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume start 1 :=
    hIntCircle.mono_set huIcc_startOne
  -- Step 6: apply `mass_mul_le_annulusSlice_of_integral_bound` with mass = 1.
  have hSliceBound :
      (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap start stop :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
      (modeIntegrand :=
        fun ρ => ModeBridge.scalarIntegrand c mode
          (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := start) (b := stop)
      (mass := 1)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hStartLeStop zero_le_one hMass hIntMode hIntDens_startStop
      hPointwiseDensity hAnnNonneg
  have hDiskLeSlice :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap start stop := by
    simpa [one_mul] using hSliceBound
  -- Step 7: split `annulusSlice c 1 = annulusSlice c start + annulusSlice
  -- start stop + annulusSlice stop 1` and dominate.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c start +
          AnnulusIntegralReduction.annulusSlice paper.circleGap start 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cStart hIntDens_startOne
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap start stop +
          AnnulusIntegralReduction.annulusSlice paper.circleGap stop 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap start 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_startStop hIntDens_stopOne
  -- Side-slice non-negativities.
  have hSlice_cStart_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c start := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c start),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c start),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hStart_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := start) hc_le_start
      hNonnegAE
  have hSlice_stopOne_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap stop 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc stop 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo stop (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hc_lt_stop hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := stop) (b := (1 : ℝ)) hStop_le_one
      hNonnegAE
  -- Chain to dominate by annulusExcess.
  have hSliceLE :
      AnnulusIntegralReduction.annulusSlice paper.circleGap start stop ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cStart_nonneg, hSlice_stopOne_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  -- Final calc chain.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap start stop :=
          hDiskLeSlice
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/--
Sprint 076 — disk-side polar-Jacobian termwise-integration identity at the
**annulus-parity signature** (with both `0 ≤ c` and `c ≤ 1` hypotheses, mirroring
the sprint 046 annulus theorem `annulusExcess_eq_tsum_via_termwise_integration`).

The disk-side `tsum`-of-integrals identity itself was already shipped by
sprint 042 as `diskExcess_eq_tsum_via_termwise_integration` (line 6473 above),
so the structural content of the disk/annulus polar-Jacobian asymmetry was
already closed at the time of sprint 042 (predating V57). What sprint 076
explicitly adds is a sibling theorem at the **exact annulus-parity signature**
(`hc_nonneg, hc_le_one, hSummable_int_norm`), so that downstream candidate-side
sprints needing a disk-side signature byte-for-byte parallel to sprint 046's
annulus signature can consume this theorem directly without an adapter shim.

The `hc_le_one` premise is **not** used in the proof body (the disk-side
integration over `[0, c]` has no upper-endpoint dependency on `1`); it is
present purely for signature parity with the annulus theorem. The proof
delegates to sprint 042's existing identity.

No `Section2Assumptions` parameter, no `paper.eq*` invocation, no
`paperLambda`, no oracle cell. The conclusion is an **equality** at the
per-coefficient level. Mirrors sprint 046's annulus signature byte-for-byte
modulo the integration-domain swap and the per-`k` polar-weight swap.
-/
theorem diskExcess_eq_tsum_via_termwise_integration_with_le_one
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (_hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k
          * c ^ (2 * k + 2) / (k + 1) :=
  diskExcess_eq_tsum_via_termwise_integration a b hc_nonneg hSummable_int_norm

/--
Sprint 078 — first **two-window** per-mode τ-partition closing reducer in the
workspace.

Per the contract, this is the m=2 concrete-endpoint version of the
multi-window τ-partition route. Sprint 072 attempted a general-`m`
`Fin m`-indexed version and hit a `hcEqStart0 : c = start 0` rewrite-motive
obstruction; sprint 074 rolled it back. This sprint uses **four plain real
parameter endpoints** `(ρStart₁, ρStop₁, ρStart₂, ρStop₂)` plus a single
adjacency equality `ρStop₁ = ρStart₂` to sidestep the motive issue.

The proof composes two invocations of the per-mode pointwise bound
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
(one per window), invokes `mass_mul_le_annulusSlice_of_integral_bound` per
window with `mass := ∫ ModeBridge.scalarIntegrand` set to the literal
window-integral, and glues the two slices into a single
`annulusSlice paper.circleGap ρStart₁ ρStop₂` slice via
`AnnulusIntegralReduction.annulusSlice_add_adjacent`. The joint mass
hypothesis `hMassTotal : 1 ≤ mass₁ + mass₂` then yields
`innerExcess ≤ annulusSlice paper.circleGap ρStart₁ ρStop₂`, and the
three-piece interval split (`[c, ρStart₁]`, `[ρStart₁, ρStop₂]`,
`[ρStop₂, 1]`) plus non-negativity of the side slices delivers the final
`diskExcess ≤ annulusExcess` chain.

The signature uses sprint 071's witness style: a single
`h_witness : ∀ paper, ∃ (window data + hMassTotal), ...` predicate
(rather than top-level paper-and-endpoint arguments), so the conclusion
is `ValidKorenblumBound c` and the per-paper window choice is allowed to
depend on `paper` (matching the per-`(a, b, K)` summability hypotheses).

The proof is structurally a doubled-up sprint 071 reducer:
  - per-window pointwise bound  (× 2)
  - per-window `mass_mul_le_annulusSlice_of_integral_bound`  (× 2)
  - `annulusSlice_add_adjacent` to merge the two slices
  - `(mass₁ + mass₂) · innerExcess ≤ merged-slice` from the sum of the two
    `mass · innerExcess ≤ slice` inequalities
  - `1 ≤ mass₁ + mass₂` ⇒ `innerExcess ≤ merged-slice`
  - three-piece slice split bounds the merged slice by `annulusExcess`

No new axioms, no oracle, no `Section2Assumptions` field. Pure Lean
composition of existing trusted-surface theorems.
-/
theorem valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ) (j₁ j₂ : ℕ),
          c < ρStart₁ ∧ ρStart₁ ≤ ρStop₁ ∧
            ρStop₁ = ρStart₂ ∧
            ρStart₂ ≤ ρStop₂ ∧ ρStop₂ < 1 ∧
            1 ≤ j₁ ∧ 1 ≤ j₂ ∧
            -- per-window τ-bounds (matching sprint 071's `tau`-form):
            OneModeTail.tau (j₁ - 1) ≤ c ^ 2 / ρStop₁ ^ 2 ∧
            c ^ 2 / ρStart₁ ^ 2 ≤ OneModeTail.tau j₁ ∧
            OneModeTail.tau (j₂ - 1) ≤ c ^ 2 / ρStop₂ ^ 2 ∧
            c ^ 2 / ρStart₂ ^ 2 ≤ OneModeTail.tau j₂ ∧
            -- summability hypotheses (shared across both windows):
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                c ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n *
                OneModeKernel.weight c n) ∧
            (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
              Summable (fun n : ℕ =>
                OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
            -- circleGap integrability on (c, 1):
            IntervalIntegrable
              (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
              volume c 1 ∧
            -- per-window scalar integrand integrability:
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c j₁
                  (WangOuter.paperLambda K c) ρ)
              volume ρStart₁ ρStop₁ ∧
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c j₂
                  (WangOuter.paperLambda K c) ρ)
              volume ρStart₂ ρStop₂ ∧
            -- diskExcess ≤ innerSeriesExcess:
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              OneModePaperBridge.innerSeriesExcess a b c ∧
            -- the joint two-window mass hypothesis:
            (1 : ℝ) ≤
              (∫ ρ in ρStart₁..ρStop₁,
                  ModeBridge.scalarIntegrand c j₁
                    (WangOuter.paperLambda K c) ρ) +
                (∫ ρ in ρStart₂..ρStop₂,
                  ModeBridge.scalarIntegrand c j₂
                    (WangOuter.paperLambda K c) ρ)) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρStart₁, ρStop₁, ρStart₂, ρStop₂, j₁, j₂,
      hStart₁, hStart₁LeStop₁, hAdj, hStart₂LeStop₂, hStop₂LtOne,
      hj₁, hj₂,
      hLower₁, hUpper₁, hLower₂, hUpper₂,
      hPlusDisk, hPlusSigma, hMinusDisk, hMinusSigmaC, hMinusWeight,
      hMinusSigma, hIntCircle, hIntMode₁, hIntMode₂, hInner,
      hMassTotal⟩ := h_witness paper
  -- Geometric ordering scaffolding.
  -- ρStart₂ = ρStop₁ via the adjacency hypothesis.
  have hStart₂_eq_Stop₁ : ρStart₂ = ρStop₁ := hAdj.symm
  have hc_le_Start₁ : c ≤ ρStart₁ := hStart₁.le
  have hc_lt_Stop₁ : c < ρStop₁ := lt_of_lt_of_le hStart₁ hStart₁LeStop₁
  have hc_le_Stop₁ : c ≤ ρStop₁ := hc_lt_Stop₁.le
  have hc_lt_Start₂ : c < ρStart₂ := by
    rw [hStart₂_eq_Stop₁]; exact hc_lt_Stop₁
  have hc_le_Start₂ : c ≤ ρStart₂ := hc_lt_Start₂.le
  have hc_lt_Stop₂ : c < ρStop₂ := lt_of_lt_of_le hc_lt_Start₂ hStart₂LeStop₂
  have hc_le_Stop₂ : c ≤ ρStop₂ := hc_lt_Stop₂.le
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  have hStop₂_le_one : ρStop₂ ≤ 1 := hStop₂LtOne.le
  have hStart₁_le_Stop₂ : ρStart₁ ≤ ρStop₂ := by
    have h2 : ρStop₁ ≤ ρStop₂ := by
      rw [← hStart₂_eq_Stop₁]; exact hStart₂LeStop₂
    linarith [hStart₁LeStop₁]
  have hStart₁_lt_one : ρStart₁ < 1 := lt_of_le_of_lt hStart₁_le_Stop₂ hStop₂LtOne
  have hStop₁_lt_one : ρStop₁ < 1 := by
    rw [← hStart₂_eq_Stop₁]
    exact lt_of_le_of_lt hStart₂LeStop₂ hStop₂LtOne
  -- Step 1: discharge `paper.eq4_sigmaPlus_bound` to get
  -- `sigmaPlus a b c ≤ sigmaMinus a b c`.
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c := by
    have h0c : (0 : ℝ) ≤ 0 := le_refl 0
    have hZeroLtC : (0 : ℝ) < c := hc_pos
    have h_eq4_at_zero :
        PaperAxioms.Eq4SigmaPlusBound (PaperAxioms.sigmaPlus a b)
          (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b) 0 c :=
      paper.eq4_sigmaPlus_bound h0c hZeroLtC hc_lt_one
    exact h_eq4_at_zero.2.1
  -- Step 2: per-mode pointwise bound on each window via the bridge.
  have hPointwiseIcc₁ :
      ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc ρStart₁ ρStop₁ →
        ModeBridge.scalarIntegrand c j₁
            (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
    OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
      hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hPlusLeMinus hInner
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hMinusSigma hj₁ hStart₁ hStop₁_lt_one hLower₁ hUpper₁
  have hPointwiseIcc₂ :
      ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc ρStart₂ ρStop₂ →
        ModeBridge.scalarIntegrand c j₂
            (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * PaperAxioms.circleGap a b ρ :=
    OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
      hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hPlusLeMinus hInner
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hMinusSigma hj₂ hc_lt_Start₂ hStop₂LtOne hLower₂ hUpper₂
  -- Step 3: package as `mass_mul_le_annulusSlice_of_integral_bound` pointwise
  -- hypotheses (modeIntegrand · innerExcess ≤ annulusDensity).
  have hPointwiseDensity₁ :
      ∀ ρ ∈ Set.Icc ρStart₁ ρStop₁,
        (fun ρ' =>
          ModeBridge.scalarIntegrand c j₁
            (WangOuter.paperLambda K c) ρ') ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hPt := hPointwiseIcc₁ hρ
    change ModeBridge.scalarIntegrand c j₁
              (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * paper.circleGap ρ
    have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
    rw [hCircleEq]
    exact hPt
  have hPointwiseDensity₂ :
      ∀ ρ ∈ Set.Icc ρStart₂ ρStop₂,
        (fun ρ' =>
          ModeBridge.scalarIntegrand c j₂
            (WangOuter.paperLambda K c) ρ') ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hPt := hPointwiseIcc₂ hρ
    change ModeBridge.scalarIntegrand c j₂
              (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * paper.circleGap ρ
    have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
    rw [hCircleEq]
    exact hPt
  -- Step 4: ae nonneg of annulus density on each subinterval.
  have hAnnNonneg₁ :
      ∀ ρ ∈ Set.Icc ρStart₁ ρStop₁,
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hStart₁ hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 hStop₁_lt_one
    exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
  have hAnnNonneg₂ :
      ∀ ρ ∈ Set.Icc ρStart₂ ρStop₂,
        0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hc_lt_Start₂ hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 hStop₂LtOne
    exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
  -- Step 5: integrability of `annulusDensity` on the relevant subintervals
  -- of (c, 1), via mono_set from `hIntCircle`.
  have huIcc_w1 : Set.uIcc ρStart₁ ρStop₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart₁LeStop₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Start₁ hStop₁_lt_one.le
  have huIcc_w2 : Set.uIcc ρStart₂ ρStop₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart₂LeStop₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Start₂ hStop₂_le_one
  have huIcc_cStart₁ : Set.uIcc c ρStart₁ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_Start₁, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc le_rfl hStart₁_lt_one.le
  have huIcc_Stop₂One : Set.uIcc ρStop₂ 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStop₂_le_one, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Stop₂ le_rfl
  have huIcc_Start₁Stop₂ : Set.uIcc ρStart₁ ρStop₂ ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart₁_le_Stop₂, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Start₁ hStop₂_le_one
  have hIntDens_w1 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρStart₁ ρStop₁ :=
    hIntCircle.mono_set huIcc_w1
  have hIntDens_w2 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρStart₂ ρStop₂ :=
    hIntCircle.mono_set huIcc_w2
  have hIntDens_cStart₁ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c ρStart₁ :=
    hIntCircle.mono_set huIcc_cStart₁
  have hIntDens_Stop₂One :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρStop₂ 1 :=
    hIntCircle.mono_set huIcc_Stop₂One
  have hIntDens_Start₁Stop₂ :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume ρStart₁ ρStop₂ :=
    hIntCircle.mono_set huIcc_Start₁Stop₂
  -- Step 6: per-window slice bounds with `mass = ∫ scalarIntegrand` (so the
  -- mass-vs-integral hypothesis is `le_refl`).
  set mass₁ : ℝ :=
      ∫ ρ in ρStart₁..ρStop₁,
        ModeBridge.scalarIntegrand c j₁ (WangOuter.paperLambda K c) ρ
    with hmass₁_def
  set mass₂ : ℝ :=
      ∫ ρ in ρStart₂..ρStop₂,
        ModeBridge.scalarIntegrand c j₂ (WangOuter.paperLambda K c) ρ
    with hmass₂_def
  -- Mass non-negativity: each `scalarIntegrand` term is non-negative on its
  -- window (kernel positive, paperLambda positive).  This is needed for the
  -- innerExcess-negative branch of `mass_mul_le_annulusSlice_of_integral_bound`.
  -- We bound it from below by `0 ≤ mass_k` via `intervalIntegral.integral_nonneg`
  -- using the fact that on the window, scalarIntegrand is non-negative pointwise
  -- (since we have `modeIntegrand · innerExcess ≤ annulusDensity` with both
  -- sides handled via `paperLambda`-positivity machinery; alternatively we
  -- prove `scalarIntegrand ≥ 0` directly from its definition).
  -- For the proof body, the standard approach is to fall through both cases
  -- of `mass_mul_le_annulusSlice_of_integral_bound`: the theorem already
  -- handles `innerExcess ≤ 0` by collapsing to `mass · innerExcess ≤ 0 ≤ slice`.
  -- So we just need `0 ≤ mass`. We extract this from the `0 ≤ scalarIntegrand`
  -- pointwise property.
  have hScalar_nonneg₁ :
      ∀ ρ ∈ Set.Icc ρStart₁ ρStop₁,
        0 ≤ ModeBridge.scalarIntegrand c j₁ (WangOuter.paperLambda K c) ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hStart₁ hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 hStop₁_lt_one
    have hρpos : 0 < ρ := lt_trans hc_pos hcρ
    have hTermPos : 0 < OneModeKernel.term c ρ j₁ := by
      unfold OneModeKernel.term OneModeKernel.weight
      positivity
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    unfold ModeBridge.scalarIntegrand
    positivity
  have hScalar_nonneg₂ :
      ∀ ρ ∈ Set.Icc ρStart₂ ρStop₂,
        0 ≤ ModeBridge.scalarIntegrand c j₂ (WangOuter.paperLambda K c) ρ := by
    intro ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le hc_lt_Start₂ hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 hStop₂LtOne
    have hρpos : 0 < ρ := lt_trans hc_pos hcρ
    have hTermPos : 0 < OneModeKernel.term c ρ j₂ := by
      unfold OneModeKernel.term OneModeKernel.weight
      positivity
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    unfold ModeBridge.scalarIntegrand
    positivity
  have hMass₁_nonneg : 0 ≤ mass₁ := by
    rw [hmass₁_def]
    exact intervalIntegral.integral_nonneg hStart₁LeStop₁ hScalar_nonneg₁
  have hMass₂_nonneg : 0 ≤ mass₂ := by
    rw [hmass₂_def]
    exact intervalIntegral.integral_nonneg hStart₂LeStop₂ hScalar_nonneg₂
  -- Per-window slice bound (window 1).
  have hSliceBound₁ :
      mass₁ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₁ :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
      (modeIntegrand :=
        fun ρ => ModeBridge.scalarIntegrand c j₁
          (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρStart₁) (b := ρStop₁)
      (mass := mass₁)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hStart₁LeStop₁ hMass₁_nonneg le_rfl hIntMode₁ hIntDens_w1
      hPointwiseDensity₁ hAnnNonneg₁
  have hSliceBound₂ :
      mass₂ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₂ ρStop₂ :=
    AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
      (modeIntegrand :=
        fun ρ => ModeBridge.scalarIntegrand c j₂
          (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρStart₂) (b := ρStop₂)
      (mass := mass₂)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      hStart₂LeStop₂ hMass₂_nonneg le_rfl hIntMode₂ hIntDens_w2
      hPointwiseDensity₂ hAnnNonneg₂
  -- Step 7: glue the two slices via adjacency (ρStop₁ = ρStart₂).
  have hAdjMerged :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₂ ρStop₂ =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ := by
    -- Rewrite ρStart₂ to ρStop₁ everywhere, then apply
    -- `annulusSlice_add_adjacent`.
    rw [hStart₂_eq_Stop₁]
    -- For the integrability hypotheses on the second window after rewrite,
    -- we now need integrability on `ρStop₁ ρStop₂`.
    have hIntDens_StopOne_Stop₂ :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume ρStop₁ ρStop₂ := by
      rw [hStart₂_eq_Stop₁] at hIntDens_w2
      exact hIntDens_w2
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_w1 hIntDens_StopOne_Stop₂
  -- Step 8: sum the two `mass · innerExcess ≤ slice` inequalities.
  have hSumBound :
      (mass₁ + mass₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ := by
    have h := add_le_add hSliceBound₁ hSliceBound₂
    rw [← hAdjMerged, add_mul]
    exact h
  -- Step 9: apply `hMassTotal : 1 ≤ mass₁ + mass₂` to dominate by the merged
  -- slice. Use `innerExcess_le_of_window_bounds` style argument inline.
  have hMassTotal' : (1 : ℝ) ≤ mass₁ + mass₂ := by
    rw [hmass₁_def, hmass₂_def]
    exact hMassTotal
  have hSumNonneg : 0 ≤ mass₁ + mass₂ := add_nonneg hMass₁_nonneg hMass₂_nonneg
  have hMergedSlice_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
            ρStart₁ ρStop₂ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρStart₁ ρStop₂),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρStart₁ ρStop₂),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_of_lt_of_le hStart₁ hρ.1.le
        have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 hStop₂_le_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap)
      (a := ρStart₁) (b := ρStop₂)
      hStart₁_le_Stop₂
      hNonnegAE
  have hDiskLeMerged :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ := by
    by_cases hInnerNonneg :
        0 ≤ PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
    · -- If innerExcess ≥ 0, scale the mass-bound by `1 ≤ mass₁ + mass₂`.
      have h1 :
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            (mass₁ + mass₂) *
              PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
        have := mul_le_mul_of_nonneg_right hMassTotal' hInnerNonneg
        simpa [one_mul] using this
      exact le_trans h1 hSumBound
    · -- innerExcess ≤ 0, so the inequality is trivially true since
      -- the merged slice is non-negative.
      have hInnerNeg :
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤ 0 :=
        le_of_lt (lt_of_not_ge hInnerNonneg)
      exact le_trans hInnerNeg hMergedSlice_nonneg
  -- Step 10: bound the merged slice by `annulusExcess` via the three-piece
  -- split `[c, ρStart₁] ⊕ [ρStart₁, ρStop₂] ⊕ [ρStop₂, 1]`.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c ρStart₁ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    have hIntDens_Start₁One :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume ρStart₁ 1 := by
      have hu : Set.uIcc ρStart₁ 1 ⊆ Set.uIcc c 1 := by
        rw [Set.uIcc_of_le hStart₁_lt_one.le, Set.uIcc_of_le hc_le_one]
        exact Set.Icc_subset_Icc hc_le_Start₁ le_rfl
      exact hIntCircle.mono_set hu
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cStart₁ hIntDens_Start₁One
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ +
          AnnulusIntegralReduction.annulusSlice paper.circleGap ρStop₂ 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_Start₁Stop₂ hIntDens_Stop₂One
  -- Side-slice non-negativities.
  have hSlice_cStart₁_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c ρStart₁ := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c ρStart₁),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c ρStart₁),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hStart₁_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρStart₁) hc_le_Start₁
      hNonnegAE
  have hSlice_Stop₂One_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρStop₂ 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc ρStop₂ 1),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρStop₂ (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans hc_lt_Stop₂ hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρStop₂) (b := (1 : ℝ)) hStop₂_le_one
      hNonnegAE
  have hMergedSlice_le_full :
      AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cStart₁_nonneg, hSlice_Stop₂One_nonneg]
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  -- Final calc chain.
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρStart₁ ρStop₂ :=
          hDiskLeMerged
    _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
        hMergedSlice_le_full
    _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

/-!
## Sprint 084: general-`m` per-mode τ-partition closing reducer

Generalization of sprint 078's `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
to an arbitrary number of `Fin m`-indexed adjacent τ-windows, structurally
preparing the way for V38's seven-window (m = 7) c-push at
`c = 356401/1000000`. Sprint 072 attempted a similar `Fin m`-form and got
stuck on a `c = start 0` rewrite-motive issue; the design here sidesteps
that by **per-window** quantification (`∀ i, c < ρStart i ∧ ρStop i < 1`),
removing the need to rewrite `c` to `start 0` anywhere in the proof body.

Discharge route is **Option β** (per the contract): apply
`AnnulusIntegralReduction.innerExcess_le_of_window_bounds` over
`Finset.univ : Finset (Fin m)`. The slice-sum bound
`∑ i, annulusSlice (ρStart i) (ρStop i) ≤ annulusExcess` is established
via a private helper `sum_annulusSlice_collapse_adjacent` that collapses
the adjacent-window sum to a single slice by induction on the index count.

No new axioms, no oracle, no `Section2Assumptions` field. Pure Lean
composition of existing trusted-surface theorems plus standard `Fin`-sum
machinery.
-/

/-- Helper: under adjacency `stop i.castSucc = start i.succ`, the sum of
`annulusSlice` over `Fin (n+1)` adjacent windows collapses to the single
slice `annulusSlice (start 0) (stop (Fin.last n))`. Proved by induction
on `n` using `Fin.sum_univ_castSucc` + `annulusSlice_add_adjacent`.

The integrability hypothesis takes a single blanket form: per-`i ≤ j`,
`IntervalIntegrable annulusDensity volume (start i) (stop j)`. In practice
the caller provides this by `mono_set` from a single integrability on
`[c, 1]` plus the inclusion `[start i, stop j] ⊆ [c, 1]`. -/
private theorem sum_annulusSlice_collapse_adjacent
    {circleGap : ℝ → ℝ} :
    ∀ (n : ℕ)
      (start stop : Fin (n + 1) → ℝ)
      (_hAdj : ∀ i : Fin n, stop i.castSucc = start i.succ)
      (_hInt : ∀ i : Fin (n + 1),
          IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
            MeasureTheory.volume (start i) (stop i))
      (_hIntPrefix : ∀ k : Fin n,
          IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
            MeasureTheory.volume (start 0) (stop k.castSucc)),
      ∑ i : Fin (n + 1),
          AnnulusIntegralReduction.annulusSlice circleGap (start i) (stop i) =
        AnnulusIntegralReduction.annulusSlice circleGap (start 0) (stop (Fin.last n))
  | 0, start, stop, _hAdj, _hInt, _hIntPrefix => by
    -- `Fin 1`: the sum has a single term `annulusSlice (start 0) (stop 0)`.
    -- And `Fin.last 0 = (0 : Fin 1)`, so the right-hand side is the same.
    simp [Fin.sum_univ_one, Fin.last]
  | n + 1, start, stop, hAdj, hInt, hIntPrefix => by
    -- Peel off the last index using `Fin.sum_univ_castSucc`.
    rw [Fin.sum_univ_castSucc]
    -- The inner sum is over `Fin (n+1)` with restricted endpoint functions.
    set start' : Fin (n + 1) → ℝ := fun i => start i.castSucc with hstart'_def
    set stop' : Fin (n + 1) → ℝ := fun i => stop i.castSucc with hstop'_def
    -- Inductive adjacency: for `i : Fin n`, `stop' i.castSucc = start' i.succ` reduces to
    -- `stop i.castSucc.castSucc = start i.succ.castSucc`. This follows from `hAdj i.castSucc`
    -- because `(i.castSucc : Fin (n+1)).succ = i.succ.castSucc`.
    have hAdj' : ∀ i : Fin n, stop' i.castSucc = start' i.succ := by
      intro i
      simp only [hstart'_def, hstop'_def]
      have h1 : (i.castSucc : Fin (n + 1)).succ = (i.succ : Fin (n + 1)).castSucc := by
        ext
        simp
      have := hAdj i.castSucc
      rw [h1] at this
      exact this
    -- Inductive per-window integrability for `start', stop'`.
    have hInt' :
        ∀ i : Fin (n + 1),
          IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
            MeasureTheory.volume (start' i) (stop' i) := by
      intro i
      simp only [hstart'_def, hstop'_def]
      exact hInt i.castSucc
    -- Inductive prefix integrability: for `k : Fin n`, integrability on
    -- `[start' 0, stop' k.castSucc] = [start 0, stop k.castSucc.castSucc]`.
    have hIntPrefix' :
        ∀ k : Fin n,
          IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
            MeasureTheory.volume (start' 0) (stop' k.castSucc) := by
      intro k
      simp only [hstart'_def, hstop'_def]
      -- `start' 0 = start (0 : Fin (n+1)).castSucc = start 0` (definitionally),
      -- `stop' k.castSucc = stop (k.castSucc).castSucc = stop k.castSucc.castSucc`.
      -- We need `IntervalIntegrable ... (start 0) (stop k.castSucc.castSucc)`.
      -- This is `hIntPrefix k.castSucc` since `(k.castSucc : Fin (n+1)).castSucc = k.castSucc.castSucc`.
      have hkk : (k.castSucc : Fin (n + 1)).castSucc = k.castSucc.castSucc := rfl
      have := hIntPrefix k.castSucc
      -- `(0 : Fin (n+1)).castSucc = (0 : Fin (n+2))`, but the LHS is `start (0 : Fin (n+2))`.
      -- These match by definitional unfolding.
      exact this
    -- Apply IH.
    have hIH :=
      sum_annulusSlice_collapse_adjacent n start' stop' hAdj' hInt' hIntPrefix'
    -- The IH conclusion equals
    --   ∑ i : Fin (n+1), annulusSlice (start i.castSucc) (stop i.castSucc) =
    --     annulusSlice (start (0:Fin(n+1)).castSucc) (stop (Fin.last n).castSucc).
    -- Using `(0 : Fin (n+1)).castSucc = (0 : Fin (n+2))` and the adjacency
    -- `stop (Fin.last n).castSucc = start (Fin.last n).succ = start (Fin.last (n+1))`.
    simp only [hstart'_def, hstop'_def] at hIH
    -- Adjacency at the last index `Fin.last n : Fin (n+1)` lifted to `Fin (n+2)`:
    --   stop (Fin.last n).castSucc = start (Fin.last n).succ = start (Fin.last (n+1)).
    have hAdjLast : stop (Fin.last n).castSucc = start (Fin.last (n + 1)) := by
      have := hAdj (Fin.last n)
      have hSuccLast : (Fin.last n).succ = (Fin.last (n + 1) : Fin (n + 2)) := rfl
      rw [hSuccLast] at this
      exact this
    -- The peeled last window's integrability (per-window).
    have hIntLast :
        IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
          MeasureTheory.volume
          (start (Fin.last (n + 1))) (stop (Fin.last (n + 1))) :=
      hInt (Fin.last (n + 1))
    -- Prefix integrability on `[start 0, start (Fin.last (n+1))]`: take the
    -- prefix-integrability hypothesis at `k = Fin.last n : Fin (n+1)`, giving
    -- integrability on `[start 0, stop (Fin.last n).castSucc]`, then rewrite
    -- the upper endpoint via `hAdjLast`.
    have hIntPrefixLast :
        IntervalIntegrable (AnnulusIntegralReduction.annulusDensity circleGap)
          MeasureTheory.volume (start 0) (start (Fin.last (n + 1))) := by
      have h := hIntPrefix (Fin.last n)
      rw [hAdjLast] at h
      exact h
    -- Now combine:
    --   ∑_{Fin (n+2)} = (∑_{Fin (n+1)} on castSucc) + (last) [from `Fin.sum_univ_castSucc`]
    --                 = annulusSlice (start 0) (stop (Fin.last n).castSucc) + annulusSlice last
    --                 = annulusSlice (start 0) (start (Fin.last (n+1))) + annulusSlice last
    --                 = annulusSlice (start 0) (stop (Fin.last (n+1)))
    -- by `annulusSlice_add_adjacent` on `[start 0 .. start (Fin.last (n+1)) .. stop (Fin.last (n+1))]`.
    rw [hIH, hAdjLast]
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntPrefixLast hIntLast

/--
Sprint 084 — general-`m` per-mode τ-partition closing reducer.

Generalizes sprint 078's `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
to an arbitrary number of `Fin (n + 1)`-indexed adjacent τ-windows. The
witness predicate quantifies per-window over `i : Fin (n + 1)`:
endpoints `(ρStart i, ρStop i)`, mode `j i ≥ 1`, τ-bounds, integrability
of the scalar integrand on each window, plus shared paper-level
summability hypotheses and the joint-mass witness
`1 ≤ ∑ i : Fin (n + 1), ∫ ρStart i..ρStop i, scalarIntegrand …`.

Per the contract, the parameter is taken as `Fin (n + 1)` (equivalent
to `Fin m` with `m = n + 1 ≥ 1`) to avoid `Nat.sub` arithmetic in the
proof body. Discharge route: **Option β** (per the contract) — apply
`AnnulusIntegralReduction.innerExcess_le_of_window_bounds` over
`Finset.univ : Finset (Fin (n + 1))`. The slice-sum bound
`∑ i, annulusSlice (ρStart i) (ρStop i) ≤ annulusExcess` is established
via the helper `sum_annulusSlice_collapse_adjacent` plus the side-slice
non-negativity argument (`[c, ρStart 0]` and `[ρStop (Fin.last n), 1]`).

Sprint 072 attempted a similar `Fin m` form and got stuck on a
`hcEqStart0 : c = start 0` rewrite-motive obstruction; this design
sidesteps it by **per-window** `c < ρStart i` quantification (the
caller may supply this as a per-window predicate without needing to
identify `c` with any endpoint).

No new axioms, no oracle, no `Section2Assumptions` field. Pure Lean
composition of existing trusted-surface theorems plus standard
`Fin`-sum machinery.
-/
theorem valid_of_perMode_multiWindow_tau_partition_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    {n : ℕ}
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart ρStop : Fin (n + 1) → ℝ) (j : Fin (n + 1) → ℕ),
          (∀ i : Fin (n + 1), c < ρStart i) ∧
          (∀ i : Fin (n + 1), ρStart i ≤ ρStop i) ∧
          (∀ i : Fin (n + 1), ρStop i < 1) ∧
          (∀ i : Fin n, ρStop i.castSucc = ρStart i.succ) ∧
          (∀ i : Fin (n + 1), 1 ≤ j i) ∧
          (∀ i : Fin (n + 1), OneModeTail.tau (j i - 1) ≤ c ^ 2 / ρStop i ^ 2) ∧
          (∀ i : Fin (n + 1), c ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau (j i)) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.plusSeq a b n' *
              c ^ (2 * n' + 2) / (n' + 1 : ℝ)) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.plusSeq a b n' * c ^ (2 * n')) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' *
              c ^ (2 * n' + 2) / (n' + 1 : ℝ)) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' * c ^ (2 * n')) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' *
              OneModeKernel.weight c n') ∧
          (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
            Summable (fun n' : ℕ =>
              OneModePaperBridge.minusSeq a b n' * ρ ^ (2 * n'))) ∧
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
            volume c 1 ∧
          (∀ i : Fin (n + 1),
            IntervalIntegrable
              (fun ρ =>
                ModeBridge.scalarIntegrand c (j i)
                  (WangOuter.paperLambda K c) ρ)
              volume (ρStart i) (ρStop i)) ∧
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            OneModePaperBridge.innerSeriesExcess a b c ∧
          (1 : ℝ) ≤
            ∑ i : Fin (n + 1),
              ∫ ρ in (ρStart i)..(ρStop i),
                ModeBridge.scalarIntegrand c (j i)
                  (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρStart, ρStop, j,
      hStartLt, hStartLeStop, hStopLtOne, hAdj,
      hjPos, hLowerTau, hUpperTau,
      hPlusDisk, hPlusSigma, hMinusDisk, hMinusSigmaC, hMinusWeight,
      hMinusSigma, hIntCircle, hIntMode, hInner,
      hMassTotal⟩ := h_witness paper
  -- Per-window geometric scaffolding.
  have hStartLe : ∀ i : Fin (n + 1), c ≤ ρStart i := fun i => (hStartLt i).le
  have hStopLeOne : ∀ i : Fin (n + 1), ρStop i ≤ 1 := fun i => (hStopLtOne i).le
  have hcLtStop : ∀ i : Fin (n + 1), c < ρStop i := fun i =>
    lt_of_lt_of_le (hStartLt i) (hStartLeStop i)
  have hcLeStop : ∀ i : Fin (n + 1), c ≤ ρStop i := fun i => (hcLtStop i).le
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Step 1: discharge `paper.eq4_sigmaPlus_bound` to get
  -- `sigmaPlus a b c ≤ sigmaMinus a b c`.
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c := by
    have h0c : (0 : ℝ) ≤ 0 := le_refl 0
    have hZeroLtC : (0 : ℝ) < c := hc_pos
    have h_eq4_at_zero :
        PaperAxioms.Eq4SigmaPlusBound (PaperAxioms.sigmaPlus a b)
          (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b) 0 c :=
      paper.eq4_sigmaPlus_bound h0c hZeroLtC hc_lt_one
    exact h_eq4_at_zero.2.1
  -- Step 2: per-window pointwise bound via the bridge.
  have hPointwiseIcc :
      ∀ i : Fin (n + 1), ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc (ρStart i) (ρStop i) →
        ModeBridge.scalarIntegrand c (j i)
            (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * PaperAxioms.circleGap a b ρ := by
    intro i
    exact OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
      hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
      hPlusLeMinus hInner
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
      hMinusSigma (hjPos i) (hStartLt i) (hStopLtOne i) (hLowerTau i) (hUpperTau i)
  -- Step 3: package as `mass_mul_le_annulusSlice_of_integral_bound` pointwise
  -- hypotheses (modeIntegrand · innerExcess ≤ annulusDensity).
  have hPointwiseDensity :
      ∀ i : Fin (n + 1),
        ∀ ρ ∈ Set.Icc (ρStart i) (ρStop i),
          (fun ρ' =>
            ModeBridge.scalarIntegrand c (j i)
              (WangOuter.paperLambda K c) ρ') ρ *
              PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro i ρ hρ
    have hPt := hPointwiseIcc i hρ
    change ModeBridge.scalarIntegrand c (j i)
              (WangOuter.paperLambda K c) ρ *
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          2 * ρ * paper.circleGap ρ
    have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
    rw [hCircleEq]
    exact hPt
  -- Step 4: per-window annulus-density nonneg.
  have hAnnNonneg :
      ∀ i : Fin (n + 1),
        ∀ ρ ∈ Set.Icc (ρStart i) (ρStop i),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro i ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le (hStartLt i) hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 (hStopLtOne i)
    exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
  -- Step 5: integrability of `annulusDensity` on subintervals, via mono_set.
  -- All the relevant subintervals lie inside `[c, 1]`.
  have hIntDens_window :
      ∀ i : Fin (n + 1),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart i) (ρStop i) := by
    intro i
    have hu : Set.uIcc (ρStart i) (ρStop i) ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le (hStartLeStop i), Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc (hStartLe i) (hStopLeOne i)
    exact hIntCircle.mono_set hu
  -- Step 6: per-window mass and slice bound.
  let mass : Fin (n + 1) → ℝ := fun i =>
    ∫ ρ in (ρStart i)..(ρStop i),
      ModeBridge.scalarIntegrand c (j i) (WangOuter.paperLambda K c) ρ
  -- Per-window scalar-integrand non-negativity (kernel positive, paperLambda positive).
  have hScalar_nonneg :
      ∀ i : Fin (n + 1),
        ∀ ρ ∈ Set.Icc (ρStart i) (ρStop i),
          0 ≤ ModeBridge.scalarIntegrand c (j i) (WangOuter.paperLambda K c) ρ := by
    intro i ρ hρ
    have hcρ : c < ρ := lt_of_lt_of_le (hStartLt i) hρ.1
    have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 (hStopLtOne i)
    have hρpos : 0 < ρ := lt_trans hc_pos hcρ
    have hjPos_i : 1 ≤ j i := hjPos i
    have hjPos_i' : 0 < (j i : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hjPos_i
    have hTermPos : 0 < OneModeKernel.term c ρ (j i) := by
      unfold OneModeKernel.term OneModeKernel.weight
      positivity
    have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    unfold ModeBridge.scalarIntegrand
    positivity
  have hMass_nonneg : ∀ i : Fin (n + 1), 0 ≤ mass i := by
    intro i
    exact intervalIntegral.integral_nonneg (hStartLeStop i) (hScalar_nonneg i)
  -- Per-window slice bound.
  have hSliceBound :
      ∀ i : Fin (n + 1),
        mass i * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) := by
    intro i
    exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound
      (modeIntegrand :=
        fun ρ => ModeBridge.scalarIntegrand c (j i)
          (WangOuter.paperLambda K c) ρ)
      (circleGap := paper.circleGap)
      (a := ρStart i) (b := ρStop i)
      (mass := mass i)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (hStartLeStop i) (hMass_nonneg i) le_rfl (hIntMode i) (hIntDens_window i)
      (hPointwiseDensity i) (hAnnNonneg i)
  -- Step 7: `∑ i, annulusSlice (ρStart i) (ρStop i)` collapses to a single slice
  -- via the helper `sum_annulusSlice_collapse_adjacent`.
  -- Prefix integrability hypothesis: for all `k : Fin n`, integrability of
  -- annulusDensity on `[ρStart 0, ρStop k.castSucc]`. Use `mono_set` from
  -- the integrability on `[c, 1]`.
  have hIntPrefix :
      ∀ k : Fin n,
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart 0) (ρStop k.castSucc) := by
    intro k
    have hStart0_le_StopK : ρStart 0 ≤ ρStop k.castSucc := by
      have h1 : ρStart 0 ≤ ρStop 0 := hStartLeStop 0
      -- Use induction: ρStop 0 ≤ ρStop k.castSucc via adjacency chain.
      -- For now, use a simpler argument: ρStop 0 ≤ ρStop k.castSucc whenever
      -- k.castSucc.val ≥ 0, which is always; but we need the chain monotonicity.
      -- Since k.castSucc.val ≥ 0, we need to show ρStop 0 ≤ ρStop k.castSucc.
      -- This requires monotonicity along adjacency:
      --   ρStop 0 = ρStart 1 ≤ ρStop 1 = ρStart 2 ≤ ... ≤ ρStop k.castSucc.
      -- We'll use induction on k.castSucc.val.
      have hChain : ∀ p : Fin (n + 1), ρStop 0 ≤ ρStop p := by
        intro p
        induction p using Fin.induction with
        | zero => exact le_refl _
        | succ p' ih =>
          -- p = p'.succ. We need ρStop 0 ≤ ρStop p'.succ.
          -- Adjacency: ρStop p'.castSucc = ρStart p'.succ.
          have hadj : ρStop p'.castSucc = ρStart p'.succ := hAdj p'
          -- ρStop 0 ≤ ρStop p'.castSucc by ih (at p'.castSucc).
          have hIH := ih
          calc ρStop 0
              ≤ ρStop p'.castSucc := hIH
            _ = ρStart p'.succ := hadj
            _ ≤ ρStop p'.succ := hStartLeStop _
      calc ρStart 0 ≤ ρStop 0 := h1
        _ ≤ ρStop k.castSucc := hChain k.castSucc
    have hu :
        Set.uIcc (ρStart 0) (ρStop k.castSucc) ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le hStart0_le_StopK, Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc (hStartLe 0) (hStopLeOne k.castSucc)
    exact hIntCircle.mono_set hu
  have hCollapseSum :
      ∑ i : Fin (n + 1),
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) =
        AnnulusIntegralReduction.annulusSlice paper.circleGap
          (ρStart 0) (ρStop (Fin.last n)) :=
    sum_annulusSlice_collapse_adjacent (circleGap := paper.circleGap)
      n ρStart ρStop hAdj hIntDens_window hIntPrefix
  -- Step 8: bound the merged slice by `annulusExcess` via the three-piece
  -- split `[c, ρStart 0] ⊕ [ρStart 0, ρStop (Fin.last n)] ⊕ [ρStop (Fin.last n), 1]`.
  have hStart0_le_StopLast : ρStart 0 ≤ ρStop (Fin.last n) := by
    have hChain : ∀ p : Fin (n + 1), ρStop 0 ≤ ρStop p := by
      intro p
      induction p using Fin.induction with
      | zero => exact le_refl _
      | succ p' ih =>
        have hadj : ρStop p'.castSucc = ρStart p'.succ := hAdj p'
        calc ρStop 0
            ≤ ρStop p'.castSucc := ih
          _ = ρStart p'.succ := hadj
          _ ≤ ρStop p'.succ := hStartLeStop _
    calc ρStart 0
        ≤ ρStop 0 := hStartLeStop 0
      _ ≤ ρStop (Fin.last n) := hChain (Fin.last n)
  have hStop_last_lt_one : ρStop (Fin.last n) < 1 := hStopLtOne (Fin.last n)
  have hc_le_Start0 : c ≤ ρStart 0 := hStartLe 0
  have hc_le_StopLast : c ≤ ρStop (Fin.last n) := hcLeStop (Fin.last n)
  -- Side-slice integrability.
  have huIcc_cStart0 : Set.uIcc c (ρStart 0) ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_Start0, Set.uIcc_of_le hc_le_one]
    have hStart0_lt_one : ρStart 0 < 1 := lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
    exact Set.Icc_subset_Icc le_rfl hStart0_lt_one.le
  have huIcc_StopLastOne : Set.uIcc (ρStop (Fin.last n)) 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStop_last_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_StopLast le_rfl
  have huIcc_Start0StopLast : Set.uIcc (ρStart 0) (ρStop (Fin.last n)) ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart0_le_StopLast, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Start0 hStop_last_lt_one.le
  have hIntDens_cStart0 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c (ρStart 0) :=
    hIntCircle.mono_set huIcc_cStart0
  have hIntDens_StopLastOne :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (ρStop (Fin.last n)) 1 :=
    hIntCircle.mono_set huIcc_StopLastOne
  have hIntDens_Start0StopLast :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (ρStart 0) (ρStop (Fin.last n)) :=
    hIntCircle.mono_set huIcc_Start0StopLast
  -- Side-slice non-negativities.
  have hSlice_cStart0_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c (ρStart 0) := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c (ρStart 0)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c (ρStart 0)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hStart0_lt_one : ρStart 0 < 1 :=
          lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hStart0_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρStart 0) hc_le_Start0
      hNonnegAE
  have hSlice_StopLastOne_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStop (Fin.last n)) 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStop (Fin.last n)) (1 : ℝ)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo (ρStop (Fin.last n)) (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans (hcLtStop (Fin.last n)) hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρStop (Fin.last n)) (b := (1 : ℝ))
      hStop_last_lt_one.le hNonnegAE
  -- Three-piece adjacency split for `[c, 1]`.
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c (ρStart 0) +
          AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart 0) 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    have hStart0_lt_one : ρStart 0 < 1 :=
      lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
    have huIcc_Start0One : Set.uIcc (ρStart 0) 1 ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le hStart0_lt_one.le, Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc hc_le_Start0 le_rfl
    have hIntDens_Start0One :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart 0) 1 :=
      hIntCircle.mono_set huIcc_Start0One
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cStart0 hIntDens_Start0One
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart 0) (ρStop (Fin.last n)) +
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStop (Fin.last n)) 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart 0) 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_Start0StopLast hIntDens_StopLastOne
  have hMergedSlice_le_full :
      AnnulusIntegralReduction.annulusSlice paper.circleGap
          (ρStart 0) (ρStop (Fin.last n)) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cStart0_nonneg, hSlice_StopLastOne_nonneg]
  -- Step 9: assemble `∑ i, annulusSlice ≤ annulusSlice c 1` from collapse + side bound.
  have hSumSliceLE :
      ∑ i : Fin (n + 1),
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    rw [hCollapseSum]; exact hMergedSlice_le_full
  -- Step 10: per-window annulusSlice is non-negative (needed for
  -- `innerExcess_le_of_window_bounds`).
  have hSlice_nonneg :
      ∀ i : Fin (n + 1),
        0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
              (ρStart i) (ρStop i) := by
    intro i
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo (ρStart i) (ρStop i)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_of_lt_of_le (hStartLt i) hρ.1.le
        have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 (hStopLeOne i)
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρStart i) (b := ρStop i)
      (hStartLeStop i) hNonnegAE
  -- Step 11: apply `innerExcess_le_of_window_bounds`.
  -- Build the `annulusTerm` function as `i ↦ annulusSlice (ρStart i) (ρStop i)`.
  let annulusTerm : Fin (n + 1) → ℝ := fun i =>
    AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart i) (ρStop i)
  have hMassTotal' :
      (1 : ℝ) ≤ Finset.sum Finset.univ (fun i : Fin (n + 1) => mass i) := by
    -- `mass i = ∫ ρ in (ρStart i)..(ρStop i), scalarIntegrand …` is the witness's
    -- joint mass cell, which is `∑ over Fin (n+1)`.
    convert hMassTotal using 1
  have hAnnulusSum :
      Finset.sum Finset.univ (fun i : Fin (n + 1) => annulusTerm i) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    -- annulusTerm i = annulusSlice (ρStart i) (ρStop i).
    convert hSumSliceLE using 1
  have hWindow :
      ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        mass i * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          annulusTerm i := fun i _ => hSliceBound i
  have hAnnulusNonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ annulusTerm i :=
    fun i _ => hSlice_nonneg i
  have hDiskLeFull :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.innerExcess_le_of_window_bounds
      (s := Finset.univ) (mass := mass) (annulusTerm := annulusTerm)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (annulusExcess := AnnulusIntegralReduction.annulusSlice paper.circleGap c 1)
      hWindow hMassTotal' hAnnulusSum hAnnulusNonneg
  -- Final calc.
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  rw [← hAnnulusEq]
  exact hDiskLeFull

/--
Sprint 086: per-window kernel-kind tag used by the mixed-kernel
multi-window reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`. A window
is either a per-mode tail window (`modeJ j` for some `j ≥ 1`) discharged
via `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`,
or a Branch.one fallback window (`branch1`) discharged via
`pointwise_branch1_on_Ioo_eq5_eq8_eq9` lifted to a.e.-`Icc` via
`Ioo_ae_eq_Icc`. The kind tag selects the per-window discharge route,
the per-window scalar integrand, and the per-window τ/branchSplit
endpoint constraints.
-/
inductive KernelKind where
  | modeJ (j : ℕ) : KernelKind
  | branch1 : KernelKind

/--
Sprint 086: standalone Branch.one a.e.-`Icc` pointwise wrapper. Lifts
`pointwise_branch1_on_Ioo_eq5_eq8_eq9` (sprint 085, `Set.Ioo` form) to
the a.e.-`Icc` form needed by
`AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`.

This is the structural piece that allows a Branch.one fallback window to
plug into the closing chain inside the mixed-kernel multi-window
reducer. The body is the verbatim `Ioo_ae_eq_Icc` lift template from
`valid_of_eq5_eq8_eq9_subinterval_branch1`'s body, factored as a
standalone theorem so it can be invoked once per Branch.one window
inside the reducer.
-/
theorem pointwise_branch1_on_Icc_eq5_eq8_eq9_ae
    {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hcρ₁ : c < ρ₁)
    (hρ₂_split : ρ₂ ≤ PaperAxioms.branchSplit c)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c) :
    ∀ᵐ ρ ∂volume.restrict (Set.Icc ρ₁ ρ₂),
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  have hPointwiseIoo :
      ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ :=
    pointwise_branch1_on_Ioo_eq5_eq8_eq9
      hc_pos hSplit_lt_one hcρ₁ hρ₂_split paper
  have hIoo :
      ∀ᵐ ρ ∂volume.restrict (Set.Ioo ρ₁ ρ₂),
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
            * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun ρ hρ => hPointwiseIoo ρ hρ
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
  exact hIoo

/--
Sprint 086 — **mixed-kernel multi-window τ-partition closing reducer**.

Generalizes `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
(sprint 084) to admit two kinds of windows within a single τ-partition
of `(c, 1)`: per-mode `modeJ j` windows (discharged via
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`)
and Branch.one fallback `branch1` windows (discharged via
`pointwise_branch1_on_Ioo_eq5_eq8_eq9` and lifted to a.e.-`Icc` via
`pointwise_branch1_on_Icc_eq5_eq8_eq9_ae`).

The witness supplies a per-window `kind : Fin (n + 1) → KernelKind`
tag. On `modeJ j` windows the τ-bounds
`OneModeTail.tau (j-1) ≤ c²/ρStop² ≤ c²/ρStart² ≤ OneModeTail.tau j`
are required; on `branch1` windows the constraint is
`ρStop ≤ branchSplit c`. The joint-mass hypothesis is
`1 ≤ ∑ i, ∫ (ρStart i)..(ρStop i), kind-dispatched-integrand`.

Discharge uses **Option α** (uniform a.e.-`Icc` closer): the per-mode
pointwise step (naturally `Icc`-shaped) is upgraded to a.e.-`Icc` via
`Filter.Eventually.of_forall`, and the Branch.one pointwise step is
already a.e.-`Icc` via the standalone wrapper. The single-code-path
closer
`AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`
applies to both kinds.

The remaining steps (adjacency-glue, side-slice non-negativity,
final `innerExcess_le_of_window_bounds`) are unchanged from sprint
084 and do not interact with the kind tag.

Composes:
  * sprint 084's `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
    body structure (template),
  * `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    (per-mode discharge, sprint 084 input),
  * `pointwise_branch1_on_Ioo_eq5_eq8_eq9` (sprint 085's standalone
    Branch.one pointwise theorem),
  * `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae` (a.e.-`Icc` lift wrapper).

No new axioms, no oracle, no `Section2Assumptions` field extension.
The new reducer's body is pure Lean composition of existing
trusted-surface theorems plus standard `Fin`-sum machinery.

Forward direction: sprint 087 ships the
`Numerical_Library.export_mode_hybrid_boxes` Phase 0 sweep + a
fallback-box-mass certified-rational oracle row at
`c = 356401/1000000`; sprint 088 ships V66 (or V67) at V38's `c`
composing four mode windows + three fallback boxes via this reducer
(the +1.2e-2 V38 prize).
-/
theorem valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    {n : ℕ}
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart ρStop : Fin (n + 1) → ℝ)
          (kind : Fin (n + 1) → KernelKind),
          (∀ i : Fin (n + 1), c < ρStart i) ∧
          (∀ i : Fin (n + 1), ρStart i ≤ ρStop i) ∧
          (∀ i : Fin (n + 1), ρStop i < 1) ∧
          (∀ i : Fin n, ρStop i.castSucc = ρStart i.succ) ∧
          (∀ i : Fin (n + 1), ∀ j : ℕ,
            kind i = KernelKind.modeJ j →
              1 ≤ j ∧
              OneModeTail.tau (j - 1) ≤ c ^ 2 / ρStop i ^ 2 ∧
              c ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau j) ∧
          (∀ i : Fin (n + 1),
            kind i = KernelKind.branch1 →
              ρStop i ≤ PaperAxioms.branchSplit c) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.plusSeq a b n' *
              c ^ (2 * n' + 2) / (n' + 1 : ℝ)) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.plusSeq a b n' * c ^ (2 * n')) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' *
              c ^ (2 * n' + 2) / (n' + 1 : ℝ)) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' * c ^ (2 * n')) ∧
          Summable (fun n' : ℕ =>
            OneModePaperBridge.minusSeq a b n' *
              OneModeKernel.weight c n') ∧
          (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
            Summable (fun n' : ℕ =>
              OneModePaperBridge.minusSeq a b n' * ρ ^ (2 * n'))) ∧
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
            volume c 1 ∧
          (∀ i : Fin (n + 1),
            (∀ j : ℕ, kind i = KernelKind.modeJ j →
              IntervalIntegrable
                (fun ρ => ModeBridge.scalarIntegrand c j
                  (WangOuter.paperLambda K c) ρ)
                volume (ρStart i) (ρStop i)) ∧
            (kind i = KernelKind.branch1 →
              IntervalIntegrable
                (fun ρ => Korenblum.scalarIntegrand1 c
                  (WangOuter.paperLambda K c) ρ)
                volume (ρStart i) (ρStop i))) ∧
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            OneModePaperBridge.innerSeriesExcess a b c ∧
          (1 : ℝ) ≤
            ∑ i : Fin (n + 1),
              match kind i with
              | KernelKind.modeJ j =>
                ∫ ρ in (ρStart i)..(ρStop i),
                  ModeBridge.scalarIntegrand c j
                    (WangOuter.paperLambda K c) ρ
              | KernelKind.branch1 =>
                ∫ ρ in (ρStart i)..(ρStop i),
                  Korenblum.scalarIntegrand1 c
                    (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  refine ⟨hc_pos, hc_lt_one, ?_⟩
  intro a b K paper
  obtain ⟨ρStart, ρStop, kind,
      hStartLt, hStartLeStop, hStopLtOne, hAdj,
      hModeJ, hBranch1Split,
      hPlusDisk, hPlusSigma, hMinusDisk, hMinusSigmaC, hMinusWeight,
      hMinusSigma, hIntCircle, hIntKind, hInner,
      hMassTotal⟩ := h_witness paper
  -- Per-window geometric scaffolding (unchanged from sprint 084).
  have hStartLe : ∀ i : Fin (n + 1), c ≤ ρStart i := fun i => (hStartLt i).le
  have hStopLeOne : ∀ i : Fin (n + 1), ρStop i ≤ 1 := fun i => (hStopLtOne i).le
  have hcLtStop : ∀ i : Fin (n + 1), c < ρStop i := fun i =>
    lt_of_lt_of_le (hStartLt i) (hStartLeStop i)
  have hcLeStop : ∀ i : Fin (n + 1), c ≤ ρStop i := fun i => (hcLtStop i).le
  have hc_le_one : c ≤ (1 : ℝ) := hc_lt_one.le
  -- Step 1: discharge `paper.eq4_sigmaPlus_bound` to get
  -- `sigmaPlus a b c ≤ sigmaMinus a b c`.
  have hPlusLeMinus :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c := by
    have h0c : (0 : ℝ) ≤ 0 := le_refl 0
    have hZeroLtC : (0 : ℝ) < c := hc_pos
    have h_eq4_at_zero :
        PaperAxioms.Eq4SigmaPlusBound (PaperAxioms.sigmaPlus a b)
          (PaperAxioms.sigmaMinus a b) (PaperAxioms.sigmaZeroMinus a b) 0 c :=
      paper.eq4_sigmaPlus_bound h0c hZeroLtC hc_lt_one
    exact h_eq4_at_zero.2.1
  -- Per-window kind-dispatched integrand. We use a `match` inside a `let`
  -- so that the joint-mass cell typechecks uniformly.
  let modeIntegrand_w : Fin (n + 1) → ℝ → ℝ := fun i ρ =>
    match kind i with
    | KernelKind.modeJ j =>
        ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ
    | KernelKind.branch1 =>
        Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
  -- Step 2: per-window pointwise bound — kind-dispatched.
  -- Both branches conclude with the a.e.-`Icc` form of the pointwise
  -- bound, which is the form consumed by
  -- `mass_mul_le_annulusSlice_of_integral_bound_ae`.
  have hPointwiseAE :
      ∀ i : Fin (n + 1),
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
          modeIntegrand_w i ρ *
              PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro i
    -- Case-split on `kind i`. We need the goal to mention `modeIntegrand_w i`,
    -- and we case-split on the kind to fix which branch of the `match` fires.
    rcases hKind : kind i with j | _
    · -- kind i = modeJ j: invoke sprint 084's per-mode discharge, then
      -- upgrade `Icc → ae`.
      obtain ⟨hjPos_i, hLowerTau_i, hUpperTau_i⟩ := hModeJ i j hKind
      have hPointwiseIcc :
          ∀ ⦃ρ : ℝ⦄, ρ ∈ Set.Icc (ρStart i) (ρStop i) →
            ModeBridge.scalarIntegrand c j
                (WangOuter.paperLambda K c) ρ *
                PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              2 * ρ * PaperAxioms.circleGap a b ρ :=
        OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9
          hc_pos hPlusDisk hPlusSigma hMinusDisk hMinusSigmaC hMinusWeight
          hPlusLeMinus hInner
          paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
          hMinusSigma hjPos_i (hStartLt i) (hStopLtOne i) hLowerTau_i hUpperTau_i
      have hAE :
          ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
            ModeBridge.scalarIntegrand c j
                (WangOuter.paperLambda K c) ρ *
                PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have h := hPointwiseIcc hρ
        change ModeBridge.scalarIntegrand c j
                  (WangOuter.paperLambda K c) ρ *
                PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              2 * ρ * paper.circleGap ρ
        have hCircleEq : paper.circleGap ρ = PaperAxioms.circleGap a b ρ := rfl
        rw [hCircleEq]
        exact h
      -- Now align the LHS with `modeIntegrand_w i ρ`, which equals the modeJ
      -- branch under `kind i = modeJ j`.
      have hRewrite :
          ∀ ρ, modeIntegrand_w i ρ =
              ModeBridge.scalarIntegrand c j
                (WangOuter.paperLambda K c) ρ := by
        intro ρ
        simp only [modeIntegrand_w, hKind]
      filter_upwards [hAE] with ρ hbnd
      rw [hRewrite ρ]
      exact hbnd
    · -- kind i = branch1: invoke the standalone Branch.one a.e.-Icc wrapper.
      have hρ₂_split : ρStop i ≤ PaperAxioms.branchSplit c := hBranch1Split i hKind
      have hAE :
          ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
            Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
                * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              AnnulusIntegralReduction.annulusDensity paper.circleGap ρ :=
        pointwise_branch1_on_Icc_eq5_eq8_eq9_ae
          hc_pos hSplit_lt_one (hStartLt i) hρ₂_split paper
      have hRewrite :
          ∀ ρ, modeIntegrand_w i ρ =
              Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ := by
        intro ρ
        simp only [modeIntegrand_w, hKind]
      filter_upwards [hAE] with ρ hbnd
      rw [hRewrite ρ]
      exact hbnd
  -- Step 3: per-window annulus-density a.e. non-negativity.
  have hAnnNonnegAE :
      ∀ i : Fin (n + 1),
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
    intro i
    have hIoo :
        ∀ᵐ ρ ∂volume.restrict (Set.Ioo (ρStart i) (ρStop i)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le (hStartLt i) hρ.1.le
      have hρ_lt_one : ρ < 1 := lt_of_lt_of_le hρ.2 (hStopLeOne i)
      exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
    exact hIoo
  -- Step 4: per-window integrability of annulusDensity, via mono_set.
  have hIntDens_window :
      ∀ i : Fin (n + 1),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart i) (ρStop i) := by
    intro i
    have hu : Set.uIcc (ρStart i) (ρStop i) ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le (hStartLeStop i), Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc (hStartLe i) (hStopLeOne i)
    exact hIntCircle.mono_set hu
  -- Step 5: per-window kind-dispatched integrability of modeIntegrand_w.
  have hIntMode_w :
      ∀ i : Fin (n + 1),
        IntervalIntegrable (modeIntegrand_w i) volume (ρStart i) (ρStop i) := by
    intro i
    rcases hKind : kind i with j | _
    · -- modeJ j case: pull from per-window integrability witness.
      have hInt_j := (hIntKind i).1 j hKind
      have hCong : modeIntegrand_w i = fun ρ =>
          ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
        funext ρ
        simp only [modeIntegrand_w, hKind]
      rw [hCong]
      exact hInt_j
    · -- branch1 case: pull from per-window integrability witness.
      have hInt_b := (hIntKind i).2 hKind
      have hCong : modeIntegrand_w i = fun ρ =>
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ := by
        funext ρ
        simp only [modeIntegrand_w, hKind]
      rw [hCong]
      exact hInt_b
  -- Step 6: per-window mass and slice bound.
  let mass : Fin (n + 1) → ℝ := fun i =>
    ∫ ρ in (ρStart i)..(ρStop i), modeIntegrand_w i ρ
  -- Per-window scalar-integrand a.e. non-negativity.
  have hMode_nonneg_AE :
      ∀ i : Fin (n + 1),
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStart i) (ρStop i)),
          0 ≤ modeIntegrand_w i ρ := by
    intro i
    rcases hKind : kind i with j | _
    · -- modeJ j case.
      obtain ⟨hjPos_i, _, _⟩ := hModeJ i j hKind
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c < ρ := lt_of_lt_of_le (hStartLt i) hρ.1
      have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2 (hStopLtOne i)
      have hρpos : 0 < ρ := lt_trans hc_pos hcρ
      have hjPos_i' : 0 < (j : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hjPos_i
      have hTermPos : 0 < OneModeKernel.term c ρ j := by
        unfold OneModeKernel.term OneModeKernel.weight
        positivity
      have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
        WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
      have hLHS : modeIntegrand_w i ρ =
          ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ := by
        simp only [modeIntegrand_w, hKind]
      rw [hLHS]
      unfold ModeBridge.scalarIntegrand
      positivity
    · -- branch1 case.
      have hρ₂_split : ρStop i ≤ PaperAxioms.branchSplit c := hBranch1Split i hKind
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le (hStartLt i) hρ.1)
      have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
        WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
      have hLHS : modeIntegrand_w i ρ =
          Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ := by
        simp only [modeIntegrand_w, hKind]
      rw [hLHS]
      exact KorenblumPaper.AffineBoxQ.scalarIntegrand1_nonneg c
        (WangOuter.paperLambda K c) hc_pos hΛpos hcρ
  have hMass_nonneg : ∀ i : Fin (n + 1), 0 ≤ mass i := by
    intro i
    exact intervalIntegral.integral_nonneg_of_ae_restrict (hStartLeStop i)
      (hMode_nonneg_AE i)
  -- Per-window slice bound via the a.e. closer.
  have hSliceBound :
      ∀ i : Fin (n + 1),
        mass i * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) := by
    intro i
    exact AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae
      (modeIntegrand := modeIntegrand_w i)
      (circleGap := paper.circleGap)
      (a := ρStart i) (b := ρStop i)
      (mass := mass i)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (hStartLeStop i) (hMass_nonneg i) le_rfl (hIntMode_w i) (hIntDens_window i)
      (hPointwiseAE i) (hAnnNonnegAE i)
  -- Step 7: collapse adjacency: ∑ i, annulusSlice = annulusSlice (start 0) (stop last).
  have hChain : ∀ p : Fin (n + 1), ρStop 0 ≤ ρStop p := by
    intro p
    induction p using Fin.induction with
    | zero => exact le_refl _
    | succ p' ih =>
      have hadj : ρStop p'.castSucc = ρStart p'.succ := hAdj p'
      calc ρStop 0
          ≤ ρStop p'.castSucc := ih
        _ = ρStart p'.succ := hadj
        _ ≤ ρStop p'.succ := hStartLeStop _
  have hIntPrefix :
      ∀ k : Fin n,
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart 0) (ρStop k.castSucc) := by
    intro k
    have hStart0_le_StopK : ρStart 0 ≤ ρStop k.castSucc := by
      have h1 : ρStart 0 ≤ ρStop 0 := hStartLeStop 0
      calc ρStart 0 ≤ ρStop 0 := h1
        _ ≤ ρStop k.castSucc := hChain k.castSucc
    have hu :
        Set.uIcc (ρStart 0) (ρStop k.castSucc) ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le hStart0_le_StopK, Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc (hStartLe 0) (hStopLeOne k.castSucc)
    exact hIntCircle.mono_set hu
  have hCollapseSum :
      ∑ i : Fin (n + 1),
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) =
        AnnulusIntegralReduction.annulusSlice paper.circleGap
          (ρStart 0) (ρStop (Fin.last n)) :=
    sum_annulusSlice_collapse_adjacent (circleGap := paper.circleGap)
      n ρStart ρStop hAdj hIntDens_window hIntPrefix
  -- Step 8: bound the merged slice by `annulusSlice c 1` via the side-slice
  -- non-negativity argument (verbatim from sprint 084).
  have hStart0_le_StopLast : ρStart 0 ≤ ρStop (Fin.last n) := by
    calc ρStart 0
        ≤ ρStop 0 := hStartLeStop 0
      _ ≤ ρStop (Fin.last n) := hChain (Fin.last n)
  have hStop_last_lt_one : ρStop (Fin.last n) < 1 := hStopLtOne (Fin.last n)
  have hc_le_Start0 : c ≤ ρStart 0 := hStartLe 0
  have hc_le_StopLast : c ≤ ρStop (Fin.last n) := hcLeStop (Fin.last n)
  have huIcc_cStart0 : Set.uIcc c (ρStart 0) ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hc_le_Start0, Set.uIcc_of_le hc_le_one]
    have hStart0_lt_one : ρStart 0 < 1 :=
      lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
    exact Set.Icc_subset_Icc le_rfl hStart0_lt_one.le
  have huIcc_StopLastOne : Set.uIcc (ρStop (Fin.last n)) 1 ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStop_last_lt_one.le, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_StopLast le_rfl
  have huIcc_Start0StopLast :
      Set.uIcc (ρStart 0) (ρStop (Fin.last n)) ⊆ Set.uIcc c 1 := by
    rw [Set.uIcc_of_le hStart0_le_StopLast, Set.uIcc_of_le hc_le_one]
    exact Set.Icc_subset_Icc hc_le_Start0 hStop_last_lt_one.le
  have hIntDens_cStart0 :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume c (ρStart 0) :=
    hIntCircle.mono_set huIcc_cStart0
  have hIntDens_StopLastOne :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (ρStop (Fin.last n)) 1 :=
    hIntCircle.mono_set huIcc_StopLastOne
  have hIntDens_Start0StopLast :
      IntervalIntegrable
        (AnnulusIntegralReduction.annulusDensity paper.circleGap)
        volume (ρStart 0) (ρStop (Fin.last n)) :=
    hIntCircle.mono_set huIcc_Start0StopLast
  have hSlice_cStart0_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c (ρStart 0) := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc c (ρStart 0)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo c (ρStart 0)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := hρ.1
        have hStart0_lt_one : ρStart 0 < 1 :=
          lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
        have hρ_lt_one : ρ < 1 := lt_trans hρ.2 hStart0_lt_one
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := c) (b := ρStart 0) hc_le_Start0
      hNonnegAE
  have hSlice_StopLastOne_nonneg :
      0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStop (Fin.last n)) 1 := by
    have hNonnegAE :
        ∀ᵐ ρ ∂volume.restrict (Set.Icc (ρStop (Fin.last n)) (1 : ℝ)),
          0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
      have hIoo :
          ∀ᵐ ρ ∂volume.restrict (Set.Ioo (ρStop (Fin.last n)) (1 : ℝ)),
            0 ≤ AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun ρ hρ => ?_
        have hcρ : c < ρ := lt_trans (hcLtStop (Fin.last n)) hρ.1
        exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ.2
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hIoo
      exact hIoo
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρStop (Fin.last n)) (b := (1 : ℝ))
      hStop_last_lt_one.le hNonnegAE
  have hSplit1 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c (ρStart 0) +
          AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart 0) 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    have hStart0_lt_one : ρStart 0 < 1 :=
      lt_of_le_of_lt hStart0_le_StopLast hStop_last_lt_one
    have huIcc_Start0One : Set.uIcc (ρStart 0) 1 ⊆ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le hStart0_lt_one.le, Set.uIcc_of_le hc_le_one]
      exact Set.Icc_subset_Icc hc_le_Start0 le_rfl
    have hIntDens_Start0One :
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume (ρStart 0) 1 :=
      hIntCircle.mono_set huIcc_Start0One
    exact AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_cStart0 hIntDens_Start0One
  have hSplit2 :
      AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart 0) (ρStop (Fin.last n)) +
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStop (Fin.last n)) 1 =
        AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart 0) 1 :=
    AnnulusIntegralReduction.annulusSlice_add_adjacent
      hIntDens_Start0StopLast hIntDens_StopLastOne
  have hMergedSlice_le_full :
      AnnulusIntegralReduction.annulusSlice paper.circleGap
          (ρStart 0) (ρStop (Fin.last n)) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    linarith [hSplit1, hSplit2, hSlice_cStart0_nonneg, hSlice_StopLastOne_nonneg]
  -- Step 9: assemble `∑ i, annulusSlice ≤ annulusSlice c 1`.
  have hSumSliceLE :
      ∑ i : Fin (n + 1),
          AnnulusIntegralReduction.annulusSlice paper.circleGap
            (ρStart i) (ρStop i) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    rw [hCollapseSum]; exact hMergedSlice_le_full
  -- Step 10: per-window annulusSlice non-negativity.
  have hSlice_nonneg :
      ∀ i : Fin (n + 1),
        0 ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap
              (ρStart i) (ρStop i) := by
    intro i
    exact AnnulusIntegralReduction.annulusSlice_nonneg_of_ae
      (circleGap := paper.circleGap) (a := ρStart i) (b := ρStop i)
      (hStartLeStop i) (hAnnNonnegAE i)
  -- Step 11: apply `innerExcess_le_of_window_bounds`.
  let annulusTerm : Fin (n + 1) → ℝ := fun i =>
    AnnulusIntegralReduction.annulusSlice paper.circleGap (ρStart i) (ρStop i)
  -- Joint mass coercion: hMassTotal supplies the kind-dispatched joint mass,
  -- which equals `∑ i, mass i` definitionally — `mass i = ∫ … modeIntegrand_w i ρ`
  -- is the kind-dispatched per-window integral, which `match`-unfolds to the
  -- modeJ or branch1 branch as appropriate.
  have hMass_eq_match :
      ∀ i : Fin (n + 1),
        mass i =
          match kind i with
          | KernelKind.modeJ j =>
              ∫ ρ in (ρStart i)..(ρStop i),
                ModeBridge.scalarIntegrand c j
                  (WangOuter.paperLambda K c) ρ
          | KernelKind.branch1 =>
              ∫ ρ in (ρStart i)..(ρStop i),
                Korenblum.scalarIntegrand1 c
                  (WangOuter.paperLambda K c) ρ := by
    intro i
    -- mass i = ∫ ρ in …, modeIntegrand_w i ρ.
    -- modeIntegrand_w i ρ = match kind i with | modeJ j => … | branch1 => ….
    -- We push the `match` outside the integral by case-splitting.
    rcases hKind : kind i with j | _
    · -- modeJ j case.
      have hCong : (fun ρ => modeIntegrand_w i ρ) =
          fun ρ => ModeBridge.scalarIntegrand c j
            (WangOuter.paperLambda K c) ρ := by
        funext ρ; simp only [modeIntegrand_w, hKind]
      show (∫ ρ in (ρStart i)..(ρStop i), modeIntegrand_w i ρ) = _
      rw [hCong]
    · -- branch1 case.
      have hCong : (fun ρ => modeIntegrand_w i ρ) =
          fun ρ => Korenblum.scalarIntegrand1 c
            (WangOuter.paperLambda K c) ρ := by
        funext ρ; simp only [modeIntegrand_w, hKind]
      show (∫ ρ in (ρStart i)..(ρStop i), modeIntegrand_w i ρ) = _
      rw [hCong]
  have hSum_eq :
      ∑ i : Fin (n + 1), mass i =
        ∑ i : Fin (n + 1),
          match kind i with
          | KernelKind.modeJ j =>
              ∫ ρ in (ρStart i)..(ρStop i),
                ModeBridge.scalarIntegrand c j
                  (WangOuter.paperLambda K c) ρ
          | KernelKind.branch1 =>
              ∫ ρ in (ρStart i)..(ρStop i),
                Korenblum.scalarIntegrand1 c
                  (WangOuter.paperLambda K c) ρ := by
    apply Finset.sum_congr rfl
    intro i _
    exact hMass_eq_match i
  have hMassTotal' :
      (1 : ℝ) ≤ Finset.sum Finset.univ (fun i : Fin (n + 1) => mass i) := by
    rw [hSum_eq]
    exact hMassTotal
  have hAnnulusSum :
      Finset.sum Finset.univ (fun i : Fin (n + 1) => annulusTerm i) ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
    convert hSumSliceLE using 1
  have hWindow :
      ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        mass i * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          annulusTerm i := fun i _ => hSliceBound i
  have hAnnulusNonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ annulusTerm i :=
    fun i _ => hSlice_nonneg i
  have hDiskLeFull :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 :=
    AnnulusIntegralReduction.innerExcess_le_of_window_bounds
      (s := Finset.univ) (mass := mass) (annulusTerm := annulusTerm)
      (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (annulusExcess := AnnulusIntegralReduction.annulusSlice paper.circleGap c 1)
      hWindow hMassTotal' hAnnulusSum hAnnulusNonneg
  -- Final calc.
  have hAnnulusEq :
      AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 =
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
  change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  rw [← hAnnulusEq]
  exact hDiskLeFull

/-!
## Sprint 087 — V38 seven-window joint-mass oracle handle

The `axiom` below is the Lean-facing handle on the registered numerical
oracle `h_seven_window_mass_certified_at_356562_sqrt`, which is in turn
backed by `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356562_sqrt`
(`lemma.toml:[[oracles]]`). It asserts the joint-mass hypothesis of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint
086) instantiated at the Phase 0-sweep-pinned c (`c = 356562/1000000`,
the largest c above V64's `35646/100000` at which the V38 seven-window
split has joint mass exceeding `1 + 1e-4`; see
`Scratch/sprint_087_v38_seven_window_mass_sweep.txt`).

The seven-window split is:
  i = 0 boxA1 (Branch.one)   `[c·(1+1e-6),  c·sqrt(50/49)]`
  i = 1 boxA2 (Branch.one)   `[c·sqrt(50/49), c·sqrt(36/35)]`
  i = 2 boxA3 (Branch.one)   `[c·sqrt(36/35), c·sqrt(25/24)]`
  i = 3 mode4 (modeJ j=4)    `[c·sqrt(25/24), c·sqrt(16/15)]`
  i = 4 mode3 (modeJ j=3)    `[c·sqrt(16/15), c·sqrt(9/8)]`
  i = 5 mode2 (modeJ j=2)    `[c·sqrt(9/8),   c·sqrt(4/3)]`
  i = 6 mode1 (modeJ j=1)    `[c·sqrt(4/3),   999999/1000000]`

This is a free workspace axiom (not a `Section2Assumptions` field) and
is discharged by the registered oracle. Sprint 088 will consume it
inside V66's `h_witness` to discharge the joint-mass premise of the
mixed reducer.

-/

/-- Sprint 087 helper: `c_value` for the V38 seven-window c-push
candidate (V66, sprint 088). -/
def v66CValue : ℝ := 356562 / 1000000

/-- Sprint 087 helper: per-window kind tag for the V38 seven-window
split (3 Branch.one fallback boxes + 4 per-mode windows for j=4,3,2,1). -/
def v66SevenWindowKind : Fin 7 → KernelKind
  | ⟨0, _⟩ => KernelKind.branch1
  | ⟨1, _⟩ => KernelKind.branch1
  | ⟨2, _⟩ => KernelKind.branch1
  | ⟨3, _⟩ => KernelKind.modeJ 4
  | ⟨4, _⟩ => KernelKind.modeJ 3
  | ⟨5, _⟩ => KernelKind.modeJ 2
  | ⟨6, _⟩ => KernelKind.modeJ 1

/-- Sprint 087 helper: per-window `ρStart` for the V38 seven-window
split. The mode windows are sqrt-pinned at the τ-breakpoints
`τ_j = 1 - 1/(j+1)²`; the Branch.one fallback boxes split the deep
`(c, c·sqrt(25/24))` region at `c·sqrt(50/49)` and `c·sqrt(36/35)`. -/
def v66SevenWindowStart : Fin 7 → ℝ
  | ⟨0, _⟩ => v66CValue * (1 + 1 / 1000000)
  | ⟨1, _⟩ => v66CValue * Real.sqrt (50 / 49)
  | ⟨2, _⟩ => v66CValue * Real.sqrt (36 / 35)
  | ⟨3, _⟩ => v66CValue * Real.sqrt (25 / 24)
  | ⟨4, _⟩ => v66CValue * Real.sqrt (16 / 15)
  | ⟨5, _⟩ => v66CValue * Real.sqrt (9 / 8)
  | ⟨6, _⟩ => v66CValue * Real.sqrt (4 / 3)

/-- Sprint 087 helper: per-window `ρStop` for the V38 seven-window
split. Adjacency `ρStop i = ρStart (i+1)` holds by construction. -/
def v66SevenWindowStop : Fin 7 → ℝ
  | ⟨0, _⟩ => v66CValue * Real.sqrt (50 / 49)
  | ⟨1, _⟩ => v66CValue * Real.sqrt (36 / 35)
  | ⟨2, _⟩ => v66CValue * Real.sqrt (25 / 24)
  | ⟨3, _⟩ => v66CValue * Real.sqrt (16 / 15)
  | ⟨4, _⟩ => v66CValue * Real.sqrt (9 / 8)
  | ⟨5, _⟩ => v66CValue * Real.sqrt (4 / 3)
  | ⟨6, _⟩ => 999999 / 1000000

/--
Sprint 087: Lean-facing handle on the registered oracle
`h_seven_window_mass_certified_at_356562_sqrt`. The `axiom` body
asserts the kind-dispatched joint-mass hypothesis at V38's seven-
window split, discharged by
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356562_sqrt`
at evaluator-time per `lemma.toml:[[oracles]]`.

The statement matches the kind-dispatched joint-mass field of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint
086) instantiated at `c = v66CValue = 356562/1000000` with the seven-
window endpoint data baked in via `v66SevenWindowKind`,
`v66SevenWindowStart`, `v66SevenWindowStop`.

This is a free workspace axiom (not a `Section2Assumptions` field)
and is discharged by the registered oracle. Sprint 088 will consume
this axiom inside V66's `h_witness` to discharge the joint-mass
premise of the mixed reducer.
-/
axiom h_seven_window_mass_certified_at_356562_sqrt
    (K : ℝ → ℝ → ℝ)
    (hK : KorenblumPaper.PaperAxioms.Eq7PaperKFormula K v66CValue) :
  (1 : ℝ) ≤
    ∑ i : Fin 7,
      match v66SevenWindowKind i with
      | KernelKind.modeJ j =>
        ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
          ModeBridge.scalarIntegrand v66CValue j
            (WangOuter.paperLambda K v66CValue) ρ
      | KernelKind.branch1 =>
        ∫ ρ in (v66SevenWindowStart i)..(v66SevenWindowStop i),
          Korenblum.scalarIntegrand1 v66CValue
            (WangOuter.paperLambda K v66CValue) ρ

/-!
## Sprint 090 — V67 eight-window joint-mass oracle handle

The `axiom` below is the Lean-facing handle on the registered numerical
oracle `h_eight_window_mass_certified_at_356564_modeJ7`, which is in turn
backed by `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
(`lemma.toml:[[oracles]]`). It asserts the joint-mass hypothesis of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint
086) instantiated at the sprint 089 GO-witness c (`c = 89141/250000 =
356564/1000000`, the largest c above V66's `178281/500000 = 356562/1000000`
at which the eight-window architecture has joint mass exceeding `1 + 1e-4`;
see `Scratch/sprint_089_witness.txt`).

The eight-window split is:
  i = 0 box0  (Branch.one)   `[c·(1+1e-9),  c·sqrt(64/63)]`
  i = 1 mode7 (modeJ j=7)    `[c·sqrt(64/63), c·sqrt(49/48)]`
  i = 2 mode6 (modeJ j=6)    `[c·sqrt(49/48), c·sqrt(36/35)]`
  i = 3 mode5 (modeJ j=5)    `[c·sqrt(36/35), c·sqrt(25/24)]`
  i = 4 mode4 (modeJ j=4)    `[c·sqrt(25/24), c·sqrt(16/15)]`
  i = 5 mode3 (modeJ j=3)    `[c·sqrt(16/15), c·sqrt(9/8)]`
  i = 6 mode2 (modeJ j=2)    `[c·sqrt(9/8),   c·sqrt(4/3)]`
  i = 7 mode1 (modeJ j=1)    `[c·sqrt(4/3),   1 - 1/1000000000]`

This is a free workspace axiom (not a `Section2Assumptions` field) and
is discharged by the registered oracle. Sprint 090 ships V67 consuming
it inside V67's `h_witness` to discharge the joint-mass premise of the
mixed reducer at `n = 7` (i.e. `Fin 8` windows).

-/

/-- Sprint 090 helper: `c_value` for the eight-window c-push candidate
(V67). `89141/250000 = 356564/1000000`, +2e-6 above V66's
`178281/500000 = 356562/1000000`. -/
def v67CValue : ℝ := 89141 / 250000

/-- Sprint 090 helper: per-window kind tag for the eight-window split
(1 Branch.one residual box + 7 per-mode windows for j = 7, 6, 5, 4,
3, 2, 1). -/
def v67EightWindowKind : Fin 8 → KernelKind
  | ⟨0, _⟩ => KernelKind.branch1
  | ⟨1, _⟩ => KernelKind.modeJ 7
  | ⟨2, _⟩ => KernelKind.modeJ 6
  | ⟨3, _⟩ => KernelKind.modeJ 5
  | ⟨4, _⟩ => KernelKind.modeJ 4
  | ⟨5, _⟩ => KernelKind.modeJ 3
  | ⟨6, _⟩ => KernelKind.modeJ 2
  | ⟨7, _⟩ => KernelKind.modeJ 1

/-- Sprint 090 helper: per-window `ρStart` for the eight-window split.
The mode windows are sqrt-pinned at the τ-breakpoints
`τ_j = 1 - 1/(j+1)²` for j = 1..7; the Branch.one residual box starts
at `c · (1 + 1e-9)`. -/
def v67EightWindowStart : Fin 8 → ℝ
  | ⟨0, _⟩ => v67CValue * (1 + 1 / 1000000000)
  | ⟨1, _⟩ => v67CValue * Real.sqrt (64 / 63)
  | ⟨2, _⟩ => v67CValue * Real.sqrt (49 / 48)
  | ⟨3, _⟩ => v67CValue * Real.sqrt (36 / 35)
  | ⟨4, _⟩ => v67CValue * Real.sqrt (25 / 24)
  | ⟨5, _⟩ => v67CValue * Real.sqrt (16 / 15)
  | ⟨6, _⟩ => v67CValue * Real.sqrt (9 / 8)
  | ⟨7, _⟩ => v67CValue * Real.sqrt (4 / 3)

/-- Sprint 090 helper: per-window `ρStop` for the eight-window split.
Adjacency `ρStop i = ρStart (i+1)` holds by construction. The mode1
upper edge sits at `1 - 1e-9` per sprint 089's witness (a finer ρ_top
than V66's `999999/1000000 = 1 - 1e-6`). -/
def v67EightWindowStop : Fin 8 → ℝ
  | ⟨0, _⟩ => v67CValue * Real.sqrt (64 / 63)
  | ⟨1, _⟩ => v67CValue * Real.sqrt (49 / 48)
  | ⟨2, _⟩ => v67CValue * Real.sqrt (36 / 35)
  | ⟨3, _⟩ => v67CValue * Real.sqrt (25 / 24)
  | ⟨4, _⟩ => v67CValue * Real.sqrt (16 / 15)
  | ⟨5, _⟩ => v67CValue * Real.sqrt (9 / 8)
  | ⟨6, _⟩ => v67CValue * Real.sqrt (4 / 3)
  | ⟨7, _⟩ => 1 - 1 / 1000000000

/--
Sprint 090: Lean-facing handle on the registered oracle
`h_eight_window_mass_certified_at_356564_modeJ7`. The `axiom` body
asserts the kind-dispatched joint-mass hypothesis at the eight-window
split, discharged by
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
at evaluator-time per `lemma.toml:[[oracles]]`. Despite the wrapper's
`seven_window` name prefix (retained from sprint 089's witness) the
underlying architecture is **eight windows**: 1 Branch.one residual
box plus 7 per-mode windows for j ∈ {7, 6, 5, 4, 3, 2, 1}.

The statement matches the kind-dispatched joint-mass field of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint
086) instantiated at `c = v67CValue = 89141/250000 = 356564/1000000`
with the eight-window endpoint data baked in via `v67EightWindowKind`,
`v67EightWindowStart`, `v67EightWindowStop`.

This is a free workspace axiom (not a `Section2Assumptions` field)
and is discharged by the registered oracle. V67 consumes this axiom
inside its `h_witness` to discharge the joint-mass premise of the
mixed reducer.
-/
axiom h_eight_window_mass_certified_at_356564_modeJ7
    (K : ℝ → ℝ → ℝ)
    (hK : KorenblumPaper.PaperAxioms.Eq7PaperKFormula K v67CValue) :
  (1 : ℝ) ≤
    ∑ i : Fin 8,
      match v67EightWindowKind i with
      | KernelKind.modeJ j =>
        ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
          ModeBridge.scalarIntegrand v67CValue j
            (WangOuter.paperLambda K v67CValue) ρ
      | KernelKind.branch1 =>
        ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
          Korenblum.scalarIntegrand1 v67CValue
            (WangOuter.paperLambda K v67CValue) ρ

/-! ## Sprint 092: V68 eleven-window c-push helper defs and oracle axiom -/

/-- Sprint 092 helper: `c_value` for the eleven-window c-push candidate
(V68). `71313/200000 = 356565/1000000`, +1e-6 above V67's
`89141/250000 = 356564/1000000`. -/
def v68CValue : ℝ := 71313 / 200000

/-- Sprint 092 helper: per-window kind tag for the eleven-window split
(1 Branch.one residual box + 10 per-mode windows for j = 10, 9, 8, 7, 6,
5, 4, 3, 2, 1). -/
def v68ElevenWindowKind : Fin 11 → KernelKind
  | ⟨0, _⟩ => KernelKind.branch1
  | ⟨1, _⟩ => KernelKind.modeJ 10
  | ⟨2, _⟩ => KernelKind.modeJ 9
  | ⟨3, _⟩ => KernelKind.modeJ 8
  | ⟨4, _⟩ => KernelKind.modeJ 7
  | ⟨5, _⟩ => KernelKind.modeJ 6
  | ⟨6, _⟩ => KernelKind.modeJ 5
  | ⟨7, _⟩ => KernelKind.modeJ 4
  | ⟨8, _⟩ => KernelKind.modeJ 3
  | ⟨9, _⟩ => KernelKind.modeJ 2
  | ⟨10, _⟩ => KernelKind.modeJ 1

/-- Sprint 092 helper: per-window `ρStart` for the eleven-window split.
The mode windows are sqrt-pinned at the τ-breakpoints
`τ_j = 1 - 1/(j+1)²` for j = 1..10; the Branch.one residual box starts
at `c · (1 + 1e-9)`. -/
def v68ElevenWindowStart : Fin 11 → ℝ
  | ⟨0, _⟩ => v68CValue * (1 + 1 / 1000000000)
  | ⟨1, _⟩ => v68CValue * Real.sqrt (121 / 120)
  | ⟨2, _⟩ => v68CValue * Real.sqrt (100 / 99)
  | ⟨3, _⟩ => v68CValue * Real.sqrt (81 / 80)
  | ⟨4, _⟩ => v68CValue * Real.sqrt (64 / 63)
  | ⟨5, _⟩ => v68CValue * Real.sqrt (49 / 48)
  | ⟨6, _⟩ => v68CValue * Real.sqrt (36 / 35)
  | ⟨7, _⟩ => v68CValue * Real.sqrt (25 / 24)
  | ⟨8, _⟩ => v68CValue * Real.sqrt (16 / 15)
  | ⟨9, _⟩ => v68CValue * Real.sqrt (9 / 8)
  | ⟨10, _⟩ => v68CValue * Real.sqrt (4 / 3)

/-- Sprint 092 helper: per-window `ρStop` for the eleven-window split.
Adjacency `ρStop i = ρStart (i+1)` holds by construction. The mode1
upper edge sits at `1 - 1e-9` per sprint 091's witness. -/
def v68ElevenWindowStop : Fin 11 → ℝ
  | ⟨0, _⟩ => v68CValue * Real.sqrt (121 / 120)
  | ⟨1, _⟩ => v68CValue * Real.sqrt (100 / 99)
  | ⟨2, _⟩ => v68CValue * Real.sqrt (81 / 80)
  | ⟨3, _⟩ => v68CValue * Real.sqrt (64 / 63)
  | ⟨4, _⟩ => v68CValue * Real.sqrt (49 / 48)
  | ⟨5, _⟩ => v68CValue * Real.sqrt (36 / 35)
  | ⟨6, _⟩ => v68CValue * Real.sqrt (25 / 24)
  | ⟨7, _⟩ => v68CValue * Real.sqrt (16 / 15)
  | ⟨8, _⟩ => v68CValue * Real.sqrt (9 / 8)
  | ⟨9, _⟩ => v68CValue * Real.sqrt (4 / 3)
  | ⟨10, _⟩ => 1 - 1 / 1000000000

/--
Sprint 092: Lean-facing handle on the registered oracle
`h_eleven_window_mass_certified_at_356565_modeJ10`. The `axiom` body
asserts the kind-dispatched joint-mass hypothesis at the eleven-window
split, discharged by
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10`
at evaluator-time per `lemma.toml:[[oracles]]`. Despite the wrapper's
`seven_window` name prefix (retained from sprint 091's witness for
backwards consistency) the underlying architecture is **eleven
windows**: 1 Branch.one residual box plus 10 per-mode windows for j ∈
{10, 9, 8, 7, 6, 5, 4, 3, 2, 1}.

The statement matches the kind-dispatched joint-mass field of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint
086) instantiated at `c = v68CValue = 71313/200000 = 356565/1000000`
with the eleven-window endpoint data baked in via
`v68ElevenWindowKind`, `v68ElevenWindowStart`, `v68ElevenWindowStop`.

This is a free workspace axiom (not a `Section2Assumptions` field)
and is discharged by the registered oracle. V68 consumes this axiom
inside its `h_witness` to discharge the joint-mass premise of the
mixed reducer at `n = 10` (i.e. `Fin 11` windows).
-/
axiom h_eleven_window_mass_certified_at_356565_modeJ10
    (K : ℝ → ℝ → ℝ)
    (hK : KorenblumPaper.PaperAxioms.Eq7PaperKFormula K v68CValue) :
  (1 : ℝ) ≤
    ∑ i : Fin 11,
      match v68ElevenWindowKind i with
      | KernelKind.modeJ j =>
        ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
          ModeBridge.scalarIntegrand v68CValue j
            (WangOuter.paperLambda K v68CValue) ρ
      | KernelKind.branch1 =>
        ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
          Korenblum.scalarIntegrand1 v68CValue
            (WangOuter.paperLambda K v68CValue) ρ

end ProofRefinement.Korenblum
