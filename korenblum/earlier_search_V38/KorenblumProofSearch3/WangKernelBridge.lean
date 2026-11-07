import KorenblumProofSearch3.WangKernelExact

open MeasureTheory Set

noncomputable section

namespace KorenblumProofSearch3

namespace WangBoxQ

theorem kSqUpperHolds_of_boxKernelValid
    {K : ℝ → ℝ → ℝ}
    {c start stop : ℚ}
    {boxes : List WangBoxQ}
    (hPaper : WangKernelExact.PaperKFormula K (c : ℝ))
    (hc : 0 < (c : ℝ))
    (hc1 : (c : ℝ) < 1)
    (hCStart : c ≤ start)
    (hOrd : OrderedFrom start boxes)
    (hHi : ∀ box ∈ boxes, box.hi ≤ stop)
    (hStop : stop ≤ 1)
    (hKernel : ∀ box ∈ boxes, WangKernelExact.boxKernelValidQ c box.lo box.hi box.kSqUpper) :
    KSqUpperHolds K c boxes := by
  intro box hMem ρ hρ
  have hclo : c ≤ box.lo := le_trans hCStart (OrderedFrom.start_le_lo_of_mem hOrd hMem)
  have hhi1 : box.hi ≤ 1 := le_trans (hHi box hMem) hStop
  exact WangKernelExact.paperKsq_le_of_boxKernelValidQ
    hPaper hc hc1 hclo hhi1 hρ WangKernelExact.defaultTerms (hKernel box hMem)

end WangBoxQ

end KorenblumProofSearch3
