from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

if __package__ in {None, ""}:
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from Numerical_Library.rigorous_scalar import build_adaptive_certificate
else:
    from .rigorous_scalar import build_adaptive_certificate


WORKSPACE = Path(__file__).resolve().parents[1]


def _namespace(version: int) -> str:
    return f"KorenblumPaper.V{version}"


def _box_name(branch: int, i: int) -> str:
    return f"branch{branch}_box_{i:04d}"


def _emit_box(name: str, box) -> str:
    if box.beta.to_fraction() != 0:
        raise ValueError(f"{name} is not a constant-box certificate")
    return (
        f"def {name} : ConstantBoxQ := "
        f"{{ lo := {box.lo.to_lean()}, hi := {box.hi.to_lean()}, "
        f"alpha := {box.alpha.to_lean()}, lambdaUpper := {box.lambda_upper.to_lean()} }}\n"
    )


def _emit_box_list(name: str, box_names: list[str]) -> str:
    joined = ",\n  ".join(box_names)
    return f"def {name} : List ConstantBoxQ := [\n  {joined}\n]\n"


def render_candidate(version: int, cert) -> str:
    total_fraction = cert.total_mass_lower.to_fraction()
    if total_fraction < 1:
        raise ValueError(
            f"candidate totalBoxMass={float(total_fraction):.12f} is below 1; "
            "refusing to emit a false Lean theorem"
        )

    ns = _namespace(version)
    branch1 = [box for box in cert.boxes if box.branch == 1]
    branch2 = [box for box in cert.boxes if box.branch == 2]
    branch1_names = [_box_name(1, i) for i in range(len(branch1))]
    branch2_names = [_box_name(2, i) for i in range(len(branch2))]
    box_defs = "".join(
        _emit_box(name, box)
        for name, box in list(zip(branch1_names, branch1)) + list(zip(branch2_names, branch2))
    )

    return f'''import KorenblumPaper

open MeasureTheory
open Korenblum
open KorenblumPaper

noncomputable section

namespace {ns}

/-!
# Candidate v{version}: constant-box certificate at c = {cert.target_c.to_lean()}

This candidate leaves only the boxwise `Lambda` upper bounds outside Lean.
Lean checks:
- the exact box integrals,
- the exact rational total,
- the reciprocal step from `Lambda(rho) <= lambdaUpper`,
- and the finite-sum lower bound to Wang's scalar criterion.
-/

def cValueQ : ℚ := {cert.target_c.to_lean()}
def cValue : ℝ := cValueQ

def splitLoQ : ℚ := {cert.split_lo.to_lean()}
def splitHiQ : ℚ := {cert.split_hi.to_lean()}
def oneCutQ : ℚ := {cert.one_cut.to_lean()}

{box_defs}
{_emit_box_list("branch1Boxes", branch1_names)}
{_emit_box_list("branch2Boxes", branch2_names)}

def totalBoxMassQ : ℚ :=
  ConstantBoxQ.totalMassQ .one cValueQ branch1Boxes +
  ConstantBoxQ.totalMassQ .two cValueQ branch2Boxes

def totalBoxMass : ℝ := totalBoxMassQ

theorem cValue_pos : 0 < (cValueQ : ℝ) := by
  norm_num [cValueQ]

theorem cValue_lt_one : (cValueQ : ℝ) < 1 := by
  norm_num [cValueQ]

theorem splitLo_ge_c : cValueQ ≤ splitLoQ := by
  native_decide

theorem splitLo_sq : 3 * splitLoQ ^ 2 ≤ 4 * cValueQ ^ 2 := by
  native_decide

theorem splitHi_nonneg : 0 ≤ (splitHiQ : ℝ) := by
  norm_num [splitHiQ]

theorem splitHi_sq : 4 * cValueQ ^ 2 ≤ 3 * splitHiQ ^ 2 := by
  native_decide

theorem splitHi_le_oneCut : splitHiQ ≤ oneCutQ := by
  native_decide

theorem oneCut_le_one : oneCutQ ≤ 1 := by
  native_decide

theorem branch1Boxes_ordered : ConstantBoxQ.OrderedFrom cValueQ branch1Boxes := by
  native_decide

theorem branch1Boxes_hi_le : ∀ box ∈ branch1Boxes, box.hi ≤ splitLoQ := by
  native_decide

theorem branch1Boxes_valid : ConstantBoxQ.Valid branch1Boxes := by
  native_decide

theorem branch2Boxes_ordered : ConstantBoxQ.OrderedFrom splitHiQ branch2Boxes := by
  native_decide

theorem branch2Boxes_hi_le : ∀ box ∈ branch2Boxes, box.hi ≤ oneCutQ := by
  native_decide

theorem branch2Boxes_valid : ConstantBoxQ.Valid branch2Boxes := by
  native_decide

theorem totalBoxMassQ_ge_one : (1 : ℚ) ≤ totalBoxMassQ := by
  native_decide

theorem totalBoxMass_ge_one : (1 : ℝ) ≤ totalBoxMass := by
  simpa [totalBoxMass] using
    (show ((1 : ℚ) : ℝ) ≤ (totalBoxMassQ : ℚ) from by
      exact_mod_cast totalBoxMassQ_ge_one)

theorem scalarCriterion_ge_one
    {{Λ : ℝ → ℝ}}
    (hΛpos : ∀ ρ ∈ Set.Icc (cValueQ : ℝ) 1, 0 < Λ ρ)
    (hInt1 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (cValueQ : ℝ) Λ ρ)
      volume (cValueQ : ℝ) (AffineBoxQ.branchEndR cValueQ Branch.one))
    (hInt2 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (cValueQ : ℝ) Λ ρ)
      volume (AffineBoxQ.branchEndR cValueQ Branch.one) 1)
    (hUpper1 : ConstantBoxQ.UpperHolds branch1Boxes Λ)
    (hUpper2 : ConstantBoxQ.UpperHolds branch2Boxes Λ) :
    1 ≤ Korenblum.scalarCriterion (cValueQ : ℝ) Λ := by
  have hMass : (totalBoxMassQ : ℝ) ≤ Korenblum.scalarCriterion (cValueQ : ℝ) Λ := by
    simpa [totalBoxMassQ] using
      (ConstantBoxQ.totalMassQ_pair_le_scalarCriterion
        cValueQ splitLoQ splitHiQ oneCutQ branch1Boxes branch2Boxes Λ
        cValue_pos cValue_lt_one splitLo_ge_c splitLo_sq splitHi_nonneg splitHi_sq
        splitHi_le_oneCut oneCut_le_one branch1Boxes_ordered branch1Boxes_hi_le
        branch2Boxes_ordered branch2Boxes_hi_le branch1Boxes_valid branch2Boxes_valid
        hUpper1 hUpper2 hΛpos hInt1 hInt2)
  calc
    (1 : ℝ) ≤ totalBoxMass := totalBoxMass_ge_one
    _ = (totalBoxMassQ : ℝ) := rfl
    _ ≤ Korenblum.scalarCriterion (cValueQ : ℝ) Λ := hMass

/-- Main searchable reduction theorem for the target radius. -/
theorem korenblum_target_reduction
    {{innerExcess annulusExcess : ℝ}}
    {{Λ : ℝ → ℝ}}
    (hPaper : 1 ≤ Korenblum.scalarCriterion (cValueQ : ℝ) Λ → innerExcess ≤ annulusExcess)
    (hΛpos : ∀ ρ ∈ Set.Icc (cValueQ : ℝ) 1, 0 < Λ ρ)
    (hInt1 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 (cValueQ : ℝ) Λ ρ)
      volume (cValueQ : ℝ) (AffineBoxQ.branchEndR cValueQ Branch.one))
    (hInt2 : IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 (cValueQ : ℝ) Λ ρ)
      volume (AffineBoxQ.branchEndR cValueQ Branch.one) 1)
    (hUpper1 : ConstantBoxQ.UpperHolds branch1Boxes Λ)
    (hUpper2 : ConstantBoxQ.UpperHolds branch2Boxes Λ) :
    innerExcess ≤ annulusExcess := by
  apply hPaper
  exact scalarCriterion_ge_one hΛpos hInt1 hInt2 hUpper1 hUpper2

end {ns}
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--version", type=int, default=0)
    parser.add_argument("--c-num", type=int, default=713)
    parser.add_argument("--c-den", type=int, default=2000)
    parser.add_argument("--branch1-count", type=int, default=32)
    parser.add_argument("--branch2-count", type=int, default=768)
    parser.add_argument("--max-boxes", type=int, default=2500)
    parser.add_argument("--n-terms", type=int, default=80)
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()

    cert = build_adaptive_certificate(
        Fraction(args.c_num, args.c_den),
        branch1_count=args.branch1_count,
        branch2_count=args.branch2_count,
        max_boxes=args.max_boxes,
        n_terms=args.n_terms,
        dps=args.dps,
    )
    out_dir = WORKSPACE / "candidates"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"candidate_v{args.version}.lean"
    out_path.write_text(render_candidate(args.version, cert))
    print(f"wrote {out_path}")
    print(f"boxes={len(cert.boxes)} total={float(cert.total_mass_lower.to_fraction()):.12f}")


if __name__ == "__main__":
    main()
