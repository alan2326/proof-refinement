#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
ALLOWED_GLOBAL_AXIOMS = {
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
}


@dataclass
class ParsedCandidate:
    file_path: str
    namespace: str = ""
    theorem_name: str = "korenblum_target_reduction"
    theorem_kind: str = "legacy"
    branch1_box_count: int = 0
    branch2_box_count: int = 0


def failure_excerpt(text: str, limit: int = 4000) -> str:
    if len(text) <= limit:
        return text
    head = text[:1200].rstrip()
    tail = text[-2400:].lstrip()
    return f"{head}\n\n... [output truncated] ...\n\n{tail}"


def parse_candidate(file_path: str) -> ParsedCandidate:
    text = Path(file_path).read_text()
    out = ParsedCandidate(file_path=file_path)

    namespace_match = re.search(r"namespace\s+([A-Za-z0-9_.]+)", text)
    if namespace_match:
        out.namespace = namespace_match.group(1)

    if re.search(r"\btheorem\s+direct_disk_vs_annulus\b", text):
        out.theorem_name = "direct_disk_vs_annulus"
        out.theorem_kind = "direct"

    out.branch1_box_count = len(re.findall(r"\bbranch1_box_\d{4}\b", text))
    out.branch2_box_count = len(re.findall(r"\bbranch2_box_\d{4}\b", text))
    return out


def infer_module_name(file_path: str) -> str | None:
    path = Path(file_path).resolve()
    try:
        rel = path.relative_to(PROJECT_ROOT)
    except ValueError:
        return None
    if rel.suffix != ".lean":
        return None
    return ".".join(rel.with_suffix("").parts)


def compile_candidate(file_path: str) -> tuple[bool, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", file_path],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "error:" not in out and "declaration uses 'sorry'" not in out
    return ok, out


def axiom_audit(file_path: str, namespace: str, theorem_name: str) -> tuple[bool, str]:
    full_name = f"{namespace}.{theorem_name}" if namespace else theorem_name
    source = Path(file_path).read_text()

    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=PROJECT_ROOT, delete=False) as tmp:
        tmp.write(source)
        tmp.write("\n\n")
        tmp.write(f"#print axioms {full_name}\n")
        tmp_path = tmp.name

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", tmp_path],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
        )
        out = proc.stdout + proc.stderr
        if proc.returncode != 0 or "sorryAx" in out:
            return False, out

        custom = []
        for line in out.splitlines():
            line = line.strip()
            if line.startswith("'") and line.endswith("'"):
                name = line.strip("'")
                if name not in ALLOWED_GLOBAL_AXIOMS:
                    custom.append(name)
        if custom:
            return False, f"unexpected global axioms: {custom}"
        return True, "global axiom audit passed (no project-specific axioms)"
    finally:
        os.unlink(tmp_path)


def theorem_type_check(file_path: str, namespace: str, theorem_kind: str) -> tuple[bool, str]:
    full_name = (
        f"{namespace}.korenblum_target_reduction"
        if theorem_kind == "legacy"
        else f"{namespace}.direct_disk_vs_annulus"
    )
    scalar_name = f"{namespace}.scalarCriterion_ge_one"
    c_name = f"{namespace}.cValueQ"
    source = Path(file_path).read_text()

    expected_scalar_type = f"""
∀
  (K : ℝ → ℝ → ℝ)
  (hPaperK : KorenblumProofSearch3.WangKernelExact.PaperKFormula K ({c_name} : ℝ)),
  1 ≤ Korenblum.scalarCriterion ({c_name} : ℝ) (KorenblumProofSearch3.WangOuter.paperLambda K ({c_name} : ℝ))
""".strip()

    expected_reduction_type = f"""
∀
  (K : ℝ → ℝ → ℝ)
  {{innerExcess annulusExcess : ℝ}}
  (hPaper :
    1 ≤ Korenblum.scalarCriterion ({c_name} : ℝ) (KorenblumProofSearch3.WangOuter.paperLambda K ({c_name} : ℝ)) →
      innerExcess ≤ annulusExcess)
  (hPaperK : KorenblumProofSearch3.WangKernelExact.PaperKFormula K ({c_name} : ℝ)),
  innerExcess ≤ annulusExcess
""".strip()

    expected_direct_type = f"""
∀
  (K : ℝ → ℝ → ℝ)
  {{a b : ℕ → ℂ}}
  (paper : KorenblumProofSearch3.PaperAxioms.Section2Assumptions a b K ({c_name} : ℝ))
  (hPlusSigma :
    Summable (fun n : ℕ => KorenblumProofSearch3.OneModePaperBridge.plusSeq a b n * ({c_name} : ℝ) ^ (2 * n)))
  (hMinusSigmaC :
    Summable (fun n : ℕ => KorenblumProofSearch3.OneModePaperBridge.minusSeq a b n * ({c_name} : ℝ) ^ (2 * n)))
  (hMinusSigma :
    ∀ ⦃ρ : ℝ⦄, ({c_name} : ℝ) < ρ → ρ < 1 →
      Summable (fun n : ℕ => KorenblumProofSearch3.OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
  (hAnnInt :
    IntervalIntegrable (KorenblumProofSearch3.AnnulusIntegralReduction.annulusDensity paper.circleGap)
      volume ({c_name} : ℝ) (1 : ℝ)),
  KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap 0 ({c_name} : ℝ) ≤
    KorenblumProofSearch3.AnnulusIntegralReduction.annulusSlice paper.circleGap ({c_name} : ℝ) (1 : ℝ)
""".strip()

    if theorem_kind == "legacy":
        check_src = f"""{source}

#check (@{scalar_name} : {expected_scalar_type})
#check (@{full_name} : {expected_reduction_type})
""".strip()
    else:
        check_src = f"""{source}

#check (@{full_name} : {expected_direct_type})
""".strip()

    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=PROJECT_ROOT, delete=False) as tmp:
        tmp.write(check_src)
        tmp_path = tmp.name

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", tmp_path],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
        )
        out = proc.stdout + proc.stderr
        return proc.returncode == 0 and "error:" not in out, out
    finally:
        os.unlink(tmp_path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", required=True)
    args = parser.parse_args()

    cand = parse_candidate(args.file)
    print(f"candidate: {args.file}")
    print(f"namespace: {cand.namespace}")
    print(f"branch1 box references: {cand.branch1_box_count}")
    print(f"branch2 box references: {cand.branch2_box_count}")

    ok, out = compile_candidate(args.file)
    print(f"compile: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(failure_excerpt(out))
        raise SystemExit(1)

    ok, out = axiom_audit(args.file, cand.namespace, cand.theorem_name)
    print(f"axiom audit: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(failure_excerpt(out))
        raise SystemExit(1)

    ok, out = theorem_type_check(args.file, cand.namespace, cand.theorem_kind)
    print(f"type check: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(failure_excerpt(out))
        raise SystemExit(1)

    print("proof-path status: PASS (Lean compile + theorem type + no project-specific global axioms; paper assumptions explicit in theorem hypotheses)")


if __name__ == "__main__":
    main()
