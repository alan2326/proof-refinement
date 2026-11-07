#!/usr/bin/env python3
"""
Reconstruct S0 = the korenblum workspace as it stood at the end of sprint 083
(V64 accepted at c = 35646/100000; sprints 084-088 not yet performed).

All boundaries below were established forensically; see
docs/2026-07-27-ablation-design.md sect. 2.3.  Run against a COPY -- never
against the korenblum/ source tree.
"""
import json
import re
import shutil
import sys
from pathlib import Path

WS = Path(sys.argv[1] if len(sys.argv) > 1 else
          str(Path(__file__).resolve().parents[1] / "workspaces" / "S0_korenblum"))
K = WS / "ProofRefinement" / "Korenblum"

ANCHOR_UTC = "2026-05-05T04:00:00"
FIRST_ANCHOR_SPRINT = 84

log = []


def note(msg):
    log.append(msg)
    print(msg)


def keep_lines(path: Path, keep_ranges):
    """Rewrite `path` keeping only the given 1-indexed inclusive line ranges."""
    lines = path.read_text().splitlines(keepends=True)
    out = []
    for lo, hi in keep_ranges:
        out.extend(lines[lo - 1:hi])
    path.write_text("".join(out))
    note(f"  truncated {path.relative_to(WS)}: {len(lines)} -> {len(out)} lines")


# ---------------------------------------------------------------- 1. Reduction
note("1. Proof/Reduction.lean -> keep 1..8258 (cut at sprint-084 doc block)")
red = K / "Proof" / "Reduction.lean"
txt = red.read_text().splitlines(keepends=True)
# 1-indexed line 8259 == "/-!", 8260 == "## Sprint 084"; keep through 8258.
assert txt[8259].startswith("## Sprint 084"), f"boundary moved: {txt[8259]!r}"
assert txt[8258].startswith("/-!"), f"boundary moved: {txt[8258]!r}"
assert txt[-1].strip() == "end ProofRefinement.Korenblum", f"tail moved: {txt[-1]!r}"
keep_lines(red, [(1, 8258)])
# `namespace ProofRefinement.Korenblum` opens at line 9 and was closed only by
# the final line of the file, which the truncation removed. Re-close it.
with red.open("a") as fh:
    fh.write("\nend ProofRefinement.Korenblum\n")
note("  re-appended `end ProofRefinement.Korenblum`")

# ------------------------------------------- 2. un-hoist the V63 derived files
# Sprints 096-098 MOVED the mathematical content of Candidates/V63/{...}.lean
# into Proof/{...}.lean, left thin re-export shims behind, and rewrote V64's
# imports AND its fully-qualified body references.  Undo all three parts.
HOISTED = ("Integrability", "Summability", "DiskInnerSeriesBridge")
note("2. un-hoist V63 derived-theorem files (reverse of sprints 096-098)")
for mod in HOISTED:
    src = K / "Proof" / f"{mod}.lean"
    dst = K / "Candidates" / "V63" / f"{mod}.lean"
    assert src.exists(), f"hoisted source missing: {src}"
    body = src.read_text()
    old_ns = f"ProofRefinement.Korenblum.Proof.{mod}"
    new_ns = f"ProofRefinement.Korenblum.Candidates.V63.{mod}"
    assert f"namespace {old_ns}" in body, f"namespace not found in {src}"
    body = body.replace(old_ns, new_ns)
    dst.write_text(body)
    src.unlink()
    note(f"  Proof/{mod}.lean -> Candidates/V63/{mod}.lean "
         f"(namespace re-scoped; shim overwritten)")

note("   Candidates/V64.lean -> re-point imports and body refs at V63")
v64 = K / "Candidates" / "V64.lean"
s = v64.read_text()
n_imp = n_ref = 0
for mod in HOISTED:
    imp_before = f"import ProofRefinement.Korenblum.Proof.{mod}"
    imp_after = f"import ProofRefinement.Korenblum.Candidates.V63.{mod}"
    assert imp_before in s, f"missing hoisted import {mod}"
    n_imp += s.count(imp_before)
    s = s.replace(imp_before, imp_after)
    ref_before = f"ProofRefinement.Korenblum.Proof.{mod}."
    ref_after = f"ProofRefinement.Korenblum.Candidates.V63.{mod}."
    n_ref += s.count(ref_before)
    s = s.replace(ref_before, ref_after)
v64.write_text(s)
note(f"  {n_imp} imports + {n_ref} qualified body references re-pointed")

# --------------------------------------------------- 3. delete post-anchor Lean
note("3. delete post-anchor candidates")
for n in (65, 66, 67, 68):
    for p in (K / "Candidates" / f"V{n}.lean", K / "Candidates" / f"V{n}"):
        if p.exists():
            shutil.rmtree(p) if p.is_dir() else p.unlink()
            note(f"  rm {p.relative_to(WS)}")

# --------------------------------------------------------------- 4. lemma.toml
note("4. lemma.toml -> keep 1..205 (thru hCircleGapInt_v64) + 322..489")
lt = K / "lemma.toml"
lines = lt.read_text().splitlines()
assert lines[204].strip() == '"hCircleGapInt_v64",', lines[204]
assert lines[321].strip() == "]", lines[321]
keep_lines(lt, [(1, 205), (322, 489)])

# 4b. The [import_policy].allowed_exact list is INSIDE the kept prefix but was
#     edited by sprints 084-098: it registers V65-V68 derived-theorem modules
#     by name and states the anchor's answer (c = 356562/1000000) in a comment.
#     Restore it to the ten modules that existed at sprint 083.
note("4b. lemma.toml -> restore [import_policy].allowed_exact to sprint-083 set")
S083_ALLOWED_EXACT = [
    "ProofRefinement.Korenblum.Candidates.V53.ThetaStep",
    "ProofRefinement.Korenblum.Candidates.V54.LiftIdentity",
    "ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge",
    "ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated",
    "ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated",
    "ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity",
    "ProofRefinement.Korenblum.Candidates.V63.Integrability",
    "ProofRefinement.Korenblum.Candidates.V63.Summability",
    "ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge",
    "ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints",
]
text = lt.read_text()
start = text.index("allowed_exact = [")
end = text.index("\n]", start) + 2
old_block = text[start:end]
assert "V68.ElevenWindowEndpoints" in old_block, "import_policy block moved"
new_block = ("allowed_exact = [\n"
             + "".join(f'  "{m}",\n' for m in S083_ALLOWED_EXACT)
             + "]")
lt.write_text(text[:start] + new_block + text[end:])
note(f"  {old_block.count(chr(10))} lines -> {new_block.count(chr(10))} lines "
     f"({len(S083_ALLOWED_EXACT)} modules)")

# ------------------------------------------------------- 5. rigorous_scalar.py
note("5. Numerical_Library/rigorous_scalar.py -> keep 1..1871")
rs = K / "Numerical_Library" / "rigorous_scalar.py"
lines = rs.read_text().splitlines()
assert "Sprint 087" in lines[1873], lines[1873]
keep_lines(rs, [(1, 1871)])

# ------------------------------------------------- 6. sprint artefacts + scratch
note(f"6. delete sprint >= {FIRST_ANCHOR_SPRINT} contracts / verdicts / scratch")
pat = re.compile(r"sprint_(\d{3})")
for d in (K / "Sprint_Contracts", K / "Refinement_Log", K / "Scratch"):
    if not d.exists():
        continue
    for p in sorted(d.iterdir()):
        m = pat.search(p.name)
        if m and int(m.group(1)) >= FIRST_ANCHOR_SPRINT:
            p.unlink()
            note(f"  rm {p.relative_to(WS)}")

# ------------------------------------------------------------------ 7. log.jsonl
note(f"7. log.jsonl -> keep entries with timestamp_utc < {ANCHOR_UTC}")
lj = K / "Refinement_Log" / "log.jsonl"
rows = [json.loads(l) for l in lj.read_text().splitlines() if l.strip()]
kept = [r for r in rows if r["timestamp_utc"][:19] < ANCHOR_UTC]
lj.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in kept))
note(f"  {len(rows)} -> {len(kept)} entries (last: {kept[-1]['candidate']} "
     f"{kept[-1]['score']} @ {kept[-1]['timestamp_utc'][:19]})")

# ------------------------------------------------- 8. Bulletin / Experience
# Bulletin.md carries TWO human directive blocks at the top:
#   lines  17-279 : "2026-05-05 (human, AUDIT + NEW-IDEAS)" -- POST-anchor. It
#                   audits sprints 086-092 and states the architectural ceiling
#                   c = 0.356565 outright. Removing this is essential: it is a
#                   direct statement of the answer.
#   lines 281-... : "2026-05-04 (human, EXPLICIT V38 REFERENCE)" -- PRE-anchor,
#                   and the directive sprint 084's contract actually cites. It
#                   names V38's c = 356401/1000000 (the roadmap target at S0,
#                   which the anchor then beat). KEPT.
note("8. Bulletin.md -> drop post-anchor 2026-05-05 directive (17..280), "
     "keep 2026-05-04 V38 directive; tail -> 1279")
b = K / "Bulletin.md"
bl = b.read_text().splitlines()
assert bl[16].startswith("> **Directive update — 2026-05-05"), bl[16][:60]
assert bl[280].startswith("> **Directive update — 2026-05-04"), bl[280][:60]
keep_lines(b, [(1, 16), (281, 1279)])
note("  dropped the 2026-05-05 AUDIT directive (264 lines) — stated the answer")
keep_lines(K / "Experience.md", [(1, 4583)])

# ---------------------------------------------------- 9. stray post-anchor files
note("9. delete stray post-anchor artefacts")
for rel in ("ProofRefinement/Korenblum/V68_vs_Wang.md",
            "ProofRefinement/Korenblum/AXIOM_EXTRACTION.md",
            "eval_v68_output.txt"):
    p = WS / rel
    if p.exists():
        p.unlink()
        note(f"  rm {rel}  (post-anchor; would leak the answer)")

# ShinkaAblation is a separate side-experiment, not part of the harness loop.
sh = WS / "ShinkaAblation"
if sh.exists():
    shutil.rmtree(sh)
    note("  rm ShinkaAblation/  (separate side-experiment, not in harness loop)")

# ------------------------------------------------------ 10. scrub stale refs
# Two known deviations from a perfect sprint-083 state, both unavoidable:
#
#  (a) `certify_two_window_mass_at_35646_sqrt` was migrated IN PLACE from
#      mp.quad to Arb interval arithmetic at sprints 099/101/102. The
#      pre-migration body is unrecoverable (no VCS coverage). We keep the Arb
#      version: it is strictly MORE rigorous than what the anchor run used, so
#      it steelmans every arm rather than weakening any. Its docstrings,
#      however, cite sprints 100-102 and V66's joint-mass margin -> scrub.
#  (b) The V63 derived files carry sprint-097/098 hoist headers (the bodies
#      are byte-identical to the originals; only the header differs) -> scrub.
#
# Neither scrub touches executable code or Lean proof terms.
note("10. scrub post-anchor references from surviving file headers/docstrings")

rs = K / "Numerical_Library" / "rigorous_scalar.py"
s = rs.read_text()
SCRUBS = [
    ("    — three orders of magnitude tighter than V66's `+1.20e-4`\n"
     "    centered margin. The boxA windows were never the bottleneck in\n"
     "    sprint 100; the bottleneck was the mode1 union-radius scaling,\n"
     "    which sprint 101's Λ_upper dispatch fixed.\n",
     "    — comfortably tighter than the joint-mass acceptance margin.\n"),
]
for before, after in SCRUBS:
    if before in s:
        s = s.replace(before, after)
        note("  scrubbed post-anchor margin reference in rigorous_scalar.py")
rs.write_text(s)
assert "V66" not in rs.read_text(), "residual V66 reference in numerical library"

HEADER = {
    "Integrability":
        "-- V63 per-candidate derived theorems: parametric `IntervalIntegrable`\n"
        "-- of `ModeBridge.scalarIntegrand`, plus its two-window consolidation\n"
        "-- shape. Two `theorem`s; no `axiom`s, no `sorry`s.\n",
    "Summability":
        "-- V63 per-candidate derived theorems: the six summability shapes\n"
        "-- derived from the H² hypothesis. No `axiom`s, no `sorry`s.\n",
    "DiskInnerSeriesBridge":
        "-- V63 per-candidate derived theorems: the `diskExcess ≤\n"
        "-- innerSeriesExcess` bridge and its summability side-condition.\n"
        "-- No `axiom`s, no `sorry`s.\n",
}
for mod, hdr in HEADER.items():
    p = K / "Candidates" / "V63" / f"{mod}.lean"
    lines = p.read_text().splitlines(keepends=True)
    n = 0
    while n < len(lines) and lines[n].lstrip().startswith("--"):
        n += 1
    assert n > 0, f"no leading comment block in {p}"
    p.write_text(hdr + "".join(lines[n:]))
    note(f"  replaced {n}-line sprint-097/098 hoist header in V63/{mod}.lean")

# 10c. Relabel post-anchor sprint TAGS in comments that survive inside kept
#      code. These are prose labels only -- no executable code or proof term is
#      touched. Leaving them would tell the agent it is at sprint 099+, which is
#      both false at S0 and a hint that many more sprints happened.
#
#      DOCUMENTED DEVIATION: sprint 085 refactored Reduction.lean IN PLACE at
#      ~line 2497, extracting `pointwise_branch1_on_Ioo_eq5_eq8_eq9` from an
#      inline derivation. That extraction therefore survives in S0. It is
#      score-neutral (sprint 085 shipped a V65-tie, no c-change) and is not
#      cleanly reversible, so it is kept and reported: the anchor task in this
#      reproduction is "sprints 084-088 minus 085's DRY refactor".
RELABEL = {
    K / "Numerical_Library" / "rigorous_scalar.py": [
        ("# Sprint 099: arb-based rigorous interval-arithmetic re-discharge of",
         "# Arb-based rigorous interval-arithmetic discharge of"),
        ("Sprint 099 helper:", "Helper:"),
        ("Sprint 099 zero-argument", "Zero-argument"),
        ("Sprint 099 migration:", "Note:"),
        ("Sprint 099 witness (arb interval-quadrature backend):",
         "Witness (arb interval-quadrature backend):"),
        ("``Scratch/sprint_099_arb_two_window_mass_witness.py`` — rigorous",
         "``Scratch/arb_two_window_mass_witness.py`` — rigorous"),
        ("sprint 099's behaviour byte-for-byte", "the mp.quad behaviour byte-for-byte"),
        ("Structurally parallel to sprint 099's", "Structurally parallel to"),
    ],
    K / "Proof" / "Reduction.lean": [
        ("Sprint 085: factored Branch.one pointwise bound. The standalone theorem",
         "Factored Branch.one pointwise bound. The standalone theorem"),
        ("Sprint 085 refactor: the inline pointwise derivation has been extracted into",
         "The inline pointwise derivation has been extracted into"),
        ("  -- (sprint 085).", "  -- (factored out above)."),
    ],
}
for p, subs in RELABEL.items():
    s = p.read_text()
    hits = 0
    for before, after in subs:
        hits += s.count(before)
        s = s.replace(before, after)
    p.write_text(s)
    note(f"  relabelled {hits} post-anchor sprint tag(s) in {p.name}")

(WS / "RECONSTRUCTION.log").write_text("\n".join(log) + "\n")
note("\nDONE -- now run the acceptance gate.")
