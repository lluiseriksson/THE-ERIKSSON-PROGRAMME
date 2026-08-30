#!/usr/bin/env python3
"""Retained-checkout diagnostic for two-scale physical Neumann absorption."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path

RUNNER_REV = "cmp89-neumann-two-scale-physical-absorption-hot-v3"
SOURCE_SHA = "dd0030677c5036331343a98bc5e4df653209f39f"
BASE_SHA = "5e83f665a0fec3dd2a780a6d4e2b1575f57a1d5d"
ROOT = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScaling.lean":
        "2c87edc4cabc0483f3e20328843647c2518b1fd98c6bf3d5b3396371160b5b9f",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean":
        "167a36ddafefcfcdd4791e17874eef013179b751d37e0bf8a415c07608e53042",
    "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorption.lean":
        "b6b5c5f0e93c6fb3330cd449009c14e3a6c68da02dfc0c9abdd996838f8d639d",
    "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorptionAudit.lean":
        "530395fbfa1f3d79260c487585adf16fb754c5bed1ccf164b11327c12b858fd3",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitness.lean":
        "9bcc6d7cef4ab730d53ed2d97783521d348881828a1609c0d8887567b30650e8",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitnessAudit.lean":
        "8026566164e40f2dd797bb6031f2c6b97a367a27c3d340d96315809e93dea901",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling",
    "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_physical_scaling",
    "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_lt_one_iff",
    "YangMills.RG.eq_zero_of_cmp89SourceNeumann_twoScale_physical_absorption",
    "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_eq",
    "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_lt_one",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {"sorryAx", "ofReduceBool", "Lean.ofReduceBool"}


def run(stage: str, command: list[str]) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, check=False)
    elapsed = time.perf_counter() - started
    if child.stdout:
        print(child.stdout, end="" if child.stdout.endswith("\n") else "\n")
    print(f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}", flush=True)
    if child.returncode != 0:
        raise RuntimeError(f"STAGE_FAILED={stage} EXIT={child.returncode}")
    return child.stdout


def git_blob(path: str) -> bytes:
    child = subprocess.run(["git", "cat-file", "blob", f"{SOURCE_SHA}:{path}"],
                           cwd=ROOT, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, check=False)
    if child.returncode != 0:
        raise RuntimeError(f"GIT_BLOB_READ_FAILED={path}")
    return child.stdout


def audit_axioms(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for token in FORBIDDEN_TOKENS:
        if token in compact:
            raise RuntimeError(f"FORBIDDEN_AXIOM={token}")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != EXPECTED_DECLARATIONS:
        raise RuntimeError("AXIOM_DECLARATIONS_MISMATCH=" + repr({
            "found": sorted(found), "expected": sorted(EXPECTED_DECLARATIONS)}))
    for name in sorted(EXPECTED_DECLARATIONS):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET={name}:{sorted(axioms)!r}")
        print(f"AXIOM_GATE={name} AXIOMS={','.join(sorted(axioms))}", flush=True)


def main() -> int:
    print(f"RUNNER_REV={RUNNER_REV}", flush=True)
    dirty = run("tracked_clean_gate", ["git", "status", "--porcelain",
                                        "--untracked-files=no"]).strip()
    if dirty:
        raise RuntimeError(f"TRACKED_WORKTREE_DIRTY={dirty!r}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("head_gate", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError(f"HEAD_MISMATCH={head}")
    mathlib = run("mathlib_pin_gate", ["git", "-C", ".lake/packages/mathlib",
                                       "rev-parse", "HEAD"]).strip()
    if mathlib != "07642720480157414db592fa85b626dafb71355b":
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={mathlib}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    run("overlay_text_guard", ["python3", "scripts/check_lean_overlay_text.py",
        "--base", BASE_SHA, "--head", SOURCE_SHA, "--require-prevalidation"])
    run("import_prefix_guard", ["python3", "scripts/check_lean_import_prefix.py",
                                 *SOURCE_BLOBS])
    physical = run("cmp89_neumann_physical_one_step_scaling_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling"])
    del physical
    physical_audit = run("cmp89_neumann_physical_one_step_scaling_audit", ["lake", "env",
        "lean", "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean"])
    run("cmp89_neumann_two_scale_physical_absorption_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89SourceNeumannTwoScalePhysicalAbsorption"])
    audit = run("cmp89_neumann_two_scale_physical_absorption_audit", ["lake", "env",
        "lean", "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorptionAudit.lean"])
    witness = run("cmp89_neumann_physical_gate_witness_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateWitness"])
    del witness
    witness_audit = run("cmp89_neumann_physical_gate_witness_audit", ["lake", "env",
        "lean", "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitnessAudit.lean"])
    audit_axioms(physical_audit + "\n" + audit + "\n" + witness_audit)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
