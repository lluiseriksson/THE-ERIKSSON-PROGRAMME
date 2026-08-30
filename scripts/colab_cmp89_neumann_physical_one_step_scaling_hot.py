#!/usr/bin/env python3
"""Retained-checkout diagnostic for physical one-step spacing cancellation."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path

RUNNER_REV = "cmp89-neumann-physical-one-step-scaling-hot-v2"
SOURCE_SHA = "ce8bc262452f33906a8f34112810cfb15637820a"
BASE_SHA = "f48c7eeb7af46c708e94301a2529d632f584c7d5"
ROOT = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScaling.lean":
        "f3d9e397a126bd305d9cbabdb24b3dcd2f150ccfa7324d677773f131c838f205",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean":
        "167a36ddafefcfcdd4791e17874eef013179b751d37e0bf8a415c07608e53042",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling",
    "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_physical_scaling",
    "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_lt_one_iff",
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
    run("cmp89_neumann_physical_one_step_scaling_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling"])
    audit = run("cmp89_neumann_physical_one_step_scaling_audit", ["lake", "env",
        "lean", "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean"])
    audit_axioms(audit)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
