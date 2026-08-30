#!/usr/bin/env python3
"""Retained-checkout diagnostic for the quantitative CMP89 Neumann defect."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-recursive-defect-hot-v2"
SOURCE_SHA = "b82d65be54166db01c154031263cc018307bbaed"
BASE_SHA = "6a1f71c4a0ab1ac6c7160c087720d6b681377a22"
ROOT = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBound.lean":
        "b097d05f557904a3b16a456afec029c5bdca147933a925d679b8f5c4e920bd37",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBoundAudit.lean":
        "5d4ca0c3fef0577ce31d59a1a62423300cfeaec5a6205375ff769cac98c1feb7",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp99SourceCoarseTransportRemainderCochain_apply",
    "YangMills.RG.restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel",
    "YangMills.RG.norm_restrictOne_cmp99SourceCoarseTransportRemainderCochain_sq_le",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {"sorryAx", "ofReduceBool", "Lean.ofReduceBool"}


def run(stage: str, command: list[str]) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    elapsed = time.perf_counter() - started
    if child.stdout:
        print(child.stdout, end="" if child.stdout.endswith("\n") else "\n")
    print(f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}", flush=True)
    if child.returncode != 0:
        raise RuntimeError(f"STAGE_FAILED={stage} EXIT={child.returncode}")
    return child.stdout


def git_blob(path: str) -> bytes:
    child = subprocess.run(
        ["git", "cat-file", "blob", f"{SOURCE_SHA}:{path}"], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
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
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(EXPECTED_DECLARATIONS)})
        )
    for name in sorted(EXPECTED_DECLARATIONS):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET={name}:{sorted(axioms)!r}")
        print(f"AXIOM_GATE={name} AXIOMS={','.join(sorted(axioms))}", flush=True)


def main() -> int:
    print(f"RUNNER_REV={RUNNER_REV}", flush=True)
    dirty = run("tracked_clean_gate", ["git", "status", "--porcelain", "--untracked-files=no"]).strip()
    if dirty:
        raise RuntimeError(f"TRACKED_WORKTREE_DIRTY={dirty!r}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("head_gate", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError(f"HEAD_MISMATCH={head}")
    mathlib = run("mathlib_pin_gate", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]).strip()
    if mathlib != "07642720480157414db592fa85b626dafb71355b":
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={mathlib}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    run("overlay_text_guard", [
        "python3", "scripts/check_lean_overlay_text.py", "--base", BASE_SHA,
        "--head", SOURCE_SHA, "--require-prevalidation",
    ])
    run("import_prefix_guard", ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS])
    run("cmp89_neumann_recursive_defect_focal", [
        "lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannRecursiveDefectBound",
    ])
    audit = run("cmp89_neumann_recursive_defect_audit", [
        "lake", "env", "lean",
        "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBoundAudit.lean",
    ])
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
