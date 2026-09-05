#!/usr/bin/env python3
"""Retained-runtime diagnostic for real-slice CMP89 image summability."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-physical-real-summability-hot-v2"
SOURCE_SHA = "cdd859ba99671e83a1ef2b3d8119a4e376a97ced"
ROOT = Path("/content/hrpoly-cmp89-neumann-rectangle-lift-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummability.lean":
        "d5b982f8f5715a42f56f9f3b57df334deb33c37dd6aed048840e5c18137d8312",
    "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummabilityAudit.lean":
        "c950ba2f4ca36bc88c8d8ef8846a2cf600af7040cbe65d88191753ae01584a12",
}
EXPECTED_DECLARATION = (
    "YangMills.RG.summable_cmp89Eq248PhysicalRealNeumannReflection_sum"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


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


def main() -> int:
    print(f"RUNNER_REV={RUNNER_REV}", flush=True)
    if not ROOT.is_dir():
        raise RuntimeError(f"RETAINED_ROOT_MISSING={ROOT}")
    dirty = run("tracked_clean_gate", ["git", "status", "--porcelain", "--untracked-files=no"]).strip()
    if dirty:
        raise RuntimeError(f"TRACKED_WORKTREE_DIRTY={dirty!r}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    if run("head_gate", ["git", "rev-parse", "HEAD"]).strip() != SOURCE_SHA:
        raise RuntimeError("HEAD_MISMATCH")
    pin = run("mathlib_pin_gate", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]).strip()
    if pin != "07642720480157414db592fa85b626dafb71355b":
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={pin}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    paths = Path("/content/cmp89-neumann-physical-real-summability-hot-paths.txt")
    paths.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run("overlay_text_guard", ["python3", "scripts/check_lean_overlay_text.py",
        "--paths-from", str(paths), "--require-prevalidation"])
    run("import_prefix_guard", ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS])
    run("cmp89_neumann_physical_real_summability_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89NeumannPhysicalRealReflectionSummability"])
    audit = run("cmp89_neumann_physical_real_summability_audit", ["lake", "env", "lean",
        "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummabilityAudit.lean"])
    compact = re.sub(r"\s+", "", audit)
    if "sorryAx" in compact or "ofReduceBool" in compact:
        raise RuntimeError("FORBIDDEN_AXIOM")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != 1 or blocks[0][0] != EXPECTED_DECLARATION:
        raise RuntimeError(f"AXIOM_DECLARATIONS_MISMATCH={blocks!r}")
    axioms = {item for item in blocks[0][1].split(",") if item}
    if not axioms.issubset(ALLOWED_AXIOMS):
        raise RuntimeError(f"AXIOM_SET={sorted(axioms)!r}")
    print(f"AXIOM_GATE={EXPECTED_DECLARATION} AXIOMS={','.join(sorted(axioms))}", flush=True)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
