#!/usr/bin/env python3
"""Retained-runtime retry for the CMP89 reflection inverse producer."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-reflection-inverse-hot-v2"
SOURCE_SHA = "700818adb4eb1a1a4ace8bafe17b983ef1e835e0"
ROOT = Path("/content/hrpoly-cmp89-neumann-rectangle-lift-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperator.lean":
        "699ca04c04c31900aa23a750d417bf3b716411df785794a6701aa3321d68f70e",
    "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperatorAudit.lean":
        "a0a0fbebbefa2833c9435afd822ea76d35e331f30a45762b2469cbde4d085d73",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducer.lean":
        "37e558f391f286d3dd8f7c1050e957483a4c8e7a675b2450948592925cb63bf5",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducerAudit.lean":
        "44882d0ec10fe5cfa6fa156acb2a5551e8156cbdd46a3c94c951a5984e03fdfe",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.finitePiLpScalarKernelOperator",
    "YangMills.RG.finitePiLpScalarKernelOperator_single",
    "YangMills.RG.cmp89NeumannScalarReflectionKernel",
    "YangMills.RG.cmp89NeumannScalarReflectionOperator",
    "YangMills.RG.cmp89NeumannScalarReflectionOperator_single",
    "YangMills.RG.cmp89NeumannReflectionSeries_smul",
    "YangMills.RG.cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse",
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
    paths = Path("/content/cmp89-neumann-reflection-inverse-hot-v2-paths.txt")
    paths.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run("overlay_text_guard", ["python3", "scripts/check_lean_overlay_text.py",
        "--paths-from", str(paths), "--require-prevalidation"])
    run("import_prefix_guard", ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS])
    run("cmp89_neumann_scalar_reflection_operator_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89NeumannScalarReflectionOperator"])
    audit1 = run("cmp89_neumann_scalar_reflection_operator_audit", ["lake", "env", "lean",
        "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperatorAudit.lean"])
    run("cmp89_neumann_reflection_inverse_producer_focal", ["lake", "build",
        "YangMills.RG.BalabanCMP89CanonicalNeumannReflectionInverseProducer"])
    audit2 = run("cmp89_neumann_reflection_inverse_producer_audit", ["lake", "env", "lean",
        "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducerAudit.lean"])
    audit_axioms(audit1 + "\n" + audit2)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
