#!/usr/bin/env python3
"""Retained-checkout diagnostic for the CMP89 Neumann one-scale range.

This is not cold seal authority.  It verifies that the literal physical
average and printed weighted adjoint reconstruct a field on the exact
regional Neumann kernel.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-one-scale-range-hot-v3"
SOURCE_SHA = "fd4ca187d4e943c446177ec26d920f6740a87dab"
BASE_SHA = "1851c69a"
ROOT = Path("/content/hrpoly-cmp89-neumann-source-chain-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransport.lean":
        "3ca601ce233d3c5da92572058677b71a3a4e5d97ce92c50fe3999f1715270913",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransportAudit.lean":
        "7b339d2fd3aeb5f965fc5985ed01b504d6a1684e0cb246897d164427e11c5320",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransport.lean":
        "9147a2ecd753cf68bde1707fd90e15610b04309f71985bf89481efdc36b14e8d",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransportAudit.lean":
        "342404b048690f783be814ee49d823236938d41b6a3f875687c1d70767444670",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRange.lean":
        "55fe6ac6df9f07156ba87fadc980193298732426cb4c39f33d2e37fba88a14be",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRangeAudit.lean":
        "5672fb425b1693f45d93c303fad125cfbf491e8d788a0999e5e44af9661bee94",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_blockAverage",
    "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {"sorryAx", "ofReduceBool", "Lean.ofReduceBool"}


def run(stage: str, command: list[str]) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
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
        ["git", "cat-file", "blob", f"{SOURCE_SHA}:{path}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"GIT_BLOB_READ_FAILED={path} STDERR={child.stderr.decode(errors='replace')!r}"
        )
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
    dirty = run(
        "tracked_clean_gate",
        ["git", "status", "--porcelain", "--untracked-files=no"],
    ).strip()
    if dirty:
        raise RuntimeError(f"TRACKED_WORKTREE_DIRTY={dirty!r}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("head_gate", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError(f"HEAD_MISMATCH={head}")
    mathlib = run(
        "mathlib_pin_gate",
        ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
    ).strip()
    if mathlib != "07642720480157414db592fa85b626dafb71355b":
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={mathlib}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    run(
        "overlay_text_guard",
        [
            "python3",
            "scripts/check_lean_overlay_text.py",
            "--base",
            BASE_SHA,
            "--head",
            SOURCE_SHA,
            "--require-prevalidation",
        ],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "cmp89_neumann_one_scale_range_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannOneScaleRange"],
    )
    audit = run(
        "cmp89_neumann_one_scale_range_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRangeAudit.lean",
        ],
    )
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
