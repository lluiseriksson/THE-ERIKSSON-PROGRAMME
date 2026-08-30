#!/usr/bin/env python3
"""Retained-checkout diagnostic for physical Neumann gate reachability."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-physical-gate-reachability-hot-v1"
SOURCE_SHA = "866455f7c467caf057561b43e1165b8189ed895e"
ROOT = Path("/content/hrpoly-cmp89-neumann-generated-two-scale-absorption-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicity.lean":
        "ebf14e1b4ff9d0eca2dc4d38d25144d3fa3523c5c938ccef681d33f7fb772c13",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicityAudit.lean":
        "15b27529a20769cd9b10f3170b462d71232fe025838970e1dbd357ceae13fe55",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachability.lean":
        "bcceb9079750672fd7023a93fc65b6d9f27b45e475ce2e2964e204848a5163e7",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachabilityAudit.lean":
        "c122ee5f3dead42e76ef8dafcf17d87db3eb3a267aa19130cc97ac7dd6f437f4",
}
EXPECTED_BY_STAGE = {
    "monotonicity": {
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepDefectCoefficient_mono",
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_le_d4_M4_q8",
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_radius_bounds_d4_M4",
    },
    "reachability": {
        "YangMills.RG.exists_pos_cmp89SourceNeumann_twoScale_physical_gate_radius",
    },
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
        raise RuntimeError(f"GIT_BLOB_READ_FAILED={path}")
    return child.stdout


def audit_axioms(output: str, stage: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for token in FORBIDDEN_TOKENS:
        if token in compact:
            raise RuntimeError(f"FORBIDDEN_AXIOM={token}")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    expected = EXPECTED_BY_STAGE[stage]
    if set(found) != expected:
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(expected)})
        )
    for name in sorted(expected):
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
    paths_file = Path("/content/hrpoly-cmp89-neumann-physical-gate-reachability-paths.txt")
    paths_file.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run(
        "overlay_text_guard",
        [
            "python3", "scripts/check_lean_overlay_text.py", "--paths-from",
            str(paths_file), "--require-prevalidation",
        ],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "physical_gate_monotonicity_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateMonotonicity"],
    )
    monotonicity_audit = run(
        "physical_gate_monotonicity_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicityAudit.lean"],
    )
    audit_axioms(monotonicity_audit, "monotonicity")
    run(
        "physical_gate_reachability_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateReachability"],
    )
    reachability_audit = run(
        "physical_gate_reachability_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachabilityAudit.lean"],
    )
    audit_axioms(reachability_audit, "reachability")
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
