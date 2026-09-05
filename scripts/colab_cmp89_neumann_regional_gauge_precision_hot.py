#!/usr/bin/env python3
"""Retained-checkout diagnostic for the CMP89 Neumann canonical precision.

This is deliberately not cold seal authority.  It reuses the verified
toolchain and project build of the immediately preceding fresh Colab gate,
checks out one exact source SHA, verifies its two Git blobs, and stops at the
first focal or axiom-audit failure.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-regional-gauge-precision-hot-v3"
SOURCE_SHA = "8cf3bfe7d1e83524d1a395ceaba56a7f388c90c6"
ROOT = Path("/content/hrpoly-cmp89-neumann-dirichlet-boundary-nogo")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecision.lean":
        "dfef4cef851c6062632098b3ab49971c0bf9cb6fe6ec9f2219f961cff4706a73",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecisionAudit.lean":
        "3dff5e6ea6a93f743820b9710ac10e295e55587194e7bb826a7580e9c9051e1f",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.inner_cmp89SourceNeumannRegionalGaugePrecision",
    "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_isSymmetric",
    "YangMills.RG.isCoerciveCLM_cmp89SourceNeumannRegionalGaugePrecision",
    "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_comp_green",
    "YangMills.RG.cmp89SourceNeumannRegionalGreen_comp_gaugePrecision",
    "YangMills.RG.inner_cmp89SourceRetainedNeumannPrefixGaugePrecision",
    "YangMills.RG.cmp89SourceRetainedNeumannPrefixGaugePrecision_isSymmetric",
    "YangMills.RG.isCoerciveCLM_cmp89SourceRetainedNeumannPrefixGaugePrecision",
    "YangMills.RG.cmp89SourceRetainedNeumannPrefixGaugePrecision_comp_green",
    "YangMills.RG.cmp89SourceRetainedNeumannPrefixGreen_comp_gaugePrecision",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {"sorryAx", "ofReduceBool", "Lean.ofReduceBool"}


def run(stage: str, command: list[str], *, cwd: Path = ROOT) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    elapsed = time.perf_counter() - started
    if child.stdout:
        print(child.stdout, end="" if child.stdout.endswith("\n") else "\n")
    print(
        f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
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
    if not ROOT.is_dir():
        raise RuntimeError(f"RETAINED_ROOT_MISSING={ROOT}")
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
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "cmp89_neumann_regional_gauge_precision_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision",
        ],
    )
    audit = run(
        "cmp89_neumann_regional_gauge_precision_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecisionAudit.lean",
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
