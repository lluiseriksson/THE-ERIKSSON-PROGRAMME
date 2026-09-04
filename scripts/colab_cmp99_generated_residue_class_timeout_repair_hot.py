#!/usr/bin/env python3
"""Retained-runtime diagnostic for the factored residue-class signature.

This runner reuses only the graph retained by the failed fresh-checkout gate.
It checks out the exact repair commit, verifies both Git blobs, runs the text
guards, and stops on the first focal or audit error.  A PASS is diagnostic
only and cannot retire PRE-VALIDATION.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import time


RUNNER_REV = "cmp99-generated-residue-class-timeout-repair-hot-v3"
SOURCE_SHA = "eab174fd349950fa7dedd1ad9c2f2813bc4b3493"
ROOT = Path("/content/hrpoly-cmp99-generated-residue-class-cold-v1")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClass.lean":
        "fcbff1ea72dbfaf88a8894ee027bf3e746e1b808",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClassAudit.lean":
        "905fa26eeca9418c6975fb89adeea2e7769a2451",
}


def run(stage: str, command: list[str], cwd: Path = ROOT) -> None:
    started = time.perf_counter()
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    result = subprocess.run(command, cwd=cwd, env=os.environ.copy())
    elapsed = time.perf_counter() - started
    print(
        f"STAGE={stage} EXIT={result.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if result.returncode != 0:
        print(f"FINAL_STATUS=FAIL FIRST_ERROR_STAGE={stage}", flush=True)
        raise SystemExit(result.returncode)


def output(command: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main() -> int:
    print(f"RUNNER_REV={RUNNER_REV}", flush=True)
    if not ROOT.is_dir():
        raise RuntimeError(f"RETAINED_ROOT_MISSING={ROOT}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    head = output(["git", "rev-parse", "HEAD"])
    print(f"SOURCE_HEAD={head}", flush=True)
    if head != SOURCE_SHA:
        raise RuntimeError("SOURCE_HEAD_MISMATCH")
    for path, expected in SOURCE_BLOBS.items():
        actual = output(["git", "rev-parse", f"HEAD:{path}"])
        print(f"SOURCE_BLOB={path} OID={actual}", flush=True)
        if actual != expected:
            raise RuntimeError(f"SOURCE_BLOB_MISMATCH={path}")
    manifest = Path(
        "/content/cmp99-generated-residue-class-timeout-repair-hot-v3-paths.txt"
    )
    manifest.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run(
        "overlay_text_guard",
        ["python3", "scripts/check_lean_overlay_text.py", "--paths-from", str(manifest)],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "generated_residue_class_repair_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClass",
        ],
    )
    run(
        "generated_residue_class_repair_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClassAudit.lean",
        ],
    )
    print("FINAL_STATUS=PASS HOT_DEBUG_NOT_EVIDENCE=1", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
