#!/usr/bin/env python3
"""Retained-runtime diagnostic for the physical residue endpoint dictionary.

This hot runner reuses only the graph produced by the preceding arbitrary
residue cold seal.  It checks out one immutable PRE-VALIDATION source, verifies
the two Git blob object IDs, runs the exact textual guards, then the focal and
five-declaration audit.  A PASS is diagnostic only and cannot retire either
PRE-VALIDATION notice.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import time


RUNNER_REV = "cmp99-physical-residue-endpoint-dictionary-hot-v2"
SOURCE_SHA = "b72c6d4ae9e174bf8d003d9fc0747d4bbd1151f1"
ROOT = Path("/content/hrpoly-cmp99-arbitrary-residue-dictionary-cold-v2")
TOOLCHAIN_BIN = Path(
    "/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin"
)
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary.lean":
        "1353ece31405b5ea18a76b163651f2d0fc484d2a",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionaryAudit.lean":
        "639be11b08b488f64fb414038b9e627eb92f9f2b",
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
    if not (TOOLCHAIN_BIN / "lake").is_file():
        raise RuntimeError(f"PINNED_LAKE_MISSING={TOOLCHAIN_BIN / 'lake'}")
    os.environ["PATH"] = str(TOOLCHAIN_BIN) + os.pathsep + os.environ["PATH"]
    print(f"PINNED_TOOLCHAIN_BIN={TOOLCHAIN_BIN}", flush=True)
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
        "/content/cmp99-physical-residue-endpoint-dictionary-hot-v2-paths.txt"
    )
    manifest.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run(
        "overlay_text_guard",
        [
            "python3",
            "scripts/check_lean_overlay_text.py",
            "--paths-from",
            str(manifest),
            "--require-prevalidation",
        ],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "physical_residue_endpoint_dictionary_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary",
        ],
    )
    run(
        "physical_residue_endpoint_dictionary_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionaryAudit.lean",
        ],
    )
    print("FINAL_STATUS=PASS HOT_DEBUG_NOT_EVIDENCE=1", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
