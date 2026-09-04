#!/usr/bin/env python3
"""Retained-runtime diagnostic for the arbitrary residue-class dictionary.

This hot runner reuses the graph retained by the preceding generated-residue
cold gate.  It checks out one immutable PRE-VALIDATION commit, verifies the
two Git blob object IDs, runs the textual guards, then the focal and audit.
A PASS is diagnostic only and cannot retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import time


RUNNER_REV = "cmp99-arbitrary-residue-dictionary-hot-v3"
SOURCE_SHA = "440afa7b0883cc77a30f2457c879b025dcde32f1"
ROOT = Path("/content/hrpoly-cmp99-generated-residue-class-cold-v3")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99FlatIntegerResidueClassDictionary.lean":
        "388ceecd4b4c57eea90b30cae03db07997195ea5",
    "YangMills/RG/BalabanCMP99FlatIntegerResidueClassDictionaryAudit.lean":
        "2866cbd7542babb479b9ebb0e84497974edcadf7",
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
    manifest = Path("/content/cmp99-arbitrary-residue-dictionary-hot-v3-paths.txt")
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
        "arbitrary_residue_dictionary_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99FlatIntegerResidueClassDictionary",
        ],
    )
    run(
        "arbitrary_residue_dictionary_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99FlatIntegerResidueClassDictionaryAudit.lean",
        ],
    )
    print("FINAL_STATUS=PASS RUNTIME_RETAINED_FOR_BOUNDED_DEBUG=1", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
