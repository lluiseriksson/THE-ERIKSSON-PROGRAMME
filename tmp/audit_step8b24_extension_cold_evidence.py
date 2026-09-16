#!/usr/bin/env python3
"""Fail-closed validator for the Step 8b.24 S1--C6b cold artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import runpy
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b24_extension_terminal_workflow.py")
)
BASE = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b23_ae_cold_evidence.py")
)
_GLOBALS = BASE["validate"].__globals__
_PREREQUISITES, _VALIDATION = WORKFLOW["source_scope"]()
_GLOBALS.update(
    GENERATOR={"source_paths": lambda: _PREREQUISITES + _VALIDATION},
    BRICKS=WORKFLOW["VALIDATION_BRICKS"],
    INNER_ARCHIVE="step8b24-extension-evidence.tar.gz",
    EXPECTED_FILES=80,
    EXPECTED_BRICKS=18,
    EXPECTED_AXIOMS=53,
)

MATHLIB_SHA = _GLOBALS["MATHLIB_SHA"]
TOOLCHAIN_URL = _GLOBALS["TOOLCHAIN_URL"]
TOOLCHAIN_ASSET_SHA256 = _GLOBALS["TOOLCHAIN_ASSET_SHA256"]
INNER_ARCHIVE = _GLOBALS["INNER_ARCHIVE"]
stage_rows = BASE["stage_rows"]
validate = BASE["validate"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", required=True, type=Path)
    parser.add_argument("--outer-zip", required=True, type=Path)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--workflow-sha", required=True)
    args = parser.parse_args()
    result = validate(
        args.artifact_root, args.outer_zip, args.source_sha, args.workflow_sha
    )
    print("STEP8B24_EXTENSION_COLD_EVIDENCE_OK")
    print(f"source_sha={result['source_sha']}")
    print(f"workflow_sha={result['workflow_sha']}")
    print("prerequisites=44")
    print("validation_files=36")
    print("new_bricks=17")
    print("validated_pairs=18")
    print("stages=36")
    print("axiom_blocks=53")
    print(f"manifest_entries={result['manifest_entries']}")
    print(f"inner_members={result['inner_members']}")
    print(f"outer_members={result['outer_members']}")
    print(f"inner_archive_sha256={result['inner_archive_sha256']}")
    print(f"outer_artifact_zip_sha256={result['outer_artifact_zip_sha256']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        OSError,
        ValueError,
        tarfile.TarError,
        zipfile.BadZipFile,
        json.JSONDecodeError,
    ) as error:
        print(f"STEP8B24_EXTENSION_COLD_EVIDENCE_FAIL: {error}")
        raise SystemExit(1)
