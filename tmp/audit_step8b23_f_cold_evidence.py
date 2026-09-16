#!/usr/bin/env python3
"""Fail-closed validator for the Step 8b.23 Unit-F cold artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import runpy
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
F_GENERATOR = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_f_validation_runner.py")
)
BASE = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b23_ae_cold_evidence.py")
)
_GLOBALS = BASE["validate"].__globals__
_AE, _UNIT_F = F_GENERATOR["source_paths"]()
_GLOBALS.update(
    GENERATOR={"source_paths": lambda: _AE + _UNIT_F},
    BRICKS=F_GENERATOR["BRICKS"],
    INNER_ARCHIVE="step8b23-f-evidence.tar.gz",
    EXPECTED_FILES=44,
    EXPECTED_BRICKS=4,
    EXPECTED_AXIOMS=49,
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
    print("STEP8B23_F_COLD_EVIDENCE_OK")
    print(f"source_sha={result['source_sha']}")
    print(f"workflow_sha={result['workflow_sha']}")
    print("prerequisites=36")
    print("unit_f_files=8")
    print("bricks=4")
    print("stages=8")
    print("axiom_blocks=49")
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
        print(f"STEP8B23_F_COLD_EVIDENCE_FAIL: {error}")
        raise SystemExit(1)
