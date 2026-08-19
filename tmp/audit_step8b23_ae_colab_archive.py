#!/usr/bin/env python3
"""Audit a diagnostic Step 8b.23 Units A--E Colab archive.

This composes the generic retained-stage-log checks with an independent
Git-object reconstruction of the 36 source blobs, two reproducers and the
38-stage queue.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "3e59c4a2c96804c5548961c922c6348bb9b0269e"
RUNNER_REV = "step8b23-ae-v43"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
EVIDENCE_ROOT = "hrpoly-step8b23-ae-evidence"


base = runpy.run_path(str(ROOT / "tmp" / "audit_p0_p9_evidence_archive.py"))
audit_base = base["audit"]
base_globals = audit_base.__globals__
base_globals["SOURCE_SHA"] = SOURCE_SHA
base_globals["RUNNER_REV"] = RUNNER_REV
base_globals["MATHLIB_SHA"] = MATHLIB_SHA
base_globals["EVIDENCE_ROOT"] = EVIDENCE_ROOT

generator = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_ae_validation_runner.py")
)
BRICKS: tuple[tuple[str, int], ...] = generator["BRICKS"]
SOURCE_PATHS: list[str] = generator["source_paths"]()
REPROS: tuple[tuple[str, str], ...] = generator["REPROS"]


def git_blob(path: str) -> bytes:
    child = subprocess.run(
        [
            "git", "-c", "safe.directory=*", "cat-file", "blob",
            f"{SOURCE_SHA}:{path}",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise ValueError(
            f"git blob unavailable: {path}: "
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout


def expected_blobs() -> dict[str, str]:
    return {
        path: hashlib.sha256(git_blob(path)).hexdigest()
        for path in SOURCE_PATHS + [path for _, path in REPROS]
    }


def expected_queue() -> list[str]:
    stages: list[str] = [stage for stage, _ in REPROS]
    for index, (module, _) in enumerate(BRICKS, start=1):
        slug = module.removeprefix("Balaban").lower()
        stages.extend((f"{index:02d}_{slug}_focal", f"{index:02d}_{slug}_audit"))
    return stages


def audit(path: Path) -> str:
    retained = audit_base(path)
    members = base["read_regular_members"](path)
    evidence = json.loads(
        members[f"{EVIDENCE_ROOT}/evidence.json"].decode("utf-8")
    )
    measured_blobs = evidence.get("source_blobs")
    wanted_blobs = expected_blobs()
    if measured_blobs != wanted_blobs:
        raise ValueError("source blob map differs from independent Git objects")
    records = evidence["records"]
    repro_stages = {stage for stage, _ in REPROS}
    measured_queue = [
        row["stage"] for row in records
        if isinstance(row, dict)
        and (
            row.get("stage", "") in repro_stages
            or re.fullmatch(
                r"[0-9]{2}_.+_(?:focal|audit)", row.get("stage", "")
            )
        )
    ]
    wanted_queue = expected_queue()
    if measured_queue != wanted_queue[:len(measured_queue)]:
        raise ValueError("queue is not the frozen stop-on-first-error prefix")
    if evidence["status"] == "PASS" and measured_queue != wanted_queue:
        raise ValueError(
            f"PASS queue length={len(measured_queue)}, expected={len(wanted_queue)}"
        )
    return retained.replace(
        "P0_P9_EVIDENCE_ARCHIVE_OK",
        "STEP8B23_AE_COLAB_ARCHIVE_OK",
        1,
    ) + f" source_blobs={len(wanted_blobs)} queue_stages={len(measured_queue)}"


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: audit_step8b23_ae_colab_archive.py ARCHIVE.tar.gz")
    try:
        print(audit(Path(sys.argv[1])))
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"STEP8B23_AE_COLAB_ARCHIVE_FAIL {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
