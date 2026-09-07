#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v59 artifact ZIP."""

from pathlib import Path

import audit_p0_p9_v56_github_evidence as core
import github_p0_p9_v59_driver as contract


core.contract = contract
core.CONTROL_SHA = "8ec221d815bfde3610fb101e95dde736be403b2b"
core.DRIVER_SHA256 = "5BED2CE9A301A4BEC9B92623DD40E209E9E9F7678A6E6255492701EAF278CE38"
core.DRIVER_PATH = "control/tmp/github_p0_p9_v59_driver.py"
core.ARCHIVE_NAME = "p0-p9-v59-evidence.tar.gz"
core.RESULT_MARKER = "P0_P9_V59_GITHUB_EVIDENCE_OK"

CONTROL_SHA = core.CONTROL_SHA
DRIVER_SHA256 = core.DRIVER_SHA256
DRIVER_PATH = core.DRIVER_PATH
ARCHIVE_NAME = core.ARCHIVE_NAME
RESULT_MARKER = core.RESULT_MARKER
sha256 = core.sha256
audit = core.audit


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("artifact_zip", type=Path)
    args = parser.parse_args()
    print(audit(args.artifact_zip.resolve()))
