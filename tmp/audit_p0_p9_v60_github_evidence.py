#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v60 artifact ZIP."""

from pathlib import Path

import audit_p0_p9_v56_github_evidence as core
import github_p0_p9_v60_driver as contract


core.contract = contract
core.CONTROL_SHA = "b2b3d507c18c7caa17a3db00bb4e70101eddabb5"
core.DRIVER_SHA256 = "0D1386AB4F631227A8D9C0F3D730FEC97809790EE3C4CB18E81A1B57E53B5004"
core.DRIVER_PATH = "control/tmp/github_p0_p9_v60_driver.py"
core.ARCHIVE_NAME = "p0-p9-v60-evidence.tar.gz"
core.RESULT_MARKER = "P0_P9_V60_GITHUB_EVIDENCE_OK"

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
