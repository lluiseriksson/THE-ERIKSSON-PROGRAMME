#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v61 artifact ZIP."""

from pathlib import Path

import audit_p0_p9_v56_github_evidence as core
import github_p0_p9_v61_driver as contract


core.contract = contract
core.CONTROL_SHA = "1491463c7f385e7e7dcfce7f953da8c0f599dbf9"
core.DRIVER_SHA256 = "3C605C7C58E3E955A53F248616D0F0EFF5A76A5A2FD6A3066E60FECF067E5D4D"
core.DRIVER_PATH = "control/tmp/github_p0_p9_v61_driver.py"
core.ARCHIVE_NAME = "p0-p9-v61-evidence.tar.gz"
core.RESULT_MARKER = "P0_P9_V61_GITHUB_EVIDENCE_OK"

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
