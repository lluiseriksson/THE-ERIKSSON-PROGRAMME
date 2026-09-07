#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v58 artifact ZIP."""

from pathlib import Path

import audit_p0_p9_v56_github_evidence as core
import github_p0_p9_v58_driver as contract


core.contract = contract
core.CONTROL_SHA = "3f98585e3e94762f67c4340b2458dd216d61ecf9"
core.DRIVER_SHA256 = "DB0A7D94F0A688C2801AD4454B6FCFA3CBFC7E83337F392D9CD443A2ECA9D24C"
core.DRIVER_PATH = "control/tmp/github_p0_p9_v58_driver.py"
core.ARCHIVE_NAME = "p0-p9-v58-evidence.tar.gz"
core.RESULT_MARKER = "P0_P9_V58_GITHUB_EVIDENCE_OK"

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
