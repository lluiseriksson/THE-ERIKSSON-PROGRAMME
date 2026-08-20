#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v62 artifact ZIP."""

from pathlib import Path

import audit_p0_p9_v56_github_evidence as core
import github_p0_p9_v62_driver as contract


core.contract = contract
core.CONTROL_SHA = "7e98e26e49e5a5d55e25d5ff71d9a84b601a4c04"
core.DRIVER_SHA256 = "8AA76CAF3782908F5E141A598D5F9E90A9F2BD8786A55DD300653DB609974FCE"
core.DRIVER_PATH = "control/tmp/github_p0_p9_v62_driver.py"
core.ARCHIVE_NAME = "p0-p9-v62-evidence.tar.gz"
core.RESULT_MARKER = "P0_P9_V62_GITHUB_EVIDENCE_OK"

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
