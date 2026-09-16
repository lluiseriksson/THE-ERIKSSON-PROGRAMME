#!/usr/bin/env python3
"""Fail-closed transcript audit for the promoted Step 8b.24/C6c.2 P1 pair."""

from __future__ import annotations

import argparse
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
BASE = runpy.run_path(
    str(ROOT / "tmp/audit_step8b24_c6c2_p0_executed_notebook.py")
)
SOURCE_SHA = "317b540f57e598f7dea9a41f0c7278f0c674150f"
RUNNER_REV = "step8b24-c6c2-p1-v1"
RUNNER_SHA256 = "66150de9cb5d863eba56ecc13ffbe838f84385814c721efc7facacc9f2f872f1"
SOURCE_STAGE = "01_p1_prefix_poincare_focal"
AUDIT_STAGE = "02_p1_prefix_poincare_audit"
AXIOM_HEADERS = 8


def audit(path: Path) -> str:
    base_audit = BASE["audit"]
    globals_ = base_audit.__globals__
    replacements = {
        "SOURCE_SHA": SOURCE_SHA,
        "RUNNER_REV": RUNNER_REV,
        "RUNNER_SHA256": RUNNER_SHA256,
        "SOURCE_STAGE": SOURCE_STAGE,
        "AUDIT_STAGE": AUDIT_STAGE,
        "AXIOM_HEADERS": AXIOM_HEADERS,
    }
    old = {name: globals_[name] for name in replacements}
    try:
        globals_.update(replacements)
        result = base_audit(path)
    finally:
        globals_.update(old)
    return result.replace(
        "STEP8B24_C6C2_P0_EXECUTED_NOTEBOOK_OK",
        "STEP8B24_C6C2_P1_EXECUTED_NOTEBOOK_OK",
        1,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("executed_notebook", type=Path)
    args = parser.parse_args()
    print(audit(args.executed_notebook))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
