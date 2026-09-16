#!/usr/bin/env python3
"""Fail-closed verifier specialization for kernel-distance rescaling."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "ebeea96235ac89a0a9598593855119d4bfe3ea04"
RUNNER_REV = "finite-pilp-distance-rescaling-v1"
SOURCE_BLOBS_COUNT = 3
SOURCE_BLOBS_SHA256 = "EB0737E2ECB5D72F4ED9128D209ED01CDC7DEFA68DA14865945288BBB59D878E"
NOTEBOOK_CELL_SOURCE_SHA256 = "9992F38CB0B6D930587E9823F78E80AFA957650A75E499D05307ACF0915028EF"
SUCCESS_SENTINEL = "DISTANCE_RESCALING_EVIDENCE_OK"
MODULES = ["FinitePiLpTypedKernelDistanceRescaling"]
AUDIT_STAGES = {
    MODULES[0]: "01_finitepilptypedkerneldistancerescaling_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 1}
QUEUE_STAGES = [
    "01_finitepilptypedkerneldistancerescaling_focal",
    "01_finitepilptypedkerneldistancerescaling_audit",
    "02_finite_pilp_distance_rescaling_yang_mills_core_root",
]


def load_base():
    spec = importlib.util.spec_from_file_location("distance_rescaling_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("DISTANCE_RESCALING_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    base = load_base()
    base.SOURCE_SHA = SOURCE_SHA
    base.RUNNER_REV = RUNNER_REV
    base.SOURCE_BLOBS_COUNT = SOURCE_BLOBS_COUNT
    base.SOURCE_BLOBS_SHA256 = SOURCE_BLOBS_SHA256
    base.NOTEBOOK_CELL_SOURCE_SHA256 = NOTEBOOK_CELL_SOURCE_SHA256
    base.SUCCESS_SENTINEL = SUCCESS_SENTINEL
    base.MODULES = MODULES
    base.AUDIT_STAGES = AUDIT_STAGES
    base.EXPECTED_AXIOM_HEADERS = EXPECTED_AXIOM_HEADERS
    base.QUEUE_STAGES = QUEUE_STAGES
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
