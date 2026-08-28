#!/usr/bin/env python3
"""Fail-closed verifier for the C6d ambient/compression cold archive."""

from __future__ import annotations

import importlib.util
from pathlib import Path


BASE_PATH = Path(__file__).with_name(
    "verify_c6d_source_coercivity_green_evidence.py"
)
spec = importlib.util.spec_from_file_location(
    "c6d_source_coercivity_green_evidence_base", BASE_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_AMBIENT_COMPRESSION_VERIFIER_BASE_IMPORT_FAILED")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

base.SOURCE_SHA = "89cb81e0416e6a6fbc66540a8019471bbbcafed5"
base.RUNNER_REV = "c6d-ambient-compression-cold-v2-streaming-heartbeat"
base.SOURCE_BLOBS_COUNT = 24
base.SOURCE_BLOBS_SHA256 = (
    "2F56F15797920921018B7A02E6B0196A4827738BB7F395B6263EFDB5A372654B"
)
base.NOTEBOOK_CELL_SOURCE_SHA256 = (
    "DD92E153B4F4882FF8F46BFBA225D1D7BF726910F14DC8FD9891D84029F967AC"
)

base.MODULES = [
    "BalabanCMP99RegionalDirichletGaugePrecisionCompression",
    "BalabanCMP99SourceActiveRegionFullCompanion",
    "BalabanCMP99SourceGeneratedMassCompression",
    "BalabanCMP99SourceGeneratedPhysicalPrecisionCompression",
    "BalabanCMP99SourceActiveRegionFullCompanionPrecision",
    "BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision",
    "BalabanCMP99ActiveGaugeRegionReindex",
    "BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision",
    "BalabanCMP99ActiveGaugeRegionReindexGreen",
    "BalabanCMP99SourceActiveRegionFullCompanionZeroDepth",
    "BalabanCMP99SourceActiveRegionFullCompanionZeroDepthGreen",
]
base.EXPECTED_AXIOM_HEADERS = [2, 5, 3, 3, 6, 8, 10, 8, 4, 3, 6]


def expected_queue_stages() -> list[str]:
    result = [
        "c6d_ambient_compression_manifest_gate",
        "c6d_ambient_compression_prepare_build_dirs",
    ]
    for index, module in enumerate(base.MODULES, start=1):
        stem = f"c6d_ambient_compression_{index:02d}_{module.lower()}"
        result.extend([stem + "_source", stem + "_audit"])
    result.append("c6d_ambient_compression_root")
    return result


base.expected_queue_stages = expected_queue_stages


if __name__ == "__main__":
    raise SystemExit(base.main())
