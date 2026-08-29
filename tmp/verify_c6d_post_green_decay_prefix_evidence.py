#!/usr/bin/env python3
"""Fail-closed verifier specialization for the post-Green decay prefix."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "a554cba0c398e816316e53d76a4fe08bf379d931"
RUNNER_REV = "c6d-post-green-decay-prefix-v1"
SOURCE_BLOBS_COUNT = 5
SOURCE_BLOBS_SHA256 = "F38E990C5E4BFC087D281996685AB12E56CA5D3F7E861E1F4C3F95DA66866640"
NOTEBOOK_CELL_SOURCE_SHA256 = "4170A98E3AAD5BE7F022216FE46EB9098C2A34A7FCDDAC9C5FCCFF5E66CCDD9B"
SUCCESS_SENTINEL = "C6D_POST_GREEN_DECAY_PREFIX_EVIDENCE_OK"
MODULES = [
    "BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay",
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric",
]
AUDIT_STAGES = {
    MODULES[0]: "01_cmp99sourceactiveregionfullcompanionprecisiondecay_audit",
    MODULES[1]: "02_cmp99eq360c6dsourceseparatedambientmetric_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 7, MODULES[1]: 3}
QUEUE_STAGES = [
    "01_cmp99sourceactiveregionfullcompanionprecisiondecay_focal",
    "01_cmp99sourceactiveregionfullcompanionprecisiondecay_audit",
    "02_cmp99eq360c6dsourceseparatedambientmetric_focal",
    "02_cmp99eq360c6dsourceseparatedambientmetric_audit",
    "03_c6d_post_green_decay_prefix_yang_mills_core_root",
]


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_post_green_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_POST_GREEN_VERIFIER_BASE_IMPORT_FAILED")
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
