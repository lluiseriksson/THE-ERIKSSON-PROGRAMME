#!/usr/bin/env python3
"""Fail-closed verifier for C6d D2 plus owner-distance rescaling."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "1d7b33059eb3964a3ff99003869be84ec0806288"
RUNNER_REV = "c6d-d2-owner-rescaling-v2"
SOURCE_BLOBS_COUNT = 7
SOURCE_BLOBS_SHA256 = "CEB109D80B85244596642D56BC1E7628F44FF7F032A2E3DDE9E3EF37A7EFB347"
NOTEBOOK_CELL_SOURCE_SHA256 = "26C1719954A8B7B39222D03F37A5397ECD1B943CD46580E6A8D66D2DD3A34B69"
SUCCESS_SENTINEL = "C6D_D2_OWNER_RESCALING_EVIDENCE_OK"
MODULES = [
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay",
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth",
    "BalabanCMP99Eq360C6dSourceSeparatedOwnerDecayRescaling",
]
AUDIT_STAGES = {
    MODULES[0]: "01_cmp99eq360c6dsourceseparatedambientgreendecay_audit",
    MODULES[1]: "02_cmp99eq360c6dsourceseparatedambientgreendecayzerodepth_audit",
    MODULES[2]: "03_cmp99eq360c6dsourceseparatedownerdecayrescaling_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 4, MODULES[1]: 3, MODULES[2]: 1}
QUEUE_STAGES = [
    "01_cmp99eq360c6dsourceseparatedambientgreendecay_focal",
    "01_cmp99eq360c6dsourceseparatedambientgreendecay_audit",
    "02_cmp99eq360c6dsourceseparatedambientgreendecayzerodepth_focal",
    "02_cmp99eq360c6dsourceseparatedambientgreendecayzerodepth_audit",
    "03_cmp99eq360c6dsourceseparatedownerdecayrescaling_focal",
    "03_cmp99eq360c6dsourceseparatedownerdecayrescaling_audit",
    "04_c6d_d2_owner_rescaling_yang_mills_core_root",
]


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_d2_owner_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_D2_OWNER_VERIFIER_BASE_IMPORT_FAILED")
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
