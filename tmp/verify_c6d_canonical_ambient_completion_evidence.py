#!/usr/bin/env python3
"""Fail-closed verifier specialization for canonical ambient completion."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_completion_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    base = load_base()
    generic = "BalabanCMP99ActiveRegionCanonicalAmbientCompletion"
    integration = "BalabanCMP99Eq360C6dCanonicalAmbientCompletion"
    base.SOURCE_SHA = "4dc3a90e0b8516baae16568889832d0e15b6cd72"
    base.RUNNER_REV = "c6d-canonical-ambient-completion-v3"
    base.SOURCE_BLOBS_COUNT = 5
    base.SOURCE_BLOBS_SHA256 = (
        "5EEC561C45051147ADBD93B576D3E20C2C79D454F030F1F8FE2024A9146B4528"
    )
    base.NOTEBOOK_CELL_SOURCE_SHA256 = (
        "76C27FFF7009BA723E8AE48181D4EB2326DBFF292A15921941FEBEE439955717"
    )
    base.SUCCESS_SENTINEL = "C6D_CANONICAL_AMBIENT_COMPLETION_EVIDENCE_OK"
    base.MODULES = [generic, integration]
    base.AUDIT_STAGES = {
        generic: "01_cmp99activeregioncanonicalambientcompletion_audit",
        integration: "02_cmp99eq360c6dcanonicalambientcompletion_audit",
    }
    base.EXPECTED_AXIOM_HEADERS = {generic: 9, integration: 1}
    base.QUEUE_STAGES = [
        "01_cmp99activeregioncanonicalambientcompletion_focal",
        "01_cmp99activeregioncanonicalambientcompletion_audit",
        "02_cmp99eq360c6dcanonicalambientcompletion_focal",
        "02_cmp99eq360c6dcanonicalambientcompletion_audit",
        "03_c6d_canonical_ambient_completion_yang_mills_core_root",
    ]
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
