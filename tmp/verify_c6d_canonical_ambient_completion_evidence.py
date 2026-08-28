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
    module = "BalabanCMP99ActiveRegionCanonicalAmbientCompletion"
    base.SOURCE_SHA = "4b52bea54b5928139614fe842a2736b296358808"
    base.RUNNER_REV = "c6d-canonical-ambient-completion-v1"
    base.SOURCE_BLOBS_COUNT = 3
    base.SOURCE_BLOBS_SHA256 = (
        "7D142C6E70FB4D2B5B9AE5667F00EC0A6776B581D8F5997CA665041392C72B53"
    )
    base.NOTEBOOK_CELL_SOURCE_SHA256 = (
        "5BE4E50F77DEF9DEE3C744B2D4334330849407A0B0453F400D7FC97BDC9A86FB"
    )
    base.SUCCESS_SENTINEL = "C6D_CANONICAL_AMBIENT_COMPLETION_EVIDENCE_OK"
    base.MODULES = [module]
    base.AUDIT_STAGES = {
        module: "01_cmp99activeregioncanonicalambientcompletion_audit"
    }
    base.EXPECTED_AXIOM_HEADERS = {module: 8}
    base.QUEUE_STAGES = [
        "01_cmp99activeregioncanonicalambientcompletion_focal",
        "01_cmp99activeregioncanonicalambientcompletion_audit",
        "02_c6d_canonical_ambient_completion_yang_mills_core_root",
    ]
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
