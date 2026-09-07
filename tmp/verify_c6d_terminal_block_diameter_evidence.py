#!/usr/bin/env python3
"""Fail-closed verifier specialization for terminal-block diameter."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "a2715bf8cdae841dfc313ea9f34a23fe1d2bdd35"
RUNNER_REV = "c6d-terminal-block-diameter-v4"
SOURCE_BLOBS_COUNT = 3
SOURCE_BLOBS_SHA256 = (
    "BCFB607FC8A23F8544A7DDCCC46A460848CB6656B5ED57CD4837055E1FE270CB"
)
NOTEBOOK_CELL_SOURCE_SHA256 = (
    "C3C91B1DE9CB8F511B9F94B141AB0A09ABB3D3FA341F61E93B5E22B920B378AF"
)
SUCCESS_SENTINEL = "C6D_TERMINAL_BLOCK_DIAMETER_EVIDENCE_OK"
MODULES = ["BalabanCMP99SourceActiveRegionTerminalBlockDiameter"]
AUDIT_STAGES = {
    MODULES[0]: "01_cmp99sourceactiveregionterminalblockdiameter_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 4}
QUEUE_STAGES = [
    "01_cmp99sourceactiveregionterminalblockdiameter_focal",
    "01_cmp99sourceactiveregionterminalblockdiameter_audit",
    "02_c6d_terminal_block_diameter_yang_mills_core_root",
]


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_terminal_diameter_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_TERMINAL_DIAMETER_VERIFIER_BASE_IMPORT_FAILED")
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
