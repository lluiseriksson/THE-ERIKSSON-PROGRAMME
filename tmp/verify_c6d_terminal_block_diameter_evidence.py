#!/usr/bin/env python3
"""Fail-closed verifier specialization for terminal-block diameter."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_terminal_diameter_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_TERMINAL_DIAMETER_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    base = load_base()
    module = "BalabanCMP99SourceActiveRegionTerminalBlockDiameter"
    base.SOURCE_SHA = "dc227762c8873441f5865d4b51f831f9dd017ae9"
    base.RUNNER_REV = "c6d-terminal-block-diameter-v1"
    base.SOURCE_BLOBS_COUNT = 3
    base.SOURCE_BLOBS_SHA256 = (
        "5BE5F32E9B7240AB514829760978ED3F355435B13850851896376217B9702EE6"
    )
    base.NOTEBOOK_CELL_SOURCE_SHA256 = (
        "804E07637BE8479F643E287E523550602D7140C2D6EF839FA9CD54B97955EEE7"
    )
    base.SUCCESS_SENTINEL = "C6D_TERMINAL_BLOCK_DIAMETER_EVIDENCE_OK"
    base.MODULES = [module]
    base.AUDIT_STAGES = {
        module: "01_cmp99sourceactiveregionterminalblockdiameter_audit",
    }
    base.EXPECTED_AXIOM_HEADERS = {module: 5}
    base.QUEUE_STAGES = [
        "01_cmp99sourceactiveregionterminalblockdiameter_focal",
        "01_cmp99sourceactiveregionterminalblockdiameter_audit",
        "02_c6d_terminal_block_diameter_yang_mills_core_root",
    ]
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
