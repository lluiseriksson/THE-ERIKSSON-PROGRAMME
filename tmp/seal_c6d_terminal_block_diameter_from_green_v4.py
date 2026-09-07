#!/usr/bin/env python3
"""Fail-closed selective diameter seal from the Green-v4 cold root."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_source_separated_ambient_green_prevalidation.py"


def main() -> int:
    spec = importlib.util.spec_from_file_location("diameter_green_v4_sealer_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("DIAMETER_GREEN_V4_SEALER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.VERIFIER_PATH = (
        ROOT / "tmp" / "verify_c6d_terminal_block_diameter_from_green_v4_evidence.py"
    )
    module.PATH_MANIFEST = (
        ROOT / "tmp" / "c6d-terminal-block-diameter-prevalidation-paths.txt"
    )
    module.EXPECTED_EVIDENCE_SENTINEL = (
        "C6D_TERMINAL_BLOCK_DIAMETER_FROM_GREEN_V4_EVIDENCE_OK"
    )
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
