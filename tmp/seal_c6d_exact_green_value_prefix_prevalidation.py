#!/usr/bin/env python3
"""Fail-closed selective seal for the exact C6d Green value prefix."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_source_separated_ambient_green_prevalidation.py"


def main() -> int:
    spec = importlib.util.spec_from_file_location("c6d_value_prefix_sealer_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_VALUE_PREFIX_SEALER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.VERIFIER_PATH = ROOT / "tmp" / "verify_c6d_exact_green_value_prefix_evidence.py"
    module.PATH_MANIFEST = ROOT / "tmp" / "c6d-exact-green-value-prefix-prevalidation-paths.txt"
    module.EXPECTED_EVIDENCE_SENTINEL = "C6D_EXACT_GREEN_VALUE_PREFIX_EVIDENCE_OK"
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
