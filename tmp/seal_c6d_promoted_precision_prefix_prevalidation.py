#!/usr/bin/env python3
"""Seal only the promoted C6d precision-prefix files certified in one archive."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_next_real_slice_prevalidation.py"


def load():
    spec = importlib.util.spec_from_file_location("c6d_promoted_prefix_seal_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PROMOTED_PREFIX_SEAL_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.CONTRACT_PATH = (
        ROOT / "tmp" / "verify_c6d_promoted_precision_prefix_contract.py"
    )
    module.ARCHIVE_VERIFIER = (
        ROOT / "tmp" / "verify_c6d_promoted_precision_prefix_archive.py"
    )
    module.SOURCE_SHA = "fe17c932cd712ba2952c501f7944b9317943af06"
    module.RUNNER_REV = "c6d-promoted-precision-prefix-v1"
    module.EXPECTED_DECLARATIONS = 27
    return module


if __name__ == "__main__":
    raise SystemExit(load().main())
