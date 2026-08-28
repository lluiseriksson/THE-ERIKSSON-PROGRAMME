#!/usr/bin/env python3
"""Verify the promoted C6d precision-prefix archive with the shared verifier."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_next_real_slice_archive.py"
CONTRACT = ROOT / "tmp" / "verify_c6d_promoted_precision_prefix_contract.py"


def load():
    spec = importlib.util.spec_from_file_location("c6d_promoted_prefix_archive_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PROMOTED_PREFIX_ARCHIVE_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.CONTRACT_PATH = CONTRACT
    return module


if __name__ == "__main__":
    raise SystemExit(load().main())
