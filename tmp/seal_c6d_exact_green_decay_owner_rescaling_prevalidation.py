#!/usr/bin/env python3
"""Fail-closed selective seal for unified C6d D2 evidence."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_source_separated_ambient_green_prevalidation.py"


def main() -> int:
    spec = importlib.util.spec_from_file_location("c6d_d2_owner_sealer_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_D2_OWNER_SEALER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.VERIFIER_PATH = ROOT / "tmp" / "verify_c6d_exact_green_decay_owner_rescaling_evidence.py"
    module.PATH_MANIFEST = ROOT / "tmp" / "c6d-exact-green-decay-owner-rescaling-prevalidation-paths.txt"
    module.EXPECTED_EVIDENCE_SENTINEL = "C6D_D2_OWNER_RESCALING_EVIDENCE_OK"
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
