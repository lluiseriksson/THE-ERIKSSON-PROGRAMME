#!/usr/bin/env python3
"""Fail-closed selective seal for the uniform/localized source-flow B0 gate."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_source_separated_ambient_green_prevalidation.py"


def main() -> int:
    spec = importlib.util.spec_from_file_location("uniform_b0_sealer_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("UNIFORM_B0_SEALER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.VERIFIER_PATH = (
        ROOT / "tmp" / "verify_source_flow_uniform_localized_b0_colab_evidence.py"
    )
    module.PATH_MANIFEST = (
        ROOT / "tmp" / "source-flow-uniform-localized-b0-prevalidation-paths.txt"
    )
    module.EXPECTED_EVIDENCE_SENTINEL = (
        "SOURCE_FLOW_UNIFORM_LOCALIZED_B0_COLAB_EVIDENCE_OK"
    )
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
