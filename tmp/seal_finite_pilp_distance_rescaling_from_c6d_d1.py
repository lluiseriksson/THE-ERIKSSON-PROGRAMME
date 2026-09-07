#!/usr/bin/env python3
"""Fail-closed distance-rescaling seal from corrected C6d-D1 evidence."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "seal_c6d_source_separated_ambient_green_prevalidation.py"


def main() -> int:
    spec = importlib.util.spec_from_file_location("distance_rescaling_cross_sealer_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("DISTANCE_RESCALING_CROSS_SEALER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.VERIFIER_PATH = (
        ROOT / "tmp" / "verify_finite_pilp_distance_rescaling_from_c6d_d1_evidence.py"
    )
    module.PATH_MANIFEST = (
        ROOT / "tmp" / "finite-pilp-distance-rescaling-prevalidation-paths.txt"
    )
    module.EXPECTED_EVIDENCE_SENTINEL = (
        "DISTANCE_RESCALING_FROM_C6D_D1_EVIDENCE_OK"
    )
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
