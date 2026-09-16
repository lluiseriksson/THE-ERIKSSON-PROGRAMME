#!/usr/bin/env python3
"""Deterministic promotion preview for the full C6c.2 P0--P9 chain."""

from __future__ import annotations

from pathlib import Path

import audit_p0_p5_promotion_preview as preview
import audit_p0_p9_promotion as scope


ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    preview.scope = scope
    preview.PATHS = ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt"
    preview.RAW_MANIFEST = ROOT / "tmp" / "P0-P9-SCRATCH-MANIFEST.sha256"
    preview.EXPECTED_RAW_MANIFEST_SHA256 = (
        "A5506D94E4198A5E6AC5B69DC32E9E1D1BD5B814EA9CF047A428E190C7A111CD"
    )
    preview.SCOPE_LABEL = "P0_P9"
    preview.EXPECTED_DECLARATIONS = 182
    preview.EXPECTED_PROMOTED_MODULES = 39
    return preview.main()


if __name__ == "__main__":
    raise SystemExit(main())
