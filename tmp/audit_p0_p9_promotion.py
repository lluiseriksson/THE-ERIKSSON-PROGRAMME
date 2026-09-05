#!/usr/bin/env python3
"""Extended static promotion gate for the full C6c.2 P0--P9 chain."""

from __future__ import annotations

import audit_p0_p5_promotion as base


SOURCES = base.SOURCES + (
    (
        "P7SourceSeparatedAmbientPrefixPrecision.lean",
        "BalabanCMP89SourceSeparatedAmbientPrefixPrecision.lean",
    ),
    (
        "P8SourceSeparatedRegionalPrefixGreen.lean",
        "BalabanCMP96SourceSeparatedRegionalPrefixGreen.lean",
    ),
    (
        "P9SourceSeparatedPrefixCombesThomas.lean",
        "BalabanCMP89SourceSeparatedPrefixCombesThomas.lean",
    ),
)
P3_AGGREGATE = base.P3_AGGREGATE
DECL = base.DECL
PRINT = base.PRINT
IMPORT = base.IMPORT
promoted_name = base.promoted_name
ALREADY_PROMOTED_SOURCES = frozenset(
    {"P0CanonicalPrefixTower.lean", "P1CoefficientMonotonicity.lean"}
)
ALREADY_PROMOTED_FILES = frozenset(
    {
        "P0CanonicalPrefixTower.lean",
        "P0CanonicalPrefixTowerAudit.lean",
        "P1CoefficientMonotonicity.lean",
        "P1CoefficientMonotonicityAudit.lean",
    }
)


def main() -> int:
    base.SOURCES = SOURCES
    base.SCOPE_LABEL = "P0_P9"
    base.DISPLAY_LABEL = "P0--P9"
    base.PATH_LIST_NAME = "P0-P9-SCRATCH-PATHS.txt"
    base.MANIFEST_NAME = "P0-P9-SCRATCH-MANIFEST.sha256"
    base.ALREADY_PROMOTED_SOURCES = ALREADY_PROMOTED_SOURCES
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
