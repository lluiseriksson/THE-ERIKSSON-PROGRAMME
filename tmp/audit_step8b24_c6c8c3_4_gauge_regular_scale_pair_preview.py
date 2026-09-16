#!/usr/bin/env python3
"""Fail-closed static preview for C6c.8c3--c4 source scale pair."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99SourceGaugeRegularScalePair.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99SourceGaugeRegularScalePairAudit.draft.lean"
PATHS = ROOT / "tmp" / "C6C8C3-4-GAUGE-REGULAR-SCALE-PAIR-PATHS.txt"
EXPECTED = (
    "CMP99SourceGaugeRegularScalePair",
    "cmp99SourceGaugeRegularScalePair",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> None:
    for path in (SOURCE, AUDIT, PATHS):
        if not path.is_file():
            raise SystemExit(f"MISSING={path}")
    source = SOURCE.read_text(encoding="utf-8")
    audit = AUDIT.read_text(encoding="utf-8")
    paths = [line.strip() for line in PATHS.read_text(encoding="utf-8").splitlines()
             if line.strip()]
    if paths != [
        "YangMills/RG/BalabanCMP99SourceGaugeRegularScalePair.lean",
        "YangMills/RG/BalabanCMP99SourceGaugeRegularScalePairAudit.lean",
    ]:
        raise SystemExit("PROMOTION_PATHS_MISMATCH")
    if "PRE-VALIDATION" not in source or "no `.olean`" not in source:
        raise SystemExit("PREVALIDATION_MARKER_MISSING")
    if re.search(r"\b(?:sorry|admit)\b", source):
        raise SystemExit("FORBIDDEN_PLACEHOLDER")
    declarations = re.findall(
        r"(?m)^(?:noncomputable\s+)?(?:structure|def|theorem)\s+([A-Za-z0-9_']+)",
        source,
    )
    readouts = re.findall(
        r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_']+)$", audit
    )
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "private mk ::",
        "transformedSmall",
        "norm_cmp99SourceUbarDeviationLogArg_le_fineRadius",
        "norm_UbarDeviationLogArg_gaugeAct_eq",
        "cmp99SourceBaseCoarseBackground_gaugeAct",
        "cmp99SourceRegionalScaleDataOfDeviationBudget",
        "cmp99PhysicalUbarGaugeConfigOfDeviationBudget_gaugeAct",
        "nextBackground_gaugeAct",
    )
    missing = [item for item in required if item not in source]
    if missing:
        raise SystemExit(f"REQUIRED_MECHANISM_MISSING={missing!r}")
    forbidden = (
        "fineSmall :",
        "fine_small :",
        "(hdev :",  # source endpoint must not take it as an argument
        "hcovariance",
        "nextBackgroundEq",
        "QprimeEq",
    )
    # Local derived `have hdev` is allowed; only parenthesized public arguments
    # are rejected by the explicit tokens above.
    present = [item for item in forbidden if item in source]
    if present:
        raise SystemExit(f"FORBIDDEN_RENAMING_PRESENT={present!r}")
    manifest = "\n".join(f"{p.name}:{digest(p)}" for p in (SOURCE, AUDIT, PATHS))
    print(
        "STEP8B24_C6C8C3_4_GAUGE_REGULAR_SCALE_PAIR_PREVIEW_OK "
        f"files=2 declarations=2 audit_readouts={len(readouts)} "
        f"manifest_sha256={hashlib.sha256(manifest.encode()).hexdigest().upper()}"
    )


if __name__ == "__main__":
    main()
