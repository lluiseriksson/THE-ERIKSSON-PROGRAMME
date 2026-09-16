#!/usr/bin/env python3
"""Fail-closed static preview for C6c.8c5."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99SourceWeightedPhysicalGaugeCovariance.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99SourceWeightedPhysicalGaugeCovarianceAudit.draft.lean"
PATHS = ROOT / "tmp" / "C6C8C5-SOURCE-WEIGHTED-PHYSICAL-GAUGE-COVARIANCE-PATHS.txt"
EXPECTED = ("cmp99SourceTransportedBlockAverageCLM_weightedPhysicalTransport_gaugeAct",)


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
        "YangMills/RG/BalabanCMP99SourceWeightedPhysicalGaugeCovariance.lean",
        "YangMills/RG/BalabanCMP99SourceWeightedPhysicalGaugeCovarianceAudit.lean",
    ]:
        raise SystemExit("PROMOTION_PATHS_MISMATCH")
    if "PRE-VALIDATION" not in source or "no `.olean`" not in source:
        raise SystemExit("PREVALIDATION_MARKER_MISSING")
    if re.search(r"\b(?:sorry|admit)\b", source):
        raise SystemExit("FORBIDDEN_PLACEHOLDER")
    declarations = re.findall(
        r"(?m)^(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_']+)", source
    )
    readouts = re.findall(
        r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_']+)$", audit
    )
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "cmp99SourceTransportedBlockAverageCLM Omega",
        "cmp99SourceWeightedPhysicalTransport rho",
        "cmp99SourceBlockAverageWeight M d",
        "cmp99BlockContainedContourSystem",
        "cmp99AdjointBlockAverageCLM_blockContainedContour_gaugeAct",
    )
    missing = [item for item in required if item not in source]
    if missing:
        raise SystemExit(f"REQUIRED_MECHANISM_MISSING={missing!r}")
    forbidden = (
        "hcovariance",
        "transportEq",
        "QprimeEq",
        "fineSmall",
        "GreenU =",
    )
    present = [item for item in forbidden if item in source]
    if present:
        raise SystemExit(f"FORBIDDEN_RENAMING_PRESENT={present!r}")
    manifest = "\n".join(f"{p.name}:{digest(p)}" for p in (SOURCE, AUDIT, PATHS))
    print(
        "STEP8B24_C6C8C5_SOURCE_WEIGHTED_PHYSICAL_GAUGE_PREVIEW_OK "
        f"files=2 declarations=1 audit_readouts={len(readouts)} "
        f"manifest_sha256={hashlib.sha256(manifest.encode()).hexdigest().upper()}"
    )


if __name__ == "__main__":
    main()
