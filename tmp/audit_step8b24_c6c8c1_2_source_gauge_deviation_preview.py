#!/usr/bin/env python3
"""Fail-closed static preview for C6c.8c1--c2."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99SourceGaugeDeviationTransport.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99SourceGaugeDeviationTransportAudit.draft.lean"
PATHS = ROOT / "tmp" / "C6C8C1-2-SOURCE-GAUGE-DEVIATION-PATHS.txt"

EXPECTED = (
    "norm_sun_conj_matrix_eq",
    "norm_UbarDeviationLogArg_gaugeAct_eq",
    "cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar",
    "cmp99PhysicalUbarGaugeConfigOfDeviationBudget_gaugeAct",
    "cmp99SourceBaseCoarseBackground_gaugeAct",
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
        "YangMills/RG/BalabanCMP99SourceGaugeDeviationTransport.lean",
        "YangMills/RG/BalabanCMP99SourceGaugeDeviationTransportAudit.lean",
    ]:
        raise SystemExit("PROMOTION_PATHS_MISMATCH")
    if "PRE-VALIDATION" not in source or "no `.olean`" not in source:
        raise SystemExit("PREVALIDATION_MARKER_MISSING")
    if re.search(r"\b(?:sorry|admit)\b", source):
        raise SystemExit("FORBIDDEN_PLACEHOLDER")
    declarations = re.findall(
        r"(?m)^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
        r"(?:def|theorem)\s+([A-Za-z0-9_']+)", source
    )
    readouts = re.findall(
        r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_']+)$", audit
    )
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "norm_sun_conj_matrix_le p X",
        "norm_sun_conj_matrix_le p⁻¹ Y",
        "coe_sun_inv_eq_conjTranspose",
        "UbarDeviationLogArg_gaugeAct",
        "matrixRealizationSUN_val",
        "cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe",
        "Finset.smul_sum",
        "Ubar_gaugeAct",
        "B.δ_lt_one",
        ".map_reverse",
        "cmp99SourceParallelTransportPath",
        ".holonomy_gaugeAct u A",
        "coarseTransform u",
        "cmp99SourceBaseCoarseBackground",
    )
    missing = [item for item in required if item not in source]
    if missing:
        raise SystemExit(f"REQUIRED_MECHANISM_MISSING={missing!r}")
    forbidden = (
        "fineSmall",
        "fine_small",
        "hcovariance",
        "operatorCovariance",
        "GreenU =",
    )
    present = [item for item in forbidden if item in source]
    if present:
        raise SystemExit(f"FORBIDDEN_RENAMING_PRESENT={present!r}")
    manifest = "\n".join(f"{p.name}:{digest(p)}" for p in (SOURCE, AUDIT, PATHS))
    print(
        "STEP8B24_C6C8C1_2_SOURCE_GAUGE_DEVIATION_PREVIEW_OK "
        f"files=2 declarations={len(EXPECTED)} audit_readouts={len(readouts)} "
        f"manifest_sha256={hashlib.sha256(manifest.encode()).hexdigest().upper()}"
    )


if __name__ == "__main__":
    main()
