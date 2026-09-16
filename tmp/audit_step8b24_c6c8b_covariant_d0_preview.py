#!/usr/bin/env python3
"""Fail-closed static preview for the ambient C6c.8b D0 intertwiner."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99CovariantD0GaugeIntertwiner.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99CovariantD0GaugeIntertwinerAudit.draft.lean"
PATHS = ROOT / "tmp" / "C6C8B-COVARIANT-D0-GAUGE-INTERTWINER-PATHS.txt"

EXPECTED = (
    "continuousLinearMap_adjoint_intertwines_of_isometries",
    "continuousLinearMap_adjoint_comp_self_intertwines_of_isometries",
    "cmp99PhysicalBondGaugeLinearIsometryEquiv",
    "cmp99PhysicalBondGaugeLinearIsometryEquiv_apply",
    "cmp99PhysicalBondGaugeLinearIsometryEquiv_symm_apply",
    "norm_cmp99PhysicalBondGaugeLinearIsometryEquiv_apply",
    "support_cmp99PhysicalBondGaugeLinearIsometryEquiv_apply",
    "covariantD0CLM_gaugeAct",
    "cmp99ActiveRegionSourceCovariantD0CLM_gaugeAct",
    "cmp99ActiveRegionSourceCovariantD0CLM_comp_gaugeIsometry",
    "cmp99ActiveRegionSourceCovariantLaplacian_gaugeAct",
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
        "YangMills/RG/BalabanCMP99CovariantD0GaugeIntertwiner.lean",
        "YangMills/RG/BalabanCMP99CovariantD0GaugeIntertwinerAudit.lean",
    ]:
        raise SystemExit("PROMOTION_PATHS_MISMATCH")
    if "PRE-VALIDATION" not in source or "No `.olean` has been materialized" not in source:
        raise SystemExit("PREVALIDATION_MARKER_MISSING")
    if re.search(r"\b(?:sorry|admit)\b", source):
        raise SystemExit("FORBIDDEN_PLACEHOLDER")
    declarations = re.findall(
        r"(?m)^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
        r"(?:def|theorem)\s+([A-Za-z0-9_']+)", source
    )
    readouts = re.findall(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_']+)$", audit)
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "GaugeConfig.gaugeAct u U",
        "covariantD0CLM rho",
        "cmp99FineGaugeLinearIsometryEquiv rho u",
        "cmp99PhysicalBondGaugeLinearIsometryEquiv rho u",
        "rho.ad_mul",
        "rho.ad_inv_apply_ad",
        "u b.1",
        "extendZeroZeroCLM_cmp99RegionalFineGaugeAct",
        "cmp99ActiveRegionSourceCovariantD0CLM Omega rho",
        "continuousLinearMap_adjoint_comp_self_intertwines_of_isometries",
        "cmp99ActiveRegionSourceCovariantLaplacian Omega rho",
    )
    missing = [item for item in required if item not in source]
    if missing:
        raise SystemExit(f"REQUIRED_MECHANISM_MISSING={missing!r}")
    forbidden = (
        "hcovariance",
        "operatorCovariance",
        "precisionU =",
        "GreenU =",
    )
    present = [item for item in forbidden if item in source]
    if present:
        raise SystemExit(f"FORBIDDEN_RENAMING_PRESENT={present!r}")
    manifest = "\n".join(f"{p.name}:{digest(p)}" for p in (SOURCE, AUDIT, PATHS))
    print(
        "STEP8B24_C6C8B_COVARIANT_D0_PREVIEW_OK "
        f"files=2 declarations={len(EXPECTED)} audit_readouts={len(readouts)} "
        f"manifest_sha256={hashlib.sha256(manifest.encode()).hexdigest().upper()}"
    )


if __name__ == "__main__":
    main()
