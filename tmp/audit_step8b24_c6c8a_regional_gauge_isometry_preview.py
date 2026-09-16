#!/usr/bin/env python3
"""Fail-closed static preview for the C6c.8a regional gauge-isometry pair."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99RegionalGaugeIsometry.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99RegionalGaugeIsometryAudit.draft.lean"
PATHS = ROOT / "tmp" / "C6C8A-REGIONAL-GAUGE-ISOMETRY-PATHS.txt"

EXPECTED = (
    "cmp99FineGaugeLinearIsometryEquiv",
    "cmp99FineGaugeLinearIsometryEquiv_apply",
    "cmp99RegionalFineGaugeLinearIsometryEquiv",
    "cmp99RegionalFineGaugeLinearIsometryEquiv_apply",
    "cmp99RegionalFineGaugeLinearIsometryEquiv_eq_gaugeAct",
    "cmp99RegionalFineGaugeLinearIsometryEquiv_symm_apply",
    "norm_cmp99RegionalFineGaugeAct_eq",
    "support_cmp99RegionalFineGaugeAct_eq",
    "extendZeroZeroCLM_cmp99RegionalFineGaugeAct",
    "restrictZeroCLM_cmp99FineGaugeLinearIsometryEquiv",
    "cmp99RegionalCoarseGaugeLinearIsometryEquiv",
    "cmp99RegionalCoarseGaugeLinearIsometryEquiv_apply",
    "cmp99RegionalCoarseGaugeLinearIsometryEquiv_eq_gaugeAct",
    "cmp99RegionalCoarseGaugeLinearIsometryEquiv_symm_apply",
    "norm_cmp99RegionalCoarseGaugeAct_eq",
    "support_cmp99RegionalCoarseGaugeAct_eq",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> None:
    for path in (SOURCE, AUDIT, PATHS):
        if not path.is_file():
            raise SystemExit(f"MISSING={path}")

    source = SOURCE.read_text(encoding="utf-8")
    audit = AUDIT.read_text(encoding="utf-8")
    paths = [line.strip() for line in PATHS.read_text(encoding="utf-8").splitlines()
             if line.strip()]

    if "PRE-VALIDATION" not in source or ".olean` has been materialized" not in source:
        raise SystemExit("PREVALIDATION_MARKER_MISSING")
    if "sorry" in source or "admit" in source:
        raise SystemExit("FORBIDDEN_PLACEHOLDER")
    if paths != [
        "YangMills/RG/BalabanCMP99RegionalGaugeIsometry.lean",
        "YangMills/RG/BalabanCMP99RegionalGaugeIsometryAudit.lean",
    ]:
        raise SystemExit("PROMOTION_PATHS_MISMATCH")

    declarations = re.findall(
        r"(?m)^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
        r"(?:def|theorem)\s+([A-Za-z0-9_']+)",
        source,
    )
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"DECLARATION_MISMATCH={declarations!r}")

    readouts = re.findall(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_']+)$", audit)
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"AUDIT_READOUT_MISMATCH={readouts!r}")

    required = (
        "LinearIsometryEquiv.piLpCongrRight 2",
        "rho.adLinearIsometryEquiv",
        "cmp99RegionalFineGaugeAct",
        "cmp99RegionalCoarseGaugeAct",
        "extendZeroZeroCLM",
        "restrictZeroCLM",
        "Function.support",
    )
    missing = [needle for needle in required if needle not in source]
    if missing:
        raise SystemExit(f"REQUIRED_MECHANISM_MISSING={missing!r}")

    forbidden = (
        "GreenU =",
        "precisionU =",
        "operatorCovariance",
        "finalBound",
    )
    present = [needle for needle in forbidden if needle in source]
    if present:
        raise SystemExit(f"FORBIDDEN_RENAMING_PRESENT={present!r}")

    manifest = "\n".join(
        f"{path.name}:{sha256(path)}" for path in (SOURCE, AUDIT, PATHS)
    ).encode("utf-8")
    digest = hashlib.sha256(manifest).hexdigest().upper()
    print(
        "STEP8B24_C6C8A_REGIONAL_GAUGE_ISOMETRY_PREVIEW_OK "
        f"files=2 declarations={len(EXPECTED)} audit_readouts={len(readouts)} "
        f"manifest_sha256={digest}"
    )


if __name__ == "__main__":
    main()
