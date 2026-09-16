#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H3a/H3b physical mass-uniform contour overlay."""

from __future__ import annotations

import json
import time
from pathlib import Path

import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h3-mass-uniform-contour-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H3-MASS-UNIFORM-CONTOUR-OVERLAY-MANIFEST.json"
SHARED_SHA256 = "D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"

INPUTS = (
    (
        TMP / "BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicity.draft.lean",
        "469141764CD7B59DC1DA88FBACE880DBDF107EE24C50C5D4F80C23DBA1D1E2BD",
        Path("YangMills/RG/BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicity.lean"),
        7,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicityAudit.draft.lean",
        "47F161912BF553541ADDF118BE771BD95818CA5E3CDA841C55F0FA93EC78CE8A",
        Path("YangMills/RG/BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicityAudit.lean"),
        7,
        True,
    ),
    (
        TMP / "BalabanCMP89Eq251CompleteHolderMassUniformHolomorphy.draft.lean",
        "F4DE9EE49DAEFE33D3D62323EB0801348A832606A054488A54306012F447D67A",
        Path("YangMills/RG/BalabanCMP89Eq251CompleteHolderMassUniformHolomorphy.lean"),
        2,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq251CompleteHolderMassUniformHolomorphyAudit.draft.lean",
        "90FC872A8F86669C0D2F980F4DB69715F58B5CD06C8A9312BDE134F5CBD89344",
        Path("YangMills/RG/BalabanCMP89Eq251CompleteHolderMassUniformHolomorphyAudit.lean"),
        2,
        True,
    ),
    (
        TMP / "BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShift.draft.lean",
        "1A0218BDF18BBC86437AEAC3DFCFA2453DE0125B8F6B553ED4164B8E17CD68CA",
        Path("YangMills/RG/BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShift.lean"),
        1,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShiftAudit.draft.lean",
        "4A558E8D29C68DAD11F1CA7B50330BF71AEC18D786F9ABD5C8906698817581BE",
        Path("YangMills/RG/BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShiftAudit.lean"),
        1,
        True,
    ),
)


def require_semantics(periodicity: str, holomorphy: str, shift: str) -> None:
    pcode = shared.strip_lean_comments(periodicity)
    hcode = shared.strip_lean_comments(holomorphy)
    scode = shared.strip_lean_comments(shift)
    for code in (pcode, hcode, scode):
        for forbidden in ("hmassPos", "0 < mass", "sorry", "admit", "axiom "):
            if forbidden in code:
                raise AssertionError(f"H3_MASS_UNIFORM_FORBIDDEN={forbidden}")
    required_h = (
        "differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius_massUniform",
        "cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform",
        "cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_boundarySeam_massUniform",
        "cmp89Eq251DisplayedDomain_of_boundaryFace_massUniform",
        "cmp89Eq249PhysicalFineLatticeDisplacement",
    )
    required_p = (
        "cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor",
        "cmp89Eq251ComplexDisplayedIntegrand_physicalFineHolderPeriodShift",
        "cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolderPeriodShift_of_nonzero",
        "holderU transportU : Fin d → ℤ",
        "cmp89Eq249PhysicalFineLatticeDisplacement",
    )
    required_s = (
        "intervalIntegral_cmp89Eq251ComplexStabilizedIntegrand_coordinateShift_massUniform",
        "himag : ∀ k, |(z k).im| ≤ rho",
        "DifferentiableOn ℂ f",
        "physicalFineHolder_boundarySeam_massUniform",
        "cmp89Eq249PhysicalFineLatticeDisplacement",
    )
    for marker in required_p:
        if marker not in pcode:
            raise AssertionError(f"H3_PERIODICITY_MARKER_MISSING={marker}")
    for marker in required_h:
        if marker not in hcode:
            raise AssertionError(f"H3_HOLOMORPHY_MARKER_MISSING={marker}")
    for marker in required_s:
        if marker not in scode:
            raise AssertionError(f"H3_SHIFT_MARKER_MISSING={marker}")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    if shared.sha256(Path(shared.__file__).read_bytes()) != SHARED_SHA256:
        raise AssertionError("SHARED_HELPER_DRIFT")
    rows: list[tuple[Path, bytes]] = []
    inputs: dict[str, str] = {}
    for draft, expected, target, count, audit in INPUTS:
        content = shared.promote(shared.read_pinned(draft, expected), count, audit)
        rows.append((target, content))
        inputs[draft.name] = expected
    require_semantics(
        rows[0][1].decode(), rows[2][1].decode(), rows[4][1].decode()
    )
    records = [
        {"path": p.as_posix(), "sha256": shared.sha256(b), "bytes": len(b)}
        for p, b in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "fine-lattice complete Holder periodicity plus H3a mass-uniform holomorphy/seam and H3b one-coordinate shift",
        "fine_lattice_displacements": "BOTH_LITERAL",
        "positive_mass_premise": "ABSENT",
        "polydisc_gate": "ALL_COORDINATES",
        "product_telescope": "OPEN",
        "integral_bound": "OPEN",
        "owner_dictionary": "OPEN",
        "regional_B0": "OPEN",
        "window15": "OPEN",
        "terminal_fields": "OPEN",
        "shared_helper_sha256": SHARED_SHA256,
        "input_sha256": inputs,
        "files": records,
        "declarations": 10,
        "axiom_prints": 10,
    }
    return rows, payload


def main() -> int:
    started = time.perf_counter()
    rows, payload = build_payload()
    for relative, content in rows:
        target = OVERLAY / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
        if target.read_bytes() != content:
            raise AssertionError(f"POST_WRITE_MISMATCH={relative.as_posix()}")
    manifest = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode()
    MANIFEST.write_bytes(manifest)
    print(json.dumps({
        "status": "PASS",
        "compiler_verified": False,
        "files": len(rows),
        "declarations": 10,
        "axiom_prints": 10,
        "manifest_sha256": shared.sha256(manifest),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": shared.peak_rss_bytes(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
