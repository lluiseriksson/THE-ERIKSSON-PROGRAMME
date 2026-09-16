#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H3c complete Holder telescope overlay."""

from __future__ import annotations

import json
import time
from pathlib import Path

import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h3c-product-telescope-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H3C-PRODUCT-TELESCOPE-OVERLAY-MANIFEST.json"
SHARED_SHA256 = "D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"

INPUTS = (
    (
        TMP / "BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescope.draft.lean",
        "09A0AFFCECE4A978E94EF50A269BDCDD63CB3328612DEAE4DCADA34E71840B11",
        Path("YangMills/RG/BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescope.lean"),
        5,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescopeAudit.draft.lean",
        "99E6B95D1BF6409AE778E0729A35F9A2FE48C34FABC1CEE1790B7B2D45276FA2",
        Path("YangMills/RG/BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescopeAudit.lean"),
        5,
        True,
    ),
)


def require_semantics(source: str) -> None:
    code = shared.strip_lean_comments(source)
    for forbidden in ("hmassPos", "0 < mass", "sorry", "admit", "axiom "):
        if forbidden in code:
            raise AssertionError(f"H3C_FORBIDDEN={forbidden}")
    required = (
        "cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand",
        "cmp89Eq249PhysicalFineLatticeDisplacement xi holderU",
        "cmp89Eq249PhysicalFineLatticeDisplacement xi transportU",
        "SignType.sign (transportDisplacement nu)",
        "intervalIntegral_cmp89Eq251ComplexStabilizedIntegrand_coordinateShift_massUniform",
        "integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_zero_eq_four",
        "integral_cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_eq_signed_massUniform",
    )
    for marker in required:
        if marker not in code:
            raise AssertionError(f"H3C_MARKER_MISSING={marker}")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    if shared.sha256(Path(shared.__file__).read_bytes()) != SHARED_SHA256:
        raise AssertionError("SHARED_HELPER_DRIFT")
    rows: list[tuple[Path, bytes]] = []
    inputs: dict[str, str] = {}
    for draft, expected, target, count, audit in INPUTS:
        content = shared.promote(shared.read_pinned(draft, expected), count, audit)
        rows.append((target, content))
        inputs[draft.name] = expected
    require_semantics(rows[0][1].decode())
    records = [
        {"path": p.as_posix(), "sha256": shared.sha256(b), "bytes": len(b)}
        for p, b in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "H3c complete physical fine-lattice Holder four-coordinate product telescope",
        "positive_mass_premise": "ABSENT",
        "holder_numerator": "UNSPLIT",
        "contour_direction": "TRANSPORT_DISPLACEMENT_ONLY",
        "normalized_integral_bound": "OPEN",
        "owner_dictionary": "OPEN",
        "regional_B0": "OPEN",
        "window15": "OPEN",
        "terminal_fields": "OPEN",
        "shared_helper_sha256": SHARED_SHA256,
        "input_sha256": inputs,
        "files": records,
        "declarations": 5,
        "axiom_prints": 5,
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
        "declarations": 5,
        "axiom_prints": 5,
        "manifest_sha256": shared.sha256(manifest),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": shared.peak_rss_bytes(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
