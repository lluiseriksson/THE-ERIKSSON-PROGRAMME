#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H4c nearest-contour bound overlay."""

from __future__ import annotations

import json
import time
from pathlib import Path

import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h4c-nearest-bound-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H4C-NEAREST-BOUND-OVERLAY-MANIFEST.json"
SHARED_SHA256 = "D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"

INPUTS = (
    (
        TMP / "BalabanCMP89Eq249NearestCompleteHolderNormalizedBound.draft.lean",
        "222C0061CF07F1F2CDBAA1329C5A4EE33FAE1338D02ECF11985F0828BB70C8CD",
        Path("YangMills/RG/BalabanCMP89Eq249NearestCompleteHolderNormalizedBound.lean"),
        1,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249NearestCompleteHolderNormalizedBoundAudit.draft.lean",
        "9C1B60A56EB202178C7EC8FD83D2BA07CAF15F2A4E66AC75A803478E0518E5D3",
        Path("YangMills/RG/BalabanCMP89Eq249NearestCompleteHolderNormalizedBoundAudit.lean"),
        1,
        True,
    ),
)


def require_semantics(source: str) -> None:
    code = shared.strip_lean_comments(source)
    for forbidden in ("hmassPos", "0 < mass", "sorry", "admit", "axiom "):
        if forbidden in code:
            raise AssertionError(f"H4C_FORBIDDEN={forbidden}")
    required = (
        "cmp89Eq249NearestEndpointHolder_unit",
        "cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest",
        "norm_cmp89Eq249NormalizedCompleteHolderIntegral_physicalFine_le_massUniform",
        "cmp89Eq249NearestEndpointTransport",
        "Real.exp (-(rho * cmp89Eq251DisplacementL1",
        "horientation : ‖orientation‖ = 1",
    )
    for marker in required:
        if marker not in code:
            raise AssertionError(f"H4C_MARKER_MISSING={marker}")


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
        "scope": "H4c one internally selected nearest physical signed-l1 contour",
        "positive_mass_premise": "ABSENT",
        "endpoint_bounds_summed": False,
        "orientation_norm": "EXACTLY_ONE",
        "selected_holder_unit": "DERIVED",
        "source_owner_metric_dictionary": "OPEN",
        "regional_B0": "OPEN",
        "window15": "OPEN",
        "terminal_fields": "OPEN",
        "shared_helper_sha256": SHARED_SHA256,
        "input_sha256": inputs,
        "files": records,
        "declarations": 1,
        "axiom_prints": 1,
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
        "status": "PASS", "compiler_verified": False,
        "files": len(rows), "declarations": 1, "axiom_prints": 1,
        "manifest_sha256": shared.sha256(manifest),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": shared.peak_rss_bytes(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
