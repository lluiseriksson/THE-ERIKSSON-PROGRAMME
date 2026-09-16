#!/usr/bin/env python3
"""Prepare the deterministic PRE-VALIDATION H5d1--H5d3 overlay."""

from __future__ import annotations

import json
import re
import time
from pathlib import Path

import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h5-generated-holder-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H5-GENERATED-HOLDER-OVERLAY-MANIFEST.json"
SHARED_SHA256 = "D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"

INPUTS = (
    (
        TMP / "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsum.draft.lean",
        "E8B8618F48FA0D2D43ACCB211C585BF3A866F57F9CC9B18417696F50026D677A",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsum.lean"),
        2,
        False,
    ),
    (
        TMP / "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsumAudit.draft.lean",
        "BFF46296DC597E755A5BFA2962D4486A674ABE4DFA037FA82BF6A6117B1A02DA",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsumAudit.lean"),
        2,
        True,
    ),
    (
        TMP / "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder.draft.lean",
        "1F81EEE5722064193487F70FF5EE383246284619CD76CBD8B97AFF4772CA9BD7",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder.lean"),
        3,
        False,
    ),
    (
        TMP / "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderAudit.draft.lean",
        "CAFFE5E2923A335A0F92E311584911DC06F5B45FA7A5A0CCA37DA1444C87391B",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderAudit.lean"),
        3,
        True,
    ),
)


def require_shared_helper() -> None:
    actual = shared.sha256(Path(shared.__file__).read_bytes())
    if actual != SHARED_SHA256:
        raise AssertionError(f"SHARED_HELPER_DRIFT={actual}")


def require_generated_holder_semantics(tsum_source: str, point_source: str) -> None:
    tsum_code = shared.strip_lean_comments(tsum_source)
    point_code = shared.strip_lean_comments(point_source)
    required_tsum = (
        "(derivMu bondNu : Fin 4)",
        "tsum_cmp99SourceSeparatedGeneratedFlatPhysicalDerivative_shift_eq_forward",
        "tsum_cmp89Eq249PhysicalHolderIntegral_eq_xiRpowInv_mul_derivativeDiff",
        "(((xi ^ alpha : ℝ) : ℂ)⁻¹)",
        "hsource.tsum_sub hforward",
    )
    required_point = (
        "cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative",
        "cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_eq_series_smul",
        "cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_eq_tsumIntegral_smul",
        "(derivMu bondNu : Fin 4)",
        "x.shift bondNu",
        "x.shift derivMu",
        "hsource, htarget, hreindex, hintegral",
        "(((xi ^ alpha : ℝ) : ℂ)⁻¹)",
    )
    for marker in required_tsum:
        if marker not in tsum_code:
            raise AssertionError(f"H5D_TSUM_MARKER_MISSING={marker}")
    for marker in required_point:
        if marker not in point_code:
            raise AssertionError(f"H5D_POINT_MARKER_MISSING={marker}")
    combined = tsum_code + point_code
    for forbidden in ("‖", "root_small", "outer_small", "TermSource"):
        if forbidden in combined:
            raise AssertionError(f"H5D_BOUND_OR_TERMINAL_TOKEN={forbidden}")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    require_shared_helper()
    rows: list[tuple[Path, bytes]] = []
    inputs: dict[str, str] = {}
    for draft, expected, target, count, audit in INPUTS:
        content = shared.promote(shared.read_pinned(draft, expected), count, audit)
        rows.append((target, content))
        inputs[draft.name] = expected
    require_generated_holder_semantics(
        rows[0][1].decode("utf-8"), rows[2][1].decode("utf-8")
    )
    records = [
        {"path": path.as_posix(), "sha256": shared.sha256(content), "bytes": len(content)}
        for path, content in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "H5d1 residue reindex, H5d2 complete-integral tsum, H5d3 point-source identity",
        "derivative_and_bond_directions": "INDEPENDENT",
        "derivative_xi_inverse": "LITERAL_BEFORE_NORM",
        "holder_xi_rpow_inverse": "LITERAL_BEFORE_NORM",
        "endpoint_bounds_subtracted": False,
        "owner_transport": "OPEN",
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
