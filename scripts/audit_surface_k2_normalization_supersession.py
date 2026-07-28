"""Audit the exact manifest scope of the withdrawn K2 normalization blob."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from run_record_archive import MANIFEST_DIR, iter_auditable_run_records

ROOT = Path(__file__).resolve().parents[1]
TARGET_PATH = "scripts/surface_remainder_delta0_series_design.py"
WITHDRAWN_SHA256_LF = (
    "3bf631c2efca03284d2e1a0b6308a9536792f16b8003637114da143adbb9e063"
)

# This inventory is defined by the committed evidence tree.  A local
# ``surface-remainder-k2-hybrid009-current-20260717T085239Z.json`` was never
# versioned and no longer validates against the corrected normalization
# blobs, so it is deliberately not promoted into this set post hoc.
EXPECTED_CURRENT_WITHDRAWALS = {
    "surface-remainder-k2-endpoint-20260712T125718Z.json",
    "surface-remainder-k2-r4-regular008-0-13-20260714T050257Z.json",
    "surface-remainder-k2-r4-regular008-13-25-20260714T050257Z.json",
    "surface-remainder-k2-r4-regular008-25-38-20260714T050257Z.json",
    "surface-remainder-k2-r4-regular008-38-50-20260714T050257Z.json",
    "surface-remainder-k2-r4-regular008-50-98-20260714T061148Z.json",
    "surface-remainder-k2-r4-regular008-98-146-20260714T061148Z.json",
    "surface-remainder-k2-r4-regular008-146-152-20260714T061148Z.json",
    "surface-remainder-k2-r4-regular008-152-158-20260714T061149Z.json",
    "surface-remainder-k2-r4-v2-regular005-part1-20260713T144316Z.json",
    "surface-remainder-k2-r4-v2-regular005-part2-20260713T145533Z.json",
}


def contains_withdrawn_dependency(value: Any) -> bool:
    """Recognize both manifest dependency schemas used in this repository."""

    if isinstance(value, dict):
        if value.get("path") == TARGET_PATH and WITHDRAWN_SHA256_LF in {
            value.get("sha256"),
            value.get("sha256_lf"),
        }:
            return True
        if value.get(TARGET_PATH) == WITHDRAWN_SHA256_LF:
            return True
        return any(contains_withdrawn_dependency(item) for item in value.values())
    if isinstance(value, list):
        return any(contains_withdrawn_dependency(item) for item in value)
    return False


def audit(manifest_directory: Path) -> tuple[list[Path], list[Path]]:
    affected: list[Path] = []
    current: list[Path] = []
    if manifest_directory.resolve() == MANIFEST_DIR.resolve():
        paths = [
            path for _, path in iter_auditable_run_records("*.json")
        ]
    else:
        paths = sorted(manifest_directory.glob("*.json"))
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not contains_withdrawn_dependency(data):
            continue
        affected.append(path)
        if data.get("status") == "current":
            current.append(path)
    actual_current = {path.name for path in current}
    if actual_current != EXPECTED_CURRENT_WITHDRAWALS:
        missing = sorted(EXPECTED_CURRENT_WITHDRAWALS - actual_current)
        unexpected = sorted(actual_current - EXPECTED_CURRENT_WITHDRAWALS)
        raise ValueError(
            "withdrawal scope mismatch: "
            f"missing={missing!r} unexpected={unexpected!r}"
        )
    return affected, current


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest-directory",
        type=Path,
        default=ROOT / "run-manifests",
    )
    args = parser.parse_args()
    affected, current = audit(args.manifest_directory.resolve())
    print(f"WITHDRAWN_SHA256_LF {WITHDRAWN_SHA256_LF}")
    print(f"AFFECTED_MANIFESTS {len(affected)}")
    print(f"CURRENT_WITHDRAWALS {len(current)}")
    for path in current:
        print(f"CURRENT_WITHDRAWN {path.name}")
    print("SURFACE K2 NORMALIZATION SUPERSESSION AUDIT PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
