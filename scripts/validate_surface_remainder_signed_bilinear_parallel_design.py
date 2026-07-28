"""Independent structural validator for the signed-bilinear design JSON."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


PI_HI = Fraction(
    31415926535897932384626433832795028841971693993751,
    10**49,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "path",
        nargs="?",
        default="scripts/surface_remainder_signed_bilinear_parallel_design.json",
    )
    args = parser.parse_args()
    payload = json.loads(Path(args.path).read_text(encoding="utf-8"))
    rows = payload.get("rows", [])
    errors: list[str] = []
    if payload.get("scope") != "design-only; no K2 promotion":
        errors.append("scope label changed")
    if payload.get("grid") != 96:
        errors.append("grid is not the frozen design resolution 96")
    if len(rows) != 158:
        errors.append(f"expected 158 rows, got {len(rows)}")
    indices = [int(row.get("index", -1)) for row in rows]
    if indices != list(range(158)):
        errors.append("indices are not exactly 0..157")
    cursor = Fraction(0)
    for expected, row in enumerate(rows):
        try:
            lo, hi = Fraction(row["lo"]), Fraction(row["hi"])
        except (KeyError, ValueError, ZeroDivisionError) as exc:
            errors.append(f"row {expected} has invalid endpoints: {exc}")
            continue
        if lo != cursor:
            errors.append(f"row {expected} starts at {lo}, expected {cursor}")
        if not hi > lo:
            errors.append(f"row {expected} is not increasing")
        cursor = hi
        if not bool(row.get("pass")):
            errors.append(f"row {expected} is not marked pass")
        if not row.get("kd_lower") or not row.get("y3_abs"):
            errors.append(f"row {expected} lacks charged diagnostics")
    if cursor != PI_HI:
        errors.append(f"cover ends at {cursor}, expected pi_hi")
    if int(payload.get("passes", -1)) != 158:
        errors.append("payload pass count is not 158")
    if errors:
        for error in errors:
            print("SIGNED-BILINEAR DESIGN INVALID:", error)
        raise SystemExit(1)
    print("SIGNED-BILINEAR DESIGN VALID: 158 adjacent rows, grid=96, scope=design-only")


if __name__ == "__main__":
    main()
