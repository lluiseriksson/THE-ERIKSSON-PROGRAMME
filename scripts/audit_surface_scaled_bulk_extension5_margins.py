"""Extract certified sign margins from the quarantined extension-5 archive.

This is a read-only diagnostic.  It does not promote G2/G6 or H_tail.  Each
``upper [mid +/- radius]`` row is parsed with Decimal arithmetic and the
reported margin is ``-(mid + radius)``.  The result is useful for sizing a
future absolute relay, but is not itself a relay certificate.
"""

from __future__ import annotations

import json
import re
from decimal import Decimal, getcontext
from pathlib import Path

from run_record_archive import frozen_record_path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = frozen_record_path(
    "surface-scaled-bulk-cwin3p2-mid-cover-order24-repair-extension5-20260723.json"
)
ROW_RE = re.compile(
    r"^trow\s+(?P<row>\d+)\s+\S+\s+\S+\s+upper\s+"
    r"\[(?P<mid>[+-]?[0-9.]+e[+-]?\d+)\s+\+/-\s+"
    r"(?P<rad>[+-]?[0-9.]+e[+-]?\d+)\]$"
)


def main() -> None:
    getcontext().prec = 120
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    all_rows: list[tuple[int, int, Decimal]] = []
    print("EXTENSION5 SIGN-MARGIN AUDIT (QUARANTINED; NO PROMOTION)")
    for unit in manifest["units"]:
        path = ROOT / unit["production"]["path"]
        rows: list[tuple[int, Decimal]] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            m = ROW_RE.match(line)
            if not m:
                continue
            upper = Decimal(m.group("mid")) + Decimal(m.group("rad"))
            if upper >= 0:
                raise SystemExit(f"nonnegative upper in unit {unit['index']}: {line}")
            rows.append((int(m.group("row")), -upper))
        if not rows:
            raise SystemExit(f"no rows parsed in {path}")
        row, margin = min(rows, key=lambda x: x[1])
        all_rows.extend((unit["index"], row, m) for row, m in rows)
        print(
            f"unit {unit['index']:02d} rows {len(rows):3d} "
            f"min_margin {margin} at trow {row}"
        )
    unit, row, margin = min(all_rows, key=lambda x: x[2])
    print(f"GLOBAL MIN_MARGIN {margin} unit {unit} trow {row}")
    print("MARGINS ARE ONLY FOR THE NORMALIZED SIGN PREDICATE W^J")
    print("RELAY STATUS: RELAY_LEMMA_UNPROVED; H_tail/G2/G6 UNCHANGED")


if __name__ == "__main__":
    main()
