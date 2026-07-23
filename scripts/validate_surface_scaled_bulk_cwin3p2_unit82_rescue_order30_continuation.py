"""Validate the two remaining unit-82 order-30 rescue slices."""

from __future__ import annotations

import hashlib
import re
from fractions import Fraction
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
SLICES = {
    "slice2": (Fraction(1101, 16), Fraction(1103, 16), 172),
    "slice3": (Fraction(1103, 16), Fraction(69), 167),
}
ROW_RE = re.compile(r"^trow\s+(\d+)\s+(\S+)\s+(\S+)\s+upper\s+(\S+)")
DEPS = (
    "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_continuation.py",
    "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(label: str, lo: Fraction, hi: Fraction, expected_rows: int) -> int:
    prod = ROOT / f"scripts/surface_scaled_bulk_unit82_rescue_order30_{label}.txt"
    replay = ROOT / f"scripts/surface_scaled_bulk_unit82_rescue_order30_{label}_rerun.txt"
    assert prod.read_bytes() == replay.read_bytes()
    lines = prod.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT82 RESCUE ORDER30 SLICE"
    assert "config CWIN 3/2 beta_order 30 t_order 35 min_dt 1/100000 prec 220" in lines
    assert f"beta_domain {lo} {hi}" in lines
    assert lines[-1] == "SCOPE quarantined unit82 rescue continuation; no G2/G6 promotion"
    deps = {line.split()[1]: line.split()[3]
            for line in lines if line.startswith("dependency ")}
    assert set(deps) == set(DEPS)
    for rel in DEPS:
        assert deps[rel] == sha(ROOT / rel)
    rows = []
    for line in lines:
        m = ROW_RE.match(line)
        if m:
            rows.append((int(m.group(1)), Fraction(m.group(2)), Fraction(m.group(3)), arb(m.group(4))))
    assert len(rows) == expected_rows
    assert [r[0] for r in rows] == list(range(expected_rows))
    assert rows[0][1] == Fraction(3, 5)
    assert rows[-1][2] == Fraction(31415927, 10_000_000) - Fraction(3, 2) / hi
    assert all(upper < 0 for _, _, _, upper in rows)
    return len(rows)


def main() -> None:
    total = sum(check(label, lo, hi, expected) for label, (lo, hi, expected) in SLICES.items())
    print("UNIT82 ORDER30 CONTINUATION VALIDATION PASS rows", total)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO H_tail/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
