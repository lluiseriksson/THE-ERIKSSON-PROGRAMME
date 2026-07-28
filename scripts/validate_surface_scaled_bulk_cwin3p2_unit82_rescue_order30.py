"""Validate the quarantined unit-82 order-30 rescue pair."""

from __future__ import annotations

import hashlib
import re
from fractions import Fraction
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
PROD = ROOT / "scripts/surface_scaled_bulk_unit82_rescue_order30.txt"
REPLAY = ROOT / "scripts/surface_scaled_bulk_unit82_rescue_order30_rerun.txt"
EXPECTED_DEPS = (
    "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)
ROW_RE = re.compile(r"^trow\s+(\d+)\s+(\S+)\s+(\S+)\s+upper\s+(\S+)")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT82 RESCUE ORDER30"
    assert "config CWIN 3/2 beta_order 30 t_order 35 min_dt 1/100000 prec 220" in lines
    assert "beta_domain 275/4 1101/16" in lines
    assert lines[-1] == "SCOPE quarantined unit82 rescue; no G2/G6 promotion"
    deps = {line.split()[1]: line.split()[3]
            for line in lines if line.startswith("dependency ")}
    assert set(deps) == set(EXPECTED_DEPS)
    for rel in EXPECTED_DEPS:
        assert deps[rel] == sha(ROOT / rel)
    rows = []
    for line in lines:
        m = ROW_RE.match(line)
        if m:
            rows.append((int(m.group(1)), Fraction(m.group(2)), Fraction(m.group(3)), arb(m.group(4))))
    assert len(rows) == 167
    assert [r[0] for r in rows] == list(range(167))
    assert rows[0][1] == Fraction(3, 5)
    assert rows[-1][2] == Fraction(31415927, 10_000_000) - Fraction(3, 2) / Fraction(1101, 16)
    for prev, cur in zip(rows, rows[1:]):
        assert prev[2] == cur[1]
    assert all(upper < 0 for _, _, _, upper in rows)
    assert lines[-2] == "SCALED BULK SIGN ROW PASS"
    return len(rows)


def main() -> None:
    assert PROD.read_bytes() == REPLAY.read_bytes()
    rows = validate(PROD)
    validate(REPLAY)
    print("UNIT82 ORDER30 RESCUE VALIDATION PASS rows", rows)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO H_tail/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
