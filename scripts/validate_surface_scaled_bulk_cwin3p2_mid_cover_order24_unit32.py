"""Independent validator for the isolated order-24 repair of unit 32.

The result is intentionally quarantined: it repairs one failed local cover
unit but does not establish the complete finite-beta union or the relay.
"""

from fractions import Fraction
import hashlib
from pathlib import Path
import re

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "surface_scaled_bulk_mid_cover_32_225_4_113_2"
DRIVER = "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair.py"
EXPECTED_DOMAIN = (Fraction(225, 4), Fraction(113, 2))
EXPECTED_ROWS = 168
ROW_RE = re.compile(r"^trow (\d+) (\S+) (\S+) upper (.+)$")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path):
    lines = path.read_text(encoding="utf-8").replace("\r\n", "\n").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR"
    assert "config CWIN 3/2 beta_order 24 t_order 25 min_dt 1/100000 prec 180" in lines
    domain = next(line for line in lines if line.startswith("beta_domain "))
    _, lo, hi = domain.split()
    assert (Fraction(lo), Fraction(hi)) == EXPECTED_DOMAIN
    rows = []
    for line in lines:
        match = ROW_RE.match(line)
        if match:
            index, lo, hi, upper = match.groups()
            rows.append((int(index), Fraction(lo), Fraction(hi), arb(upper)))
    assert len(rows) == EXPECTED_ROWS
    assert [row[0] for row in rows] == list(range(EXPECTED_ROWS))
    assert all(row[3].is_finite() and row[3].upper() < 0 for row in rows)
    assert rows[0][1] == Fraction(3, 5)
    for previous, current in zip(rows, rows[1:]):
        assert previous[2] == current[1]
    assert "SCALED BULK SIGN ROW PASS" in lines
    assert "SCOPE quarantined order24 repair; no G2/G6 promotion" in lines
    return lines


def main() -> int:
    production = parse(BASE.with_suffix(".txt"))
    replay = parse(BASE.with_name(BASE.name + "_rerun").with_suffix(".txt"))
    assert production == replay
    print("ORDER24 UNIT32 VALIDATION PASS")
    print("ROWS", EXPECTED_ROWS)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("SHA256", sha256(BASE.with_suffix(".txt")))
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
