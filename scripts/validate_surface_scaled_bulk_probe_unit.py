"""Text/Arb integrity audit for one exploratory scaled-bulk unit.

This validator checks only that a production/replay pair is byte-identical,
has the registered beta/t domains, has adjacent rational t rows, and records
strictly negative Arb upper endpoints.  It deliberately does not attach a
manifest or promote G2/G6.
"""

from fractions import Fraction
import hashlib
from pathlib import Path
import re

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
UNITS = (("probe-current-wide-97_2-971_20", Fraction(97, 2),
          Fraction(971, 20)),)
CWIN = Fraction(3, 2)
PI_UP = Fraction(31415927, 10000000)
TROW = re.compile(r"^trow (\d+) (\S+) (\S+) upper (.+)$")


def main() -> int:
    total_rows = 0
    for unit, lo_beta, hi_beta in UNITS:
        production = ROOT / "scripts" / f"surface_scaled_bulk_{unit}.txt"
        replay = ROOT / "scripts" / f"surface_scaled_bulk_{unit}_rerun.txt"
        assert production.read_bytes() == replay.read_bytes()
        lines = production.read_text(encoding="utf-8").splitlines()
        dependency = next(line for line in lines
                          if line.startswith("dependency scripts/certify_bulk_beta_taylor_arb.py"))
        expected_hash = dependency.rsplit(" ", 1)[-1]
        actual_hash = hashlib.sha256(
            (ROOT / "scripts/certify_bulk_beta_taylor_arb.py").read_bytes()
        ).hexdigest()
        assert expected_hash == actual_hash, (expected_hash, actual_hash)
        assert f"beta_domain {lo_beta} {hi_beta}" in lines
        t_hi = PI_UP - CWIN / hi_beta
        assert f"t_domain {Fraction(3,5)} {t_hi}" in lines
        rows = []
        for line in lines:
            match = TROW.fullmatch(line)
            if match:
                index, lo, hi, upper = match.groups()
                rows.append((int(index), Fraction(lo), Fraction(hi), arb(upper)))
        assert rows and [row[0] for row in rows] == list(range(len(rows)))
        cursor = Fraction(3, 5)
        for _, lo, hi, upper in rows:
            assert lo == cursor and lo < hi
            assert upper.upper() < 0, (lo, hi, upper)
            cursor = hi
        assert cursor == t_hi
        assert lines[-2] == "SCALED BULK SIGN ROW PASS"
        total_rows += len(rows)
        print("SCALED BULK PROBE UNIT AUDIT PASS",
              "unit", unit, "t_rows", len(rows), "byte_equal", True)
    print("TOTAL PROBE ROWS", total_rows)
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
