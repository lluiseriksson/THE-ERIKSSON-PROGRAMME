"""Generic independent validator for one quarantined order-24 mid-cover unit."""

from fractions import Fraction
import argparse
from pathlib import Path
import re

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
ROW_RE = re.compile(r"^trow (\d+) (\S+) (\S+) upper (.+)$")


def parse(base: Path, lo: Fraction, hi: Fraction, rows_expected: int):
    def one(path: Path):
        lines = path.read_text(encoding="utf-8").replace("\r\n", "\n").splitlines()
        assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR"
        assert "config CWIN 3/2 beta_order 24 t_order 25 min_dt 1/100000 prec 180" in lines
        _, got_lo, got_hi = next(x for x in lines if x.startswith("beta_domain ")).split()
        assert (Fraction(got_lo), Fraction(got_hi)) == (lo, hi)
        rows = []
        for line in lines:
            m = ROW_RE.match(line)
            if m:
                i, a, b, upper = m.groups()
                rows.append((int(i), Fraction(a), Fraction(b), arb(upper)))
        assert len(rows) == rows_expected
        assert [r[0] for r in rows] == list(range(rows_expected))
        assert all(r[3].is_finite() and r[3].upper() < 0 for r in rows)
        assert rows[0][1] == Fraction(3, 5)
        assert all(a[2] == b[1] for a, b in zip(rows, rows[1:]))
        assert "SCALED BULK SIGN ROW PASS" in lines
        assert "SCOPE quarantined order24 repair; no G2/G6 promotion" in lines
        return lines

    production = one(base.with_suffix(".txt"))
    replay = one(base.with_name(base.name + "_rerun").with_suffix(".txt"))
    assert production == replay


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--rows", required=True, type=int)
    args = parser.parse_args()
    parse(ROOT / "scripts" / args.base, Fraction(args.lo), Fraction(args.hi), args.rows)
    print("ORDER24 UNIT VALIDATION PASS", args.base)
    print("ROWS", args.rows)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
