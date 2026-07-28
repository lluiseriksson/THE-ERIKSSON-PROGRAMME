"""Independent validator for the frozen [31,35] candidate union."""

from decimal import Decimal
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
UNITS = (("31_32", Decimal("31.0"), Decimal("32.0")),
         ("32_33", Decimal("32.0"), Decimal("33.0")),
         ("33_34", Decimal("33.0"), Decimal("34.0")),
         ("34_35", Decimal("34.0"), Decimal("35.0")))
ROW = re.compile(r"^beta-box \[([0-9]+\.[0-9]+),\s*([0-9]+\.[0-9]+)\]: ([0-9]+) t-boxes$")


def rows(path: Path):
    return [line for line in path.read_text(encoding="utf-8").splitlines()
            if line.startswith("beta-box ")]


def validate() -> None:
    cursor = Decimal("31.0")
    total = 0
    for unit, lo_expected, hi_expected in UNITS:
        production = rows(ROOT / f"scripts/surface_scaled_bulk_{unit}.txt")
        replay = rows(ROOT / f"scripts/surface_scaled_bulk_{unit}_rerun.txt")
        assert len(production) == 10, (unit, len(production))
        assert production == replay, unit
        assert cursor == lo_expected
        for line in production:
            match = ROW.fullmatch(line)
            assert match is not None, line
            lo, hi, count = match.groups()
            assert Decimal(lo) == cursor, (line, cursor)
            assert Decimal(hi) > Decimal(lo), line
            assert int(count) > 0, line
            cursor = Decimal(hi)
            total += int(count)
        assert cursor == hi_expected, (unit, cursor, hi_expected)
    assert cursor == Decimal("35.0")
    print("SCALED BULK [31,35] VALIDATION PASS beta_boxes 40 t_boxes", total)


if __name__ == "__main__":
    validate()
