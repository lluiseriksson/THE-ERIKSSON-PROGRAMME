"""Validate the frozen [35,36] candidate union and replay equality."""

from decimal import Decimal
import re

import certify_surface_scaled_bulk_35_36_candidate as cert
import run_surface_scaled_bulk_35_36_candidate as runner

BOX = re.compile(r"^beta-box \[([0-9.]+),\s*([0-9.]+)\]: ([0-9]+) t-boxes$")


def records(text: str) -> list[str]:
    return [line for line in text.splitlines() if line.startswith("beta-box ")]


def validate() -> None:
    cursor = Decimal("35.0")
    total = 0
    count = 0
    for unit, (_, hi) in cert.SEGMENTS.items():
        lines = records(runner.path(unit).read_text(encoding="utf-8"))
        assert len(lines) == 4, (unit, len(lines))
        for line in lines:
            match = BOX.match(line)
            assert match is not None, line
            lo, end, n_t = match.groups()
            assert Decimal(lo) == cursor, (unit, cursor, lo)
            assert Decimal(end) > cursor
            assert int(n_t) > 0
            cursor = Decimal(end)
            total += int(n_t)
            count += 1
        assert cursor == Decimal(str(float(hi))), (unit, cursor, hi)
    assert cursor == Decimal("36.0")
    for unit in cert.SEGMENTS:
        prod = records(runner.path(unit).read_text(encoding="utf-8"))
        replay = records(runner.path(unit, "_rerun").read_text(encoding="utf-8"))
        assert prod == replay, unit
    print("SCALED BULK [35,36] CANDIDATE VALIDATION PASS:",
          "beta_boxes", count, "t_boxes", total)


if __name__ == "__main__":
    validate()
