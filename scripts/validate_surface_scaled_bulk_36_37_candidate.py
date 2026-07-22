"""Validate the order-13 scaled-bulk [36,37] candidate and replay."""

from decimal import Decimal
import re

import run_surface_scaled_bulk_36_37_candidate as runner

BOX = re.compile(r"^beta-box \[([0-9.]+),\s*([0-9.]+)\]: ([0-9]+) t-boxes$")


def records(text: str) -> list[str]:
    return [line for line in text.splitlines() if line.startswith("beta-box ")]


def validate() -> None:
    prod = records(runner.path().read_text(encoding="utf-8"))
    replay = records(runner.path("_rerun").read_text(encoding="utf-8"))
    assert prod == replay
    assert len(prod) == 8
    cursor = Decimal("36.0")
    total = 0
    for line in prod:
        match = BOX.match(line)
        assert match is not None, line
        lo, hi, n = match.groups()
        assert Decimal(lo) == cursor
        assert Decimal(hi) > cursor
        assert int(n) > 0
        cursor = Decimal(hi)
        total += int(n)
    assert cursor == Decimal("37.0")
    print("SCALED BULK [36,37] ORDER-13 VALIDATION PASS:",
          "beta_boxes", len(prod), "t_boxes", total)


if __name__ == "__main__":
    validate()
