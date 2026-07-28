"""Validate the frozen four-unit compact G5 extension union."""

from decimal import Decimal
import re
from pathlib import Path

import certify_right_edge_beta_taylor_cached_extension as cert
import run_right_edge_beta_taylor_cached_extension_units as launcher
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
HEAD = "8b4a17c0681601d0d433ed769d23ce8daa8269a9"
BOX = re.compile(
    r"^beta-box \[([0-9.]+),([0-9.]+)\]: normalized=([0-9]+) regular=([0-9]+)$")


def validate():
    cursor = Decimal("20")
    totals = [0, 0, 0]
    for unit, (lo, hi, step, splice) in cert.SEGMENTS.items():
        assert Decimal(str(float(lo))) == cursor
        lines = launcher.output_path(unit).read_text(
            encoding="utf-8").splitlines()
        assert lines.count(f"PROVENANCE git_head {HEAD}") == 1
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        validate_recorded_dependencies(
            dependencies, cert.DEPENDENCIES, ROOT
        )
        boxes = [BOX.match(line) for line in lines if line.startswith("beta-box ")]
        assert boxes and all(match is not None for match in boxes)
        for match in boxes:
            blo, bhi, normalized, regular = match.groups()
            blo, bhi = Decimal(blo), Decimal(bhi)
            assert blo == cursor and bhi > blo
            assert bhi-blo <= Decimal(str(float(step)))
            assert int(normalized) > 0 and int(regular) > 0
            cursor = bhi
            totals[0] += 1
            totals[1] += int(normalized)
            totals[2] += int(regular)
        assert cursor == Decimal(str(float(hi)))
        terminal = [line for line in lines if line.startswith(
            launcher.terminal(unit))]
        assert len(terminal) == 1
        declared = re.search(
            r"beta_boxes (\d+) normalized_boxes (\d+) regular_boxes (\d+)$",
            terminal[0])
        assert declared is not None
        unit_totals = (len(boxes),
                       sum(int(match.group(3)) for match in boxes),
                       sum(int(match.group(4)) for match in boxes))
        assert unit_totals == tuple(map(int, declared.groups()))
    assert cursor == Decimal("25.0")
    print("RIGHT-EDGE COMPACT EXTENSION UNION PASS: beta_boxes",
          totals[0], "normalized", totals[1], "regular", totals[2],
          "head", HEAD)
    return totals


if __name__ == "__main__":
    validate()
