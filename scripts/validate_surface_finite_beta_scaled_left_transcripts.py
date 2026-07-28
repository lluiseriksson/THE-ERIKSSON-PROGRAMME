"""Validate exact beta/t coverage of all paired scaled-left transcripts."""

from fractions import Fraction
import json
from pathlib import Path

from flint import arb

import certify_surface_finite_beta_scaled_left as cert
import surface_finite_beta_scaled_partition as partition
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
PARTITION_PATH = "scripts/surface_finite_beta_scaled_partition.py"
HISTORICAL_PARTITION_SHA256 = (
    "3abc0499f4cdd79d06a571c11347b8e0166c60e4f20d741bfab551cfa2cb94da"
)


def parse_fraction(value):
    return Fraction(value)


def validate():
    rows, heads = [], set()
    for unit in partition.UNITS:
        path = ROOT/"scripts"/("certify_surface_finite_beta_scaled_left_"
                               f"{partition.unit_slug(unit)}_transcript.txt")
        lines = path.read_text(encoding="utf-8").splitlines()
        assert not any("CERTIFICATE FAIL" in line for line in lines)
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        assert len(head_lines) == 1
        heads.add(head_lines[0].split()[-1])
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        assert dependencies.pop(PARTITION_PATH) == HISTORICAL_PARTITION_SHA256
        validate_recorded_dependencies(
            dependencies,
            tuple(path for path in cert.DEPENDENCIES
                  if path != PARTITION_PATH),
            ROOT,
        )
        unit_rows = [json.loads(line[4:]) for line in lines
                     if line.startswith("ROW ")]
        assert unit_rows
        rows.extend(unit_rows)
        terminals = [line for line in lines
                     if line.startswith(
                         "CERTIFIED FINITE-BETA SCALED LEFT UNIT "
                         f"{partition.unit_slug(unit)} ")]
        assert len(terminals) == 1
    assert len(heads) == 1

    grouped = {}
    for row in rows:
        key = (row["beta_index"], row["lane"])
        grouped.setdefault(key, []).append(row)
        assert arb(row["W_upper"]) < 0
    assert {index for index, _ in grouped} == set(
        range(len(partition.BETA_INTERVALS)))
    for index, (beta_lo, beta_hi) in enumerate(partition.BETA_INTERVALS):
        for lane, start, stop in (
                ("normalized", Fraction(0), paired_splice()),
                ("regular", paired_splice(), Fraction(3, 5))):
            lane_rows = grouped[index, lane]
            assert all(row["beta_lo"] == partition.fraction_string(beta_lo)
                       and row["beta_hi"] == partition.fraction_string(beta_hi)
                       for row in lane_rows)
            intervals = sorted(
                (parse_fraction(row["t_lo"]), parse_fraction(row["t_hi"]))
                for row in lane_rows)
            assert intervals[0][0] == start and intervals[-1][1] == stop
            assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    print("FINITE-BETA SCALED LEFT TRANSCRIPTS PASS:",
          len(partition.BETA_INTERVALS), "beta intervals;", len(rows),
          "strict t rows")
    return rows


def paired_splice():
    return Fraction(19, 100)


if __name__ == "__main__":
    validate()
