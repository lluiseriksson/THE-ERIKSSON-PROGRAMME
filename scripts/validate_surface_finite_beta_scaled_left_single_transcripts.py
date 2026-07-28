"""Validate the atomic one-beta scaled-left cover."""

import hashlib
import json
from pathlib import Path

from flint import arb

import certify_surface_finite_beta_scaled_left as cert
import surface_finite_beta_scaled_partition as partition
import run_surface_finite_beta_scaled_left_single_units as launcher


ROOT = Path(__file__).resolve().parents[1]


def validate():
    expected = {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                for relative in cert.DEPENDENCIES}
    rows, heads = [], set()
    for index in range(len(partition.BETA_INTERVALS)):
        path = launcher.output_path(index)
        lines = path.read_text(encoding="utf-8").splitlines()
        assert not any("CERTIFICATE FAIL" in line for line in lines)
        heads.update(line.split()[-1] for line in lines
                     if line.startswith("PROVENANCE git_head "))
        deps = {line.split()[1]: line.split()[2] for line in lines
                if line.startswith("DEPENDENCY ")}
        assert deps == expected
        unit_rows = [json.loads(line[4:]) for line in lines
                     if line.startswith("ROW ")]
        assert unit_rows
        assert any(line.startswith(
            f"CERTIFIED FINITE-BETA SCALED LEFT UNIT beta_index_{index:04d} 1")
            for line in lines)
        for row in unit_rows:
            assert arb(row["W_upper"]) < 0
        rows.extend(unit_rows)
    assert len(heads) == 1
    assert {row["beta_index"] for row in rows} == set(
        range(len(partition.BETA_INTERVALS)))
    print("FINITE-BETA SCALED LEFT SINGLE TRANSCRIPTS PASS:",
          len(partition.BETA_INTERVALS), "beta intervals;", len(rows), "rows")
    return rows


if __name__ == "__main__":
    validate()
