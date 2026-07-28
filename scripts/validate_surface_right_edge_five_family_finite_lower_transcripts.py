"""Validate the authoritative 225-cell lower finite-G5 production union."""

import json
from pathlib import Path

from flint import arb

import certify_surface_right_edge_five_family_finite_lower as cert
import run_surface_right_edge_five_family_finite_lower_units as launcher
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]


def validate():
    rows, heads = [], set()
    for unit in cert.UNITS:
        lines = launcher.output_path(unit).read_text(
            encoding="utf-8").splitlines()
        assert not any("CERTIFICATE FAIL" in line for line in lines)
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        assert len(head_lines) == 1
        heads.add(head_lines[0].split()[-1])
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        validate_recorded_dependencies(
            dependencies, cert.DEPENDENCIES, ROOT
        )
        unit_rows = [json.loads(line[4:]) for line in lines
                     if line.startswith("ROW ")]
        assert len(unit_rows) == len(cert.cover.DELTA_BANDS)*(
            unit[1]-unit[0])
        rows.extend(unit_rows)
        assert sum(line.startswith(launcher.terminal(unit))
                   for line in lines) == 1
    assert len(heads) == 1 and len(rows) == 225
    expected = {(di, li) for di in range(len(cert.cover.DELTA_BANDS))
                for li in range(75)}
    actual = [(row["delta_index"], row["lambda_index"]) for row in rows]
    assert len(actual) == len(set(actual)) and set(actual) == expected
    for row in rows:
        dlo, dhi = cert.cover.DELTA_BANDS[row["delta_index"]]
        assert row["delta_lo"] == cert.cover.fraction_string(dlo)
        assert row["delta_hi"] == cert.cover.fraction_string(dhi)
        assert len(row["tail_budgets"]) == 5
        assert len(row["families_lower"]) == 5
        assert arb(row["families_lower"][3]) > 0
        assert arb(row["P0_lower"]) > 0 and arb(row["H_lower"]) > 0
    worst = min(rows, key=lambda row: float(arb(row["H_lower"])))
    print("RIGHT-EDGE LOWER FINITE TRANSCRIPTS PASS: 225/225; worst",
          worst["delta_index"], worst["lambda_index"], "H_lower",
          worst["H_lower"])
    return rows


if __name__ == "__main__":
    validate()
