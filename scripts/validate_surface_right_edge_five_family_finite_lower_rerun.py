"""Validate the independent lower finite-G5 replay against production."""

from pathlib import Path

import certify_surface_right_edge_five_family_finite_lower as cert
import validate_surface_right_edge_five_family_finite_lower_transcripts as production
import run_surface_right_edge_five_family_finite_lower_rerun_units as replay
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]


def validate():
    total = 0
    for unit in cert.UNITS:
        prod = production.launcher.output_path(unit).read_text(
            encoding="utf-8").splitlines()
        rerun = replay.output_path(unit).read_text(
            encoding="utf-8").splitlines()
        validate_recorded_dependencies(
            {line.split()[1]: line.split()[2] for line in prod
             if line.startswith("DEPENDENCY ")},
            cert.DEPENDENCIES,
            ROOT,
        )
        validate_recorded_dependencies(
            {line.split()[1]: line.split()[2] for line in rerun
             if line.startswith("DEPENDENCY ")},
            cert.DEPENDENCIES,
            ROOT,
        )
        assert "CERTIFICATE FAIL" not in rerun
        prod_rows = [line for line in prod if line.startswith("ROW ")]
        rerun_rows = [line for line in rerun if line.startswith("ROW ")]
        assert len(prod_rows) == len(rerun_rows)
        assert prod_rows == rerun_rows
        assert any(line.startswith("CERTIFIED RIGHT-EDGE FIVE-FAMILY FINITE UNIT ")
                   for line in rerun)
        total += len(rerun_rows)
    assert total == 225
    print("RIGHT-EDGE LOWER FINITE INDEPENDENT RERUN PASS: 225/225 rows")


if __name__ == "__main__":
    validate()
