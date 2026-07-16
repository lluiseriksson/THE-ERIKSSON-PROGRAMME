"""Validate exact row equality for the upper finite-G5 replay."""

import hashlib
from pathlib import Path

import certify_surface_right_edge_five_family_finite as cert
import validate_surface_right_edge_five_family_finite_transcripts as production
import run_surface_right_edge_five_family_finite_rerun_units as replay

ROOT = Path(__file__).resolve().parents[1]


def validate():
    expected = {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
                for rel in cert.DEPENDENCIES}
    rows = 0
    for unit in cert.UNITS:
        prod = production.path_for(unit).read_text(encoding="utf-8").splitlines()
        rerun = replay.output_path(unit).read_text(encoding="utf-8").splitlines()
        for lines in (prod, rerun):
            deps = {line.split()[1]: line.split()[2] for line in lines
                    if line.startswith("DEPENDENCY ")}
            assert deps == expected and "CERTIFICATE FAIL" not in lines
        p_rows = [line for line in prod if line.startswith("ROW ")]
        r_rows = [line for line in rerun if line.startswith("ROW ")]
        assert p_rows == r_rows and p_rows
        assert any(line.startswith(
            "CERTIFIED RIGHT-EDGE FIVE-FAMILY FINITE UNIT "
            f"{cert.unit_slug(unit)} ") for line in rerun)
        rows += len(r_rows)
    assert rows == 375
    print("RIGHT-EDGE UPPER FINITE INDEPENDENT RERUN PASS: 375/375 rows")


if __name__ == "__main__":
    validate()
