"""Compare the independent scaled-left replay with production rows."""

from pathlib import Path

import certify_surface_finite_beta_scaled_left as cert
import surface_finite_beta_scaled_partition as partition
import run_surface_finite_beta_scaled_left_single_units as production
import run_surface_finite_beta_scaled_left_independent_rerun as replay
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
PARTITION_PATH = "scripts/surface_finite_beta_scaled_partition.py"
HISTORICAL_PARTITION_SHA256 = (
    "3abc0499f4cdd79d06a571c11347b8e0166c60e4f20d741bfab551cfa2cb94da"
)


def validate():
    rows = 0
    for index in range(len(partition.BETA_INTERVALS)):
        prod = production.output_path(index).read_text(encoding="utf-8").splitlines()
        rerun = replay.output_path(index).read_text(encoding="utf-8").splitlines()
        for lines in (prod, rerun):
            deps = {line.split()[1]: line.split()[2] for line in lines
                    if line.startswith("DEPENDENCY ")}
            assert deps.pop(PARTITION_PATH) == HISTORICAL_PARTITION_SHA256
            validate_recorded_dependencies(
                deps,
                tuple(path for path in cert.DEPENDENCIES
                      if path != PARTITION_PATH),
                ROOT,
            )
            assert "CERTIFICATE FAIL" not in lines
        prod_rows = [line for line in prod if line.startswith("ROW ")]
        rerun_rows = [line for line in rerun if line.startswith("ROW ")]
        assert prod_rows == rerun_rows and prod_rows
        assert any(line.startswith(
            f"CERTIFIED FINITE-BETA SCALED LEFT UNIT beta_index_{index:04d} 1")
            for line in rerun)
        rows += len(rerun_rows)
    assert rows == 4636
    print("FINITE-BETA SCALED LEFT INDEPENDENT RERUN PASS: 912 intervals;",
          rows, "rows")


if __name__ == "__main__":
    validate()
