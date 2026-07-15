"""Validate the authoritative five-family half-line transcript."""

import hashlib
import json
from pathlib import Path

from flint import arb

import certify_surface_right_edge_five_family_halfline as cert


ROOT = Path(__file__).resolve().parents[1]
def transcript_path(unit):
    return ROOT/"scripts"/(
        "certify_surface_right_edge_five_family_halfline_"
        f"{cert.unit_slug(unit)}_transcript.txt")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    expected_hashes = {
        relative: sha256(ROOT/relative) for relative in cert.DEPENDENCIES
    }
    rows, heads = [], set()
    for unit in cert.UNITS:
        lines = transcript_path(unit).read_text(encoding="utf-8").splitlines()
        assert not any("CERTIFICATE FAIL" in line for line in lines)
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        assert len(head_lines) == 1
        heads.add(head_lines[0].split()[-1])
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        assert dependencies == expected_hashes
        configs = [line for line in lines if line.startswith("CONFIG ")]
        assert len(configs) == 1
        assert "delta_partition 0:1/125:1/1000" in configs[0]
        assert "lambda_partition 0:3/2:1/50" in configs[0]
        unit_rows = [json.loads(line[4:]) for line in lines
                     if line.startswith("ROW ")]
        assert len(unit_rows) == 40
        rows.extend(unit_rows)
        terminals = [line for line in lines if line.startswith(
            "CERTIFIED RIGHT-EDGE FIVE-FAMILY HALFLINE UNIT "
            f"{cert.unit_slug(unit)} 40 rows ")]
        assert len(terminals) == 1
    assert len(heads) == 1
    assert len(rows) == 600
    expected_pairs = [(di, li) for di in range(8) for li in range(75)]
    assert [(row["delta_index"], row["lambda_index"])
            for row in rows] == expected_pairs
    for row in rows:
        delta_index, index = row["delta_index"], row["lambda_index"]
        assert row["delta_lo"] == f"{delta_index}/1000"
        assert row["delta_hi"] == f"{delta_index+1}/1000"
        assert row["lambda_lo"] == f"{index}/50"
        assert row["lambda_hi"] == f"{index+1}/50"
        assert row["resolution"] in {"coarse", "mixed"}
        assert len(row["families_lower"]) == 5
        assert len(row["families_upper"]) == 5
        assert arb(row["families_lower"][3]) > 0
        assert arb(row["P0_lower"]) > 0
        assert arb(row["H_lower"]) > 0
    worst = min(rows, key=lambda row: float(arb(row["H_lower"])))
    print(
        "RIGHT-EDGE FIVE-FAMILY HALFLINE TRANSCRIPT PASS: 600/600; worst",
        worst["delta_index"], worst["lambda_index"],
        "H_lower", worst["H_lower"],
    )
    return rows


if __name__ == "__main__":
    validate()
