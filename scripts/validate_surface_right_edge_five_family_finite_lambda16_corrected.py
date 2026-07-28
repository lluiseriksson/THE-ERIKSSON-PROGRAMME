"""Validate the corrected scoped lambda16 candidate and its replay."""

import json
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]


def rows(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert any("lambda_partition 0:8/5:1/50" in line
               and "tail_lambda_max 8/5" in line for line in lines)
    terminal = [line for line in lines
                if line.startswith(
                    "CERTIFIED SCOPED CANDIDATE RIGHT-EDGE")]
    assert len(terminal) == 1
    parsed = [json.loads(line[4:]) for line in lines
              if line.startswith("ROW ")]
    assert len(parsed) == 5
    assert {row["delta_index"] for row in parsed} == {0}
    assert {row["lambda_index"] for row in parsed} == set(range(75, 80))
    for row in parsed:
        assert arb(row["families_lower"][3]) > 0
        assert arb(row["P0_lower"]) > 0
        assert arb(row["H_lower"]) > 0
    return parsed


def main(production, replay):
    primary = rows(ROOT / production)
    rerun = rows(ROOT / replay)
    assert primary == rerun
    worst = min(primary, key=lambda row: float(arb(row["H_lower"])))
    print("CORRECTED LAMBDA16 SCOPED CANDIDATE PASS 5/5")
    print("worst", worst["delta_index"], worst["lambda_index"],
          "H_lower", worst["H_lower"])
    print("exact JSON replay equality")
    print("scope delta band 0 only; lambda [3/2,8/5]")
    print("NO G2/G5/G6 PROMOTION")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", required=True)
    parser.add_argument("--replay", required=True)
    args = parser.parse_args()
    main(args.production, args.replay)
