"""Validate the repaired beta-remainder gap-cell production/replay pair."""

from __future__ import annotations

import hashlib
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
UNIT = "101p96875_101p984375_lambda150_190"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED PAIR MEAN-VALUE CELL CERTIFICATE"
    assert "config beta_order 50 lambda_order 50 modes 115 precision 500" in lines[5]
    assert "SCOPE one beta/lambda cell only; no G2/G6 promotion" in lines
    total = arb(next(line.split(" ", 1)[1] for line in lines
                     if line.startswith("total_upper ")))
    assert total < 0
    assert any(line.startswith("lambda_beta_remainder ") for line in lines)
    for line in lines:
        if line.startswith("dependency "):
            fields = line.split()
            assert sha256(ROOT / fields[1]) == fields[3]


def main() -> int:
    ctx.prec = 500
    production = ROOT / "scripts" / (
        f"surface_scaled_pair_mean_value_gap_cell_{UNIT}.txt")
    replay = ROOT / "scripts" / (
        f"surface_scaled_pair_mean_value_gap_cell_{UNIT}_rerun.txt")
    assert production.exists() and replay.exists()
    assert production.read_bytes() == replay.read_bytes()
    validate(production)
    validate(replay)
    print("SCALED PAIR GAP CELL VALIDATION PASS", UNIT)
    print("production/replay byte equality", len(production.read_bytes()))
    print("SCOPE candidate cell only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
