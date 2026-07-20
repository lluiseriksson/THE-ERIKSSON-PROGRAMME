"""Validate the paired mean-value transcript and dependency hashes."""

from __future__ import annotations

import hashlib
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
UNIT = "beta101p8125_101p84375_lambda150_151"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED PAIR MEAN-VALUE CELL CERTIFICATE"
    assert "SCOPE one beta/lambda cell only; no G2/G6 promotion" in lines
    total = arb(next(x.split(" ", 1)[1] for x in lines
                     if x.startswith("total_upper ")))
    assert total < 0
    for line in lines:
        if line.startswith("dependency "):
            fields = line.split()
            assert sha256(ROOT / fields[1]) == fields[3]
    assert lines[-2] == "SCALED PAIR MEAN-VALUE CELL PASS"
    return next(x for x in lines if x.startswith("git_head "))


def main() -> int:
    ctx.prec = 500
    production = ROOT / f"scripts/surface_scaled_pair_mean_value_cell_{UNIT}.txt"
    replay = ROOT / f"scripts/surface_scaled_pair_mean_value_cell_{UNIT}_rerun.txt"
    assert production.exists() and replay.exists()
    assert production.read_bytes() == replay.read_bytes()
    assert validate(production) == validate(replay)
    print("SCALED PAIR MEAN-VALUE VALIDATION PASS", UNIT)
    print("paired byte equality", len(production.read_bytes()))
    print("SCOPE one beta/lambda cell only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
