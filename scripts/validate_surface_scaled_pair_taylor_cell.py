"""Validate one paired narrow-cell transcript without promoting G2."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
UNIT = "narrow_101p8125_101p81275_lambda_1501"
HEADER = "SCALED PAIR TAYLOR CELL CERTIFICATE"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == HEADER
    assert "SCOPE one rational cell only; no G2/G6 promotion" in lines
    total = arb(next(x.split(" ", 1)[1] for x in lines
                     if x.startswith("total_upper ")))
    assert total < 0
    for line in lines:
        if not line.startswith("dependency "):
            continue
        fields = line.split()
        relative, recorded = fields[1], fields[3]
        assert sha256(ROOT / relative) == recorded
    assert lines[-2] == "SCALED PAIR TAYLOR CELL PASS"
    return next(x for x in lines if x.startswith("git_head "))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", default=UNIT)
    args = parser.parse_args()
    if args.unit != UNIT:
        raise ValueError("only the frozen narrow unit is registered")
    ctx.prec = 500
    production = ROOT / f"scripts/surface_scaled_pair_taylor_cell_{UNIT}.txt"
    replay = ROOT / f"scripts/surface_scaled_pair_taylor_cell_{UNIT}_rerun.txt"
    assert production.exists() and replay.exists()
    assert production.read_bytes() == replay.read_bytes()
    head = validate(production)
    assert head == validate(replay)
    manifest = json.loads((ROOT /
        "run-manifests/surface-scaled-pair-taylor-cell-narrow-20260720.json")
                          .read_text(encoding="utf-8"))
    assert manifest["git_head"] == head.split(" ", 1)[1]
    assert manifest["transcript_sha256"] == sha256(production)
    assert manifest["replay_sha256"] == sha256(replay)
    assert manifest["status"] == "CELL_CERTIFIED_CANDIDATE"
    print("SCALED PAIR CELL VALIDATION PASS", UNIT)
    print("paired byte equality", len(production.read_bytes()))
    print("SCOPE one cell only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
