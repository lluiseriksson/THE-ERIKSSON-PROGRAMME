"""Validate the paired lambda-band transcript and its manifest."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
UNIT = "beta101p8125_101p81275_lambda150_151"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED PAIR TAYLOR CELL CERTIFICATE"
    assert "SCOPE one rational cell only; no G2/G6 promotion" in lines
    total = arb(next(x.split(" ", 1)[1] for x in lines
                     if x.startswith("total_upper ")))
    assert total < 0
    for line in lines:
        if line.startswith("dependency "):
            fields = line.split()
            assert sha256(ROOT / fields[1]) == fields[3]
    assert lines[-2] == "SCALED PAIR TAYLOR CELL PASS"
    return next(x for x in lines if x.startswith("git_head "))


def main() -> int:
    ctx.prec = 500
    production = ROOT / f"scripts/surface_scaled_pair_taylor_cell_{UNIT}.txt"
    replay = ROOT / f"scripts/surface_scaled_pair_taylor_cell_{UNIT}_rerun.txt"
    assert production.exists() and replay.exists()
    assert production.read_bytes() == replay.read_bytes()
    h1, h2 = validate(production), validate(replay)
    assert h1 == h2
    manifest = json.loads((ROOT /
        "run-manifests/surface-scaled-pair-taylor-band-20260720.json")
                          .read_text(encoding="utf-8"))
    assert manifest["git_head"] == h1.split(" ", 1)[1]
    assert manifest["transcript_sha256"] == sha256(production)
    assert manifest["replay_sha256"] == sha256(replay)
    print("SCALED PAIR LAMBDA BAND VALIDATION PASS", UNIT)
    print("paired byte equality", len(production.read_bytes()))
    print("SCOPE one beta/lambda band only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
