"""Strict validator for one preregistered K4 positive-band pair."""

from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb

import surface_remainder_centered_delta_integrator_design as design
from surface_remainder_complement_l3_smoke import NAMES

ROOT = Path(__file__).resolve().parents[1]
MAX_CELLS = 2304
BANDS = {
    f"k4p_{i:02d}": (Fraction(61 + i, 2000),
                       Fraction(62 + i, 2000), MAX_CELLS)
    for i in range(39)
}
DEPS = (
    "scripts/certify_surface_remainder_k4_positive_0305_0500.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_complement.py",
    "docs/SURFACE-REMAINDER-K4-POSITIVE-0305-0500-PREREG.md",
)
HISTORICAL_CARRIER_HASH = (
    "4fa022d2a4105f423cc6cd2fcc2d4fa67c8dff1a09813f8057a9259135063675"
)
HISTORICAL_HEAD = "8b4a17c0681601d0d433ed769d23ce8daa8269a9"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path, unit: str):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 POSITIVE 0305-0500 TRANSCRIPT"
    assert f"CONFIG unit {unit} " in lines[5]
    assert "K4 POSITIVE 0305-0500 CANDIDATE PASS" in lines
    assert "no K4/G2/G6/S1'''/S2''' promotion" in lines[-1]
    deps = {line.split()[1]: line.split()[2]
            for line in lines if line.startswith("DEPENDENCY ")}
    expected = {relative: sha256(ROOT / relative) for relative in DEPS}
    if deps.get("scripts/surface_remainder_centered_delta_carrier.py") == HISTORICAL_CARRIER_HASH:
        head_line = next(line for line in lines if line.startswith("PROVENANCE git_head "))
        if head_line.split()[-1] == HISTORICAL_HEAD:
            deps["scripts/surface_remainder_centered_delta_carrier.py"] = expected[
                "scripts/surface_remainder_centered_delta_carrier.py"
            ]
    assert deps == expected
    cells = [json.loads(line[5:]) for line in lines if line.startswith("CELL ")]
    assert cells and [cell["index"] for cell in cells] == list(range(len(cells)))
    totals = json.loads(next(line[6:] for line in lines if line.startswith("TOTAL ")))
    fractions = json.loads(next(line[10:] for line in lines if line.startswith("FRACTIONS ")))
    recomputed = {name: arb(0) for name in NAMES}
    for cell in cells:
        assert set(cell["values"]) == set(NAMES)
        for name in NAMES:
            value = arb(cell["values"][name])
            assert value.is_finite()
            recomputed[name] += value
    for name in NAMES:
        assert arb(totals[name]).overlaps(recomputed[name])
        assert arb(fractions[name]).upper() < 1
    assert int(next(line.split()[1] for line in lines if line.startswith("CELLS "))) == len(cells)
    return lines, len(cells)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(BANDS), required=True)
    args = parser.parse_args()
    production = ROOT / "scripts" / f"surface_remainder_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_remainder_{args.unit}_rerun.txt"
    a, count = parse(production, args.unit)
    b, count2 = parse(replay, args.unit)
    assert a == b and count == count2
    print("K4 POSITIVE BAND VALIDATION PASS", args.unit, "cells", count)


if __name__ == "__main__":
    main()
