"""Validator for one local K4 centred-band transcript pair."""

from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb

import surface_remainder_centered_delta_integrator_design as design
from surface_remainder_complement_l3_smoke import NAMES

ROOT = Path(__file__).resolve().parents[1]
BANDS = {
    "k4_0030": (Fraction(3, 100), Fraction(61, 2000), 9216),
    "k4_0040": (Fraction(1, 25), Fraction(81, 2000), 2304),
}
DEPS = (
    "scripts/certify_surface_remainder_k4_centered_band.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_complement.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path, unit):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 CENTERED BAND TRANSCRIPT"
    assert f"CONFIG unit {unit} " in lines[5]
    assert "K4 CENTERED BAND CANDIDATE PASS" in lines
    assert "SCOPE local positive-delta witness only; no K4/G6 promotion" in lines
    deps = {line.split()[1]: line.split()[2]
            for line in lines if line.startswith("DEPENDENCY ")}
    expected = {relative: sha256(ROOT / relative) for relative in DEPS}
    legacy = dict(expected)
    legacy["scripts/surface_remainder_centered_delta_carrier.py"] = (
        "4fa022d2a4105f423cc6cd2fcc2d4fa67c8dff1a09813f8057a9259135063675")
    historical = any(line == f"PROVENANCE git_head {head}" for line in lines
                     for head in {"91eee6b0f39b98a96e80d9567ad9b8f7d94646ef",
                                  "67653345c830729733f93f463dd4c1d11312297e",
                                  "f38efe10081fa6aae2b3569cffcbcd1631625035",
                                  "6adda35ba06afdfcd45068fc4630155a67ef1689",
                                  "4c685dcf3fd38cdc9270d693da7425be053c839b",
                                  "8b4a17c0681601d0d433ed769d23ce8daa8269a9"})
    assert deps == expected or (deps == legacy and historical)
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
    a, count = parse(ROOT / "scripts" / f"surface_remainder_k4_{args.unit}.txt", args.unit)
    b, count2 = parse(ROOT / "scripts" / f"surface_remainder_k4_{args.unit}_rerun.txt", args.unit)
    assert a == b and count == count2
    print("K4 CENTERED BAND VALIDATION PASS", args.unit, "cells", count)


if __name__ == "__main__":
    main()
