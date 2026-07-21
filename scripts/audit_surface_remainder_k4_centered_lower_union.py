"""Audit the contiguous local K4 centred-band prefix below 0.0300.

This is deliberately a candidate-only topology and arithmetic audit.  It
does not infer the missing regular endpoint, t-union, overlap, or weighted
global S1'''/S2''' theorem.
"""

from fractions import Fraction
import importlib.util
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
UNITS = (
    ("k4_00275_00280", Fraction(11, 400), Fraction(7, 250),
     "validate_surface_remainder_k4_centered_00275_00280.py"),
    ("k4_00280_00285", Fraction(7, 250), Fraction(57, 2000),
     "validate_surface_remainder_k4_centered_00280_00285.py"),
    ("k4_00285_00290", Fraction(57, 2000), Fraction(29, 1000),
     "validate_surface_remainder_k4_centered_00285_00290.py"),
    ("k4_00290_00295", Fraction(29, 1000), Fraction(59, 2000),
     "validate_surface_remainder_k4_centered_00290_00295.py"),
    ("k4_00295_0030", Fraction(59, 2000), Fraction(3, 100),
     "validate_surface_remainder_k4_centered_00295_0030.py"),
)


def load_validator(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_with_count(validator, path):
    result = validator.parse(path)
    if isinstance(result, tuple):
        return result
    lines = result
    cells = sum(1 for line in lines if line.startswith("CELL "))
    return lines, cells


def main() -> int:
    previous = None
    total_cells = 0
    worst = None
    for unit, lo, hi, validator_name in UNITS:
        validator = load_validator(validator_name)
        lines, count = parse_with_count(validator, ROOT / "scripts" / f"surface_remainder_k4_{unit}.txt")
        replay_lines, replay_count = parse_with_count(validator,
            ROOT / "scripts" / f"surface_remainder_k4_{unit}_rerun.txt")
        assert lines == replay_lines and count == replay_count
        assert previous is None or lo == previous
        previous = hi
        total_cells += count
        fractions_line = next(line for line in lines if line.startswith("FRACTIONS "))
        import json
        fractions = json.loads(fractions_line[10:])
        for name, value in fractions.items():
            interval = arb(value)
            if worst is None or interval > worst[0]:
                worst = (interval, unit, name)
    assert previous == Fraction(3, 100)
    assert worst is not None and worst[0] < 1
    print("K4 CENTERED LOWER UNION AUDIT PASS",
          "units", len(UNITS), "cells", total_cells,
          "domain", "11/400:3/100",
          "worst", worst[0].str(18), worst[1], worst[2])
    print("CANDIDATE ONLY; NO K4/G2/G6/S1'''/S2''' PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
