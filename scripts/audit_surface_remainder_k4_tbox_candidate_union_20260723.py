"""Audit the centred K4 candidate t-box chain from t=3 to pi_hi.

This is a topology/consistency audit only.  It checks exact adjacency,
production/replay byte equality, cell counts, dependency hashes, and the
seven local fraction inequalities.  It never promotes K4, S1'''/S2''', G2,
or G6.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
PI_HI = Fraction(31415927, 10_000_000)
UNITS = [(f"{i:03d}_{i+1:03d}", Fraction(i, 100), Fraction(i + 1, 100))
         for i in range(300, 314)] + [("314_pi", Fraction(157, 50), PI_HI)]
NAMES = ("muF_main", "nuD_main", "nuF_main", "MD_mirror",
         "MF_mirror", "MD2r_mirror", "MDFr_mirror")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, expected_lo: Fraction, expected_hi: Fraction) -> dict:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 CENTERED T-BOX PROBE TRANSCRIPT"
    config = next(line for line in lines if line.startswith("CONFIG ")).split()
    assert config[1:4] == ["delta", "1/25:81/2000", "t"]
    tlo, thi = (Fraction(x) for x in config[4].split(":"))
    assert (tlo, thi) == (expected_lo, expected_hi)
    assert "seed_grid 12" in lines[next(i for i, x in enumerate(lines)
                                         if x.startswith("CONFIG "))]
    assert "max_cells 2304" in lines[next(i for i, x in enumerate(lines)
                                           if x.startswith("CONFIG "))]
    assert lines[-2] == "K4 CENTERED T-BOX PROBE PASS"
    assert "SCOPE candidate t-box only; no K4/S1'''/S2'''/G6 promotion" in lines[-1]
    cells = [json.loads(line[5:]) for line in lines if line.startswith("CELL ")]
    assert len(cells) == 2304
    fractions = json.loads(next(line.split(" ", 1)[1]
                                for line in lines if line.startswith("FRACTIONS ")))
    for name in NAMES:
        assert arb(fractions[name]).upper() < 1, (path.name, name, fractions[name])
    for line in lines:
        if line.startswith("DEPENDENCY "):
            _, rel, digest = line.split()
            assert sha256(ROOT / rel) == digest, (path.name, rel)
    return fractions


def main() -> int:
    cursor = Fraction(3)
    worst = (arb(0), None, None)
    for unit, lo, hi in UNITS:
        assert lo == cursor, (unit, lo, cursor)
        production = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723.txt"
        replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_rerun.txt"
        assert production.exists() and replay.exists(), unit
        assert production.read_bytes() == replay.read_bytes(), unit
        fractions = check(production, lo, hi)
        value = arb(fractions["nuD_main"])
        if worst[1] is None or value > worst[0]:
            worst = (value, unit, "nuD_main")
        cursor = hi
    assert cursor == PI_HI
    print("K4 CENTRED T-BOX CANDIDATE UNION AUDIT PASS")
    print("units", len(UNITS), "cells", len(UNITS) * 2304,
          "domain", "3", str(PI_HI))
    print("worst", worst[2], worst[1], worst[0])
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
