"""Validate one generic mid-order CWIN=3/2 production/replay pair."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]


def parse(path: Path, lo: Fraction, hi: Fraction) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID GENERIC"
    beta = next(x for x in lines if x.startswith("beta_domain ")).split()
    assert (Fraction(beta[1]), Fraction(beta[2])) == (lo, hi)
    config = next(x for x in lines if x.startswith("config "))
    assert "CWIN 3/2" in config and "beta_order 24" in config and "t_order 25" in config
    domain = next(x for x in lines if x.startswith("t_domain ")).split()
    cursor = Fraction(domain[1]); count = 0
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper = line.split(" upper ", 1)
        _, index, left, right = head.split()
        left, right = Fraction(left), Fraction(right)
        assert int(index) == count and left == cursor and right > left and arb(upper) < 0
        cursor = right; count += 1
    assert cursor == Fraction(domain[2])
    assert int(next(x.split()[1] for x in lines if x.startswith("t_rows "))) == count
    assert "SCALED BULK SIGN ROW PASS" in lines
    return count


if __name__ == "__main__":
    p = argparse.ArgumentParser(); p.add_argument("--unit", required=True); p.add_argument("--lo", required=True); p.add_argument("--hi", required=True); a = p.parse_args()
    lo, hi = Fraction(a.lo), Fraction(a.hi)
    prod = ROOT / "scripts" / f"surface_scaled_bulk_{a.unit}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{a.unit}_rerun.txt"
    assert prod.read_bytes() == replay.read_bytes()
    count = parse(prod, lo, hi)
    print("GENERIC MID VALIDATION PASS", a.unit, "t_rows", count, "sha256", hashlib.sha256(prod.read_bytes()).hexdigest())
