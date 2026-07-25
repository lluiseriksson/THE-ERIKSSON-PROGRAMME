"""Validate one order-22 mid-cover production/replay pair.

This validator is intentionally provenance-strict and non-promoting.  It
checks the exact beta/t domains, current dependency hashes, row adjacency,
strict Arb signs, and byte equality of the stored replay pair.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path, lo: Fraction, hi: Fraction) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR"
    config = next(line for line in lines if line.startswith("config "))
    assert all(token in config for token in (
        "CWIN 3/2", "beta_order 22", "t_order 25",
        "min_dt 1/100000", "prec 180",
    ))
    beta = next(line for line in lines if line.startswith("beta_domain ")).split()
    assert (Fraction(beta[1]), Fraction(beta[2])) == (lo, hi)
    t_domain = next(line for line in lines if line.startswith("t_domain ")).split()
    cursor = Fraction(t_domain[1])
    rows = []
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index, left, right = head.split()
        left, right = Fraction(left), Fraction(right)
        upper = arb(upper_text)
        assert int(index) == len(rows)
        assert left == cursor and right > left and upper < 0
        rows.append((left, right))
        cursor = right
    assert cursor == Fraction(t_domain[2])
    count = int(next(line.split()[1] for line in lines if line.startswith("t_rows ")))
    assert count == len(rows)
    assert "SCALED BULK SIGN ROW PASS" in lines
    assert "SCOPE quarantined order22 repair; no G2/G6 promotion" in lines
    dependencies = {
        line.split()[1]: line.split()[3]
        for line in lines if line.startswith("dependency ")
    }
    for relative, recorded in dependencies.items():
        assert sha256(ROOT / relative) == recorded
    return count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    production = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}_rerun.txt"
    assert production.read_bytes() == replay.read_bytes()
    rows = validate(production, lo, hi)
    print("ORDER22 UNIT VALIDATION PASS", args.unit, "t_rows", rows,
          "sha256", sha256(production))
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
