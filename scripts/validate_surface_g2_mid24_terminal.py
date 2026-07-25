"""Validator for one terminal order-24 direct-sign unit."""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path, lo: Fraction, hi: Fraction) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW MID TERMINAL ORDER24"
    assert "SCOPE terminal direct-sign mid24 gap; no H_tail promotion" in lines
    beta = next(line.split() for line in lines if line.startswith("beta_domain "))
    assert (Fraction(beta[1]), Fraction(beta[2])) == (lo, hi)
    t_domain = next(line.split() for line in lines if line.startswith("t_domain "))
    cursor = Fraction(t_domain[1])
    count = 0
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index, left, right = head.split()
        left, right = Fraction(left), Fraction(right)
        assert int(index) == count and left == cursor and right > left
        assert arb(upper_text) < 0
        cursor, count = right, count + 1
    assert count and cursor == Fraction(t_domain[2])
    for line in lines:
        if line.startswith("dependency "):
            fields = line.split()
            assert sha(ROOT / fields[1]) == fields[3]
    return count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    ctx.prec = 200
    production, replay = ROOT / args.production, ROOT / args.replay
    assert production.read_bytes() == replay.read_bytes()
    rows = validate(production, Fraction(args.lo), Fraction(args.hi))
    print("MID24 TERMINAL VALIDATION PASS", args.lo, args.hi,
          "rows", rows, "sha256", sha(production))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
